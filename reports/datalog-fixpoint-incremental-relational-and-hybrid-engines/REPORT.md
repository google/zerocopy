# Datalog, Fixpoint, Incremental Relational, and Hybrid Engines

## Summary

Modern deductive, relational, and equality-saturation engines extend classical positive Datalog along four coupled axes: (1) **specialized compiled semi-naive evaluation** over optimal indexes (`Soufflé`), (2) **algebraic domain generalization** from Boolean sets to join-semilattices and equivalence-class functional dependencies (`Flix`, `Ascent`, `egglog`), (3) **worst-case optimal and unified join execution** eliminating quadratic intermediate blowup on cyclic queries (`Generic Join`, `Leapfrog Triejoin`, `Free Join`), and (4) **streaming incremental view maintenance (IVM)** supporting arbitrary insertions, deletions, and nested recursion via signed multiplicities (`Differential Dataflow`, `DBSP`/`Feldera`).

Core invariants and failure boundaries established from primary literature, pinned upstream implementations, and standalone execution probes:

- **Stratification gates unique least fixpoints.** Pure positive Datalog is monotone over the finite Herbrand powerset lattice and converges to a unique Knaster–Tarski least fixpoint via semi-naive $\Delta$-differentiation. Unstratified negation or aggregation inside a strongly connected component (SCC) destroys monotonicity: odd negative cycles (`p :- not p`) oscillate under $T_P$ with **zero** stable models; even negative cycles (`a :- not b; b :- not a`) yield **multiple** incomparable stable models; 3-valued Well-Founded Semantics restores polynomial uniqueness at the cost of `UNKNOWN` truth values. `Soufflé`, `Flix`, and `Ascent` reject unstratifiable SCCs statically.
- **Lattice Datalog relies on unchecked user laws and finite height.** Generalizing relations to maps $K \to L$ over a join-semilattice $(L, \sqsubseteq, \sqcup, \bot)$ preserves semi-naive soundness **only** if $\sqcup$, $\sqsubseteq$, and transfer functions satisfy semilattice laws, monotonicity, and the Ascending Chain Condition (ACC) or explicit widening ($\nabla$). Neither `Flix` (whose standard library ships an infinite-height `JoinLattice[BigInt]`) nor `Ascent` (`BoundedLattice` up to `u64`/`i64`) statically checks algebraic laws or finite height.
- **Binary hash joins blow up quadratically on cyclic queries; WCOJ and Free Join eliminate it.** On a skewed triangle query $R(x,y)\wedge S(y,z)\wedge T(z,x)$ with $N=2m+1$ tuples per relation and $3m+1=\Theta(N)$ outputs, **all three** binary join orders materialize $\ge m^2=\Theta(N^2)$ intermediate tuples (measured doubling exponent `1.98`), while `Generic Join` and `Free Join` materialize `0` intermediates (`1,539` vs. `132,610` probes at $m=256$, exponent `1.00`) and match the tight AGM bound $N^{3/2}$ on dense cliques. `Free Join`'s `COLT` lazy tries avoid eager sub-trie construction (`2/200` inner tries built at `1%` selectivity). Crucially, `egglog` v3 pairs hypertree decomposition with `Free Join` but documents that its `PureSize`/`MinCover` cover heuristics are not strictly worst-case optimal unless scanning the smallest side.
- **`egglog` unifies Datalog and equality saturation via functional dependencies plus `MergeFn`.** Storing e-nodes as rows with `MergeFn::UnionId` collapses congruence closure into relational rebuilding, while `Primitive`/`Function`/`Old`/`New`/`Const` support lattice analyses. Termination is undecidable in general, DAG extraction is NP-hard, and `MonoidCost` laws are unchecked by Rust's type system.
- **DBSP $\mathbb{Z}$-sets lift relational and recursive queries to exact streaming IVM, with a locality-dependent cost boundary.** Over the free abelian group $\mathbb{Z}[A]$, integration $\mathcal{I}$ and differentiation $\mathcal{D}$ are inverses and $Q^\Delta = \mathcal{D}\circ Q\circ \mathcal{I}$ automatically incrementalizes joins, `distinct`, and 2D-nested recursion (core algebra mechanized in **Lean 3.51.1**, not Lean 4). Localized sparse graph updates cut join work by `16.3x` (`116` vs. `1,890` ops) under exact equivalence across insertions, duplicate weights, diamonds, and cycle breaks; however, catastrophic deletions collapsing a small dense cycle can exceed scratch recomputation (`135` vs. `11` ops).
- **The host–relational FFI boundary is a soundness and marshaling fault line.** Impure or non-monotone host callbacks destroy semi-naive confluence (probe: batched `5` vs. incremental-join `10`). Cross-runtime fact copying (`Soufflé` C++ `SymbolTable`/`Relation`, `Flix` JVM boxing) incurs an $O(N)$ marshaling tax absent in macro-embedded `Ascent` or discrete-clock incremental `Feldera` batches.

## Applicability

This report covers the formal semantics, join/fixpoint compilation algorithms, algebraic IVM laws, and host–engine FFI contracts across sixteen primary subjects (eight paper/implementation pairs plus one Lean 3 formalization):

- **Compiled Stratified Datalog:** Jordan, Scholz & Subotić (CAV 2016) and `souffle-lang/souffle@2adf8c07210fe54f235e6e2d343c49b9d131463d`. The pinned tree extends CAV 2016 with Dilworth/Hopcroft–Karp minimum index selection, concurrent `BTree`/`Brie`/`EqRel` structures, subsumption, and stateful C++ functors.
- **First-Class Lattice Datalog:** Madsen, Yee & Lhoták (PLDI 2016) and `flix/flix@4022083acf86ab8b92308f2fb47ae615d5088de0`, reflecting evolved row-polymorphic constraint types, compiler-side Ullman stratification, and the self-hosted `Fixpoint3` B+-tree RAM interpreter.
- **Rust-Embedded Lattice Datalog:** Sahebolamri, Gilray & Micinski (CC 2022) and `s-arash/ascent@e52c84b4419c56976413de1cbf15d56c8c136a5c` (v0.8.1), covering macro-generated `Delta`/`Total`/`New` semi-naive loops, `ascent_base` lattices, and `byods` custom relations.
- **WCOJ & Unified Joins:** Ngo, Porat, Ré & Rudra (JACM 2018), Wang, Willsey & Suciu (SIGMOD 2023), and `SIGMOD23p561/free-join@c020bbc7964ba17594299a1910ad6b65eebdf0e0`.
- **Datalog + Equality Saturation:** Zhang et al. (PLDI 2023) and `egraphs-good/egglog@d89bc58adc9b9a87a8f571c5b9ad75d686d226e6` (v3.0.0), which replaces the PLDI 2023 prototype backend with modular `core-relations` (`Free Join` + hypertree decomposition), `egglog-bridge`, and term-encoded proof rulesets (`src/proofs/`).
- **Streaming Incremental Recursion:** McSherry, Murray, Isaacs & Isard (CIDR 2013) with `TimelyDataflow/differential-dataflow@e7c24703f4b1935cd6c99779ed0c140b0fea8ac6` (v0.26.0); and Budiu, Chajed, McSherry, Ryzhyk & Tannen (PVLDB 2023) with both `feldera/feldera@5a14ac52ae141ed188ddd8861eeaed5d1f4714a3` (`crates/dbsp/`) and `tchajed/database-stream-processing-theory@fb6ff4416108710448ccd87473c5513c1a1179ea` (Lean 3.51.1).

### Adjacent Corpus Packages & Scope Separation

This package focuses on general PL semantics, relational algorithms, IVM algebra, and FFI invariants without duplicating adjacent Rust-toolchain surveys:
- See `anneal-databases-networking-cloud-builds-and-tensor-survey` for SQL equivalence verifiers (`Cosette`, `SPES`, `WeTune`), Feldera SQL-to-circuit compiler embeddings, and demand-driven build engines (`Salsa`, `Adapton`, `Buck2 DICE`).
- See `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting` for Cranelift acyclic e-graphs (`aegraphs`), `egg` POPL 2021 congruence proof compression (`FMCAD 2022`), and Lean 4 equality-saturation tactics (`lean-egg`).

All execution receipts in `## Findings` come from `support/verify_wcoj_dbsp_and_lattices.py` run on Python 3 (stdlib only, Linux x86_64, `2026-11-19`); they establish exact algebraic identities, counterexamples, and asymptotic scaling exponents rather than native C++/Rust wall-clock throughput.

## Findings

### 1. Least-Fixpoint Semantics, Semi-Naive Differentiation, and Specialized Index Compilation

Basis: normative (Jordan, Scholz & Subotić CAV 2016; Subotić et al. PVLDB 2018; Jordan et al. PPoPP/PMAM 2019) + source (`souffle-lang/souffle@2adf8c07`, `s-arash/ascent@e52c84b4`) + derived.

#### Knaster–Tarski Least Fixpoint and Semi-Naive $\Delta$-Differentiation

A pure positive Datalog program $P$ over extensional database (EDB) $E$ induces an immediate-consequence operator $T_P : \mathcal{P}(\mathcal{H}_P) \to \mathcal{P}(\mathcal{H}_P)$ on the finite Herbrand base $\mathcal{H}_P$ (pure Datalog has no uninterpreted function symbols, bounding active domain size). Positive conjunction makes $T_P$ monotone and $\omega$-continuous on the finite complete lattice $(\mathcal{P}(\mathcal{H}_P), \subseteq)$, guaranteeing a unique Knaster–Tarski least fixpoint reached in finitely many Kleene iterations:

$$I_0 = E, \qquad I_{k+1} = I_k \cup T_P(I_k), \qquad \mathrm{lfp}(T_P) = \bigcup_{k=0}^{h} I_k.$$

**Semi-naive evaluation** avoids rediscovering earlier derivations by maintaining three logical tables per recursive relation $R$ within each SCC: cumulative `total` ($R$), previous-step frontier `delta` ($\Delta R$), and next-step scratch `new` ($R_{\text{new}}$). A clause with $m$ recursive body atoms expands into $m$ differentiated clauses, each binding one atom to $\Delta R_j$ (and preceding recursive atoms to $R_i \setminus \Delta R_i$ to avoid intra-step duplicates):

$$\Delta R_{\text{head}}^{(k+1)} = \left(\bigcup_{j=1}^{m} R_1^{(k)} \bowtie \dots \bowtie \Delta R_j^{(k)} \bowtie \dots \bowtie R_m^{(k)}\right) \setminus R_{\text{head}}^{(k)}.$$

Both compiled C++ and Rust macro backends lower recursive SCCs directly to this three-version state machine:

- **`Soufflé` (`souffle-lang/souffle@2adf8c07:src/ast2ram/seminaive/UnitTranslator.cpp`, L169–553):** `UnitTranslator::generateStratum` walks the topological `TopologicallySortedSCCGraph`. `generateStratumPreamble` (L469–498) seeds `@delta` from the main relation; `generateStratumLoopBody` (L553+) populates `@new`; and `generateStratumTableUpdates` (L514–533) merges `@new` into main, runs `ram::Swap(deltaRelation, newRelation)`, and `ram::Clear(newRelation)` (filtering `@delta = @new \ @reject` for subsumptive clauses at L363–364).
- **`Ascent` (`s-arash/ascent@e52c84b4:ascent_macro/src/ascent_codegen.rs`, L449–475):** Lowers each `MirScc` into explicit `MirRelationVersion::{Delta, Total, New}` locals (`::std::mem::take(&mut _self.#total_field)` into `#delta_var_name`), shifting `Delta -> Total` and `New -> Delta` until all deltas are empty.

#### Optimal Minimum Index Selection and Specialized Concurrent Containers

`Soufflé` closes the performance gap with hand-written C++ static analyzers via two compiler-driven specializations:

1. **Dilworth/Hopcroft–Karp Minimum Index Cover (`src/ram/analysis/Index.cpp`, L130–378; Subotić et al. PVLDB 2018):** Every prefix-nested chain of search signatures $S_1 \subset S_2 \subset \dots \subset S_k$ on a relation can share a single lexicographically ordered B-tree index. Minimizing total index count reduces by Dilworth's theorem to minimum chain cover on the search-signature poset, solved in polynomial time by `MinIndexSelectionStrategy::solve` (L223–315) via Hopcroft–Karp bipartite matching (`MaxMatching::bfSearch`, `dfSearch`, `solve`, `getChainsFromMatching`).
2. **Specialized Concurrent Relation Implementations:**
   - `BTree.h` (L2038–2110): `btree_set` / `btree_multiset` with optimistic concurrent reads and thread-local `operation_hints` caching recent leaf positions across sequential loop probes.
   - `Brie.h` (L62–69, L322–332, L1620–1630): dense integer trie combining 64-way `SparseArray<T, BITS=6>` nodes with `SparseBitMap<BITS=4>` bitset leaves for compact, cache-local storage of dense binary/ternary relations.
   - `EqRel.h` (L26–55): backs `.decl R(x: number, y: number) eqrel` with a native concurrent union-find (`EquivalenceRelation<Tuple<RamDomain, 2>>`), avoiding quadratic materialization of equivalence classes.

### 2. Stratified Negation, Aggregation, and Non-Monotone Fixpoint Semantics

Basis: normative (Van Gelder, Ross & Schlipf JACM 1991; Gelfond & Lifschitz ICLP 1988) + source (`souffle-lang/souffle@2adf8c07`, `flix/flix@4022083a`, `s-arash/ascent@e52c84b4`) + execution (`support/verify_wcoj_dbsp_and_lattices.py` Part 3c).

#### Semantic Breakdown Under Cyclic Negation and Aggregation

Negation (`not q(x)`) and non-monotone aggregates (`count`, `sum`, `min`/`max` read inside recursion) are anti-monotone or non-monotone: inserting a fact into `q` can retract previously derived facts. Inside a dependency cycle, three distinct regimes emerge:

| Program Pattern | Negative Cycle? | Immediate Consequence $T_P$ | 2-Valued Stable Models (ASP) | 3-Valued Well-Founded Semantics (WFS) | Stratified Engines |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `reach(x,y) :- edge(x,y).` `unreach(x) :- node(x), not reach(0,x).` | No (only positive cycle in `reach`) | Monotone per stratum; unique fixpoint | Unique total model | Identical 2-valued model | **Accepted** |
| `p(x) :- dom(x), not p(x).` | Odd cycle (`p -neg-> p`) | Oscillates $\emptyset \leftrightarrow \{a\}$ | **0 models** (inconsistent) | Unique 3-valued: `p(a) = UNKNOWN` | **Rejected** |
| `a(x) :- dom(x), not b(x).` `b(x) :- dom(x), not a(x).` | Even cycle (`a -neg-> b -neg-> a`) | Oscillates $\emptyset \leftrightarrow \{a,b\}$ | **2 minimal models**: `{a}` and `{b}` | Unique 3-valued: `a = b = UNKNOWN` | **Rejected** |

**Well-Founded Semantics (WFS)** (Van Gelder, Ross & Schlipf JACM 1991) computes a unique 3-valued model in polynomial data complexity ($O(N^2)$ alternating-fixpoint steps) by iterating an under-approximation $U_k$ (definitely true) and over-approximation $O_k$ (possibly true), assigning `UNKNOWN` to $O_\infty \setminus U_\infty$. **Stable Model Semantics** (Gelfond & Lifschitz ICLP 1988) keeps 2-valued models via the Gelfond–Lifschitz reduct, making model existence **NP-complete** in data complexity ($\Sigma_2^P$-complete with disjunctive heads). **Stratified Datalog** preserves polynomial unique 2-valued semantics by forbidding any negative or aggregation edge inside an SCC, inducing strata $S_0 < S_1 < \dots < S_k$ evaluated bottom-up.

#### Compiler Stratification Implementations

- **`Soufflé` (`src/ast/transform/SemanticChecker.cpp`, L209–239):** Inspects every recursive SCC in `sccGraph` via `hasClauseWithNegatedRelation` and `hasClauseWithAggregatedRelation`, failing compilation with `"Unable to stratify relation(s) { ... }"` on cyclic negation or aggregation.
- **`Flix` (`main/src/ca/uwaterloo/flix/language/phase/Stratifier.scala`, L44–54, L544–555; `UllmansAlgorithm.scala`, L71–95):** Because Flix Datalog constraint sets are first-class row-polymorphic values (`#{ A(x), B(x) | r }`), `Stratifier.stratify` restricts the program's `LabelledPrecedenceGraph` to each constraint expression's predicate row type and runs `UllmansAlgorithm.stratify`. Any strong edge (negation or lattice `fix`) on a cycle pushes a predicate's stratum above `maxStratum = g.size`, raising `StratificationError`.
- **`Ascent` (`ascent_macro/src/ascent_mir.rs`, L232–296; `ascent/src/aggregators.rs`, L89–90):** Condenses the rule dependency graph via `petgraph::algo::condensation`. Because `!foo(x)` desugars directly to the built-in aggregator `ascent::aggregators::not` (`aggregators.rs`, L89–90), the single check at `ascent_mir.rs` L284–290 (`"use of aggregated relation `{}` cannot be stratified"`) uniformly enforces both stratified negation and stratified aggregation.

Probe verification (`verify_wcoj_dbsp_and_lattices.py` Part 3c) confirms Tarjan SCC rejection of odd cycles ($T_P$ oscillates `[False, True, False, True]`, `0` stable models) and even cycles (`2` stable models `[(False, True), (True, False)]`, WFS alternating fixpoint `O \ U = {'a', 'b'}`), while accepting stratified `reach`/`unreachable`.

### 3. Finite-Height Join-Semilattices, Unchecked Algebraic Laws, and Divergence Without Widening

Basis: normative (Madsen, Yee & Lhoták PLDI 2016; Sahebolamri, Gilray & Micinski CC 2022; Arntzenius & Krishnaswami ICFP 2016 / POPL 2020; Abo Khamis et al. PODS 2022) + source (`flix/flix@4022083a`, `s-arash/ascent@e52c84b4`) + execution (`support/verify_wcoj_dbsp_and_lattices.py` Parts 3a–3b).

#### Extending Datalog to Join-Semilattices and Required Soundness Laws

Lattice Datalog (`Flix` PLDI 2016; `Ascent` CC 2022) generalizes a relation from $K \to \{\bot, \top\}$ to a finite map $K \to L$ into a bounded join-semilattice $(L, \sqsubseteq, \sqcup, \bot)$. Deriving $(k; v')$ for a key holding $v$ updates $v_{\text{new}} = v \sqcup v'$ in place and inserts $(k; v_{\text{new}})$ into $\Delta R$ only when $v_{\text{new}} \neq v$. Semi-naive evaluation computes a unique, schedule-independent least fixpoint and terminates **if and only if** four obligations hold:

1. **Semilattice laws:** $\sqcup$ is associative, commutative, idempotent, and order-compatible ($a \sqsubseteq b \iff a \sqcup b = b$).
2. **Transfer-function monotonicity:** Every host function $f$ invoked on lattice values inside a recursive SCC satisfies $x \sqsubseteq x' \implies f(x) \sqsubseteq f(x')$.
3. **Stratified lattice fixation:** Non-monotone reads of converged lattice values must execute in a strictly higher stratum.
4. **Ascending Chain Condition (ACC) or Widening ($\nabla$):** Every strictly ascending chain $v_0 \sqsubset v_1 \sqsubset \dots$ is finite, or a Cousot–Cousot widening operator accelerates infinite chains to a post-fixpoint.

#### Unchecked Obligations and Engineering Hazards in `Flix` and `Ascent`

- **`Flix` (`flix/flix@4022083a`):** Traits `PartialOrder[a]` (`PartialOrder.flix`, L18–25), `LowerBound[a]` (`LowerBound.flix`, L16–21), and `JoinLattice[a]` (`JoinLattice.flix`, L17–23) carry **no compile-time law or height proofs**. In particular, `JoinLattice.flix` L41–43 defines an **infinite-height standard-library instance**:
  ```flix
  instance JoinLattice[BigInt] {
      pub def leastUpperBound(x: BigInt, y: BigInt): BigInt = Order.max(x, y)
  }
  ```
  Recursive lattice increments over `BigInt` diverge without manual widening. At runtime, `Fixpoint3/Interpreter.flix` (L29–90) stores tuples as `Vector[Int64]` keys mapped to boxed JVM lattice objects in `BPlusTree[Tuple, Boxed, r]`.
- **`Ascent` (`s-arash/ascent@e52c84b4`):** `ascent_base/src/lattice.rs` (L17–99) defines `Lattice` (`meet_mut`, `join_mut`) and `BoundedLattice` (`bottom`, `top`) with implementations up to `i64`/`u64` (height $2^{64}$, effectively non-terminating under unit increments; note upstream doc comments at L18 and L23 swap the words "join" and "meet", though `ord_lattice_impl!` at L48–70 implements `min`/`max` correctly). Additionally, `ascent_macro/src/ascent_hir.rs` L261 enforces an explicit restriction against combining Ascent's `byods` custom data structures (Sahebolamri et al. OOPSLA 2023, DOI `10.1145/3622840`) with lattices: ``"`lattice`s cannot have custom data structure providers"``.

#### Static Monotonicity Types (`Datafun`) and Pre-Semiring Convergence

- **`Datafun` (Arntzenius & Krishnaswami, ICFP 2016 / POPL 2020):** Employs a modal type system with discrete comonad $\Box$ and monotone function arrows $A \to B$ to **statically prove monotonicity** of user functions at compile time and derive generalized higher-order semi-naive $\Delta$-evaluation (still assuming finite-height semilattices for termination).
- **Pre-Semiring Datalog (Abo Khamis, Ngo, Pichler, Suciu & Wang, PODS 2022):** Characterizes convergence over arbitrary partially ordered pre-semirings $(S, \oplus, \otimes, 0, 1)$ via **$p$-stability** ($1 \oplus a \oplus \dots \oplus a^p = 1 \oplus a \oplus \dots \oplus a^{p+1}$): absorptive $0$-stable semirings (Boolean, tropical $(\mathbb{R}_{\ge 0}\cup\{\infty\}, \min, +)$) converge in bounded steps, whereas non-absorptive semirings (e.g., $\mathbb{N}$ bag counts on cyclic graphs) diverge.

#### Empirical Probe Receipts (`verify_wcoj_dbsp_and_lattices.py`, Parts 3a–3b)

- **Height-2 Constant Propagation ($\bot \sqsubset \text{Const}(c) \sqsubset \top$):** Naive and semi-naive solvers produce identical fixpoints (`z=('C', 5)`, `w=('TOP',)`, `u15=('TOP',)`, `c15=('C', 1)`), with semi-naive using **`50` vs. `627` rule evaluations (`12.5x` reduction)**.
- **Infinite-Height `BigInt` Divergence vs. Widening:** On `A(0; 0). A(0; v+1) :- A(0; v).`, un-widened iteration hits step cap `50` at `v=50` without stabilizing; threshold widening ($\nabla \to +\infty$ past `8`) converges to `inf` in `10` steps.

### 4. Worst-Case Optimal Joins, AGM Bounds, and Free Join Unification

Basis: normative (Atserias, Grohe & Marx SICOMP 2013; Veldhuizen ICDT 2014; Ngo, Porat, Ré & Rudra JACM 2018; Wang, Willsey & Suciu SIGMOD 2023) + source (`SIGMOD23p561/free-join@c020bbc7`, `egraphs-good/egglog@d89bc58a`) + execution (`support/verify_wcoj_dbsp_and_lattices.py` Part 1).

#### Cyclic Join Blowup and the AGM Bound

Binary join trees (used by default in `Soufflé`, `Flix`, and `Ascent`) are asymptotically suboptimal on cyclic queries. By the **Atserias–Grohe–Marx (AGM) bound** (SICOMP 2013, DOI `10.1137/110859440`), the maximum output cardinality of conjunctive query $Q = \bigwedge_{e \in E} R_e(\bar{x}_e)$ equals the minimum fractional edge cover ($\sum_{e \ni v} w_e \ge 1$ for all variables $v$):

$$|Q| \le \mathrm{AGM}(Q) = \min_{w \ge 0} \prod_{e \in E} |R_e|^{w_e}.$$

For the triangle query $Q_\triangle(x,y,z) = R(x,y)\wedge S(y,z)\wedge T(z,x)$ with $|R|=|S|=|T|=N$, $w_R=w_S=w_T=1/2$ gives $\mathrm{AGM}(Q_\triangle) = N^{3/2}$ (tight on directed cliques $K_v$ where $N=v^2$ and $|Q_\triangle|=v^3=N^{3/2}$). Yet on the symmetric hub-and-spoke skew graph $R=S=T=\{(0,0)\}\cup\{(0,i),(i,0)\mid 1\le i\le m\}$ ($N=2m+1$), there are only $3m+1=\Theta(N)$ output triangles, while **every** binary join order—$(R\bowtie S)\bowtie T$, $(S\bowtie T)\bowtie R$, and $(T\bowtie R)\bowtie S$—produces $\ge m^2 = \Theta(N^2)$ intermediate pairs across hub `0`.

#### Generic Join, Leapfrog Triejoin, and Free Join (`COLT`)

**Worst-Case Optimal Joins (WCOJ)**—`Generic Join` (Ngo, Porat, Ré & Rudra JACM 2018) and `Leapfrog Triejoin` (Veldhuizen ICDT 2014)—evaluate joins **one variable at a time** over trie-indexed relations, intersecting all relations containing variable $v_i$ simultaneously in time proportional to the **smallest** participating domain $O(\min_{e \ni v_i} |R_e[\text{prefix}].v_i|)$ (up to a $\log$ factor for sorted tries). This meets $\tilde{O}(\mathrm{AGM}(Q))$ with **zero** intermediate tuple materialization.

Pure WCOJ historically underperformed binary hash joins on acyclic queries because eager full-trie indexing hashes every column up front and single-variable loops prevent vectorized multi-column probing. **Free Join** (Wang, Willsey & Suciu SIGMOD 2023; `SIGMOD23p561/free-join@c020bbc7`) unifies both regimes:

1. **Generalized Hash Tries & Cover Plans (`gj/src/trie.rs`, `gj/src/join.rs`):** Each stage iterates a *covering sub-atom* (one or more columns) and probes peer tries via vectorized `TrieRef::get_many` (`trie.rs`, L397). Covering an entire build relation recovers binary hash join; single-column smallest-side covers recover `Generic Join`.
2. **COLT (Column-Oriented Lazy Trie) (`gj/src/trie.rs`, L15–70, L358–376):** Inner trie levels live inside an `UnsafeCell`-backed `OnceCell<T, Z>` holding unpartitioned row slices until actually probed (`get_or_init`, `force_one`), eliminating wasted hash-table construction on unmatched keys.

#### Production Adoption & Non-WCOJ Heuristic Caveat in `egglog` v3

`egraphs-good/egglog@d89bc58a:core-relations/src/free_join/plan.rs` (L1–46) executes rules in two stages: (1) **(hyper)tree decomposition** via min-fill variable elimination (`next_var_to_eliminate`), ear-merging, and Yannakakis bag materialization keyed on message variables; and (2) per-bag join compilation via either `PlanStrategy::Gj` (`JoinStage::Intersect`) or `PlanStrategy::PureSize` / `PlanStrategy::MinCover` (`JoinStage::FusedIntersect`, fused by `JoinStage::fuse`). Notably, `plan.rs` L41 explicitly documents that its `PureSize`/`MinCover` cover strategies are **not strictly worst-case optimal** (`"although this is not worst-case optimal because it does not necessarily picks the smallest side to scan"`).

#### Empirical Probe Receipts (`verify_wcoj_dbsp_and_lattices.py`, Part 1)

| Workload | Scale | $N$ | AGM Bound | $|Q_\triangle|$ | Binary Hash Join (All 3 Orders) Inter. Tuples | Binary Probes | Generic Join Probes | Free Join Probes | Doubling Exponent (Bin / GJ) |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| Skew Hub-Spoke | $m=32$ | 65 | 524.0 | 97 | 1,121 | 2,242 | 195 | 195 | — |
| Skew Hub-Spoke | $m=64$ | 129 | 1,465.2 | 193 | 4,289 | 8,578 | 387 | 387 | **1.94** / **0.99** |
| Skew Hub-Spoke | $m=128$ | 257 | 4,120.0 | 385 | 16,769 | 33,538 | 771 | 771 | **1.97** / **0.99** |
| Skew Hub-Spoke | $m=256$ | 513 | 11,619.2 | 769 | **66,305** | **132,610** | **1,539** | **1,539** | **1.98** / **1.00** |
| Dense Clique $K_v$ | $v=8$ | 64 | 512.0 | 512 | 512 | 1,024 | 584 | 584 | Tight AGM ($N^{3/2}$) |
| Dense Clique $K_v$ | $v=16$ | 256 | 4,096.0 | 4,096 | 4,096 | 8,192 | 4,368 | 4,368 | Tight AGM ($N^{3/2}$) |

In Part 1c (`200` keys $\times$ `10` rows/key, `1%` selectivity), `COLT` lazy tries materialized only **`2/200`** inner sub-tries (`2,020` vs. `4,000` hash inserts) with identical `200`-row output.

### 5. Unifying Datalog and Equality Saturation (`egglog`)

Basis: normative (Zhang et al. PLDI 2023) + source (`egraphs-good/egglog@d89bc58a`) + derived.

*(For classical `egg` POPL 2021 congruence proofs, FMCAD 2022 proof compression, and Cranelift `aegraphs`, see `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`.)*

`egglog` (Zhang, Wang, Flatt, Cao, Zucker, Rosenthal, Tatlock & Willsey, PLDI 2023) unifies Datalog and equality saturation via **tables with functional dependencies (key $\to$ output) and programmable merge functions**: term constructors `(Add a b) -> id` are functional tables returning e-class IDs, pure Datalog relations are `(x, y) -> ()` tables, and lattice analyses are `(e) -> LatticeVal` tables.

Direct inspection of `egraphs-good/egglog@d89bc58a:egglog-bridge/src/lib.rs` (L1224–1244) shows the exact `MergeFn` conflict-resolution algebra:

```rust
pub enum MergeFn {
    AssertEq,                                    // Panic on FD conflict
    UnionId,                                     // Congruence closure via uf_table union-find
    Primitive(ExternalFunctionId, Vec<MergeFn>), // Lattice/host merge (e.g. max, min, interval join)
    Function(FunctionId, Vec<MergeFn>),          // Recursive e-graph function lookup/merge
    Old,                                         // Retain prior value (order-dependent)
    New,                                         // Overwrite with new value (order-dependent)
    Const(Value),                                // Overwrite with constant (e.g. clamp base case)
}
```

Key operational semantics and theoretical limits verified in `egraphs-good/egglog@d89bc58a`:

1. **Semi-Naive Relational E-Matching & Rebuilding (`egglog-bridge/src/lib.rs`, L676–736):** `run_rules` executes queries incrementally over `core-relations` (`Free Join` + hypertree decomposition), applies rule actions, and invokes `rebuild_now()`. Rebuilding canonicalizes table rows through `uf_table`; whenever canonicalization causes two keys to collide, the table's `MergeFn` fires (`UnionId` propagating congruence closure, or `Primitive` propagating lattice joins) until fixpoint.
2. **Undecidable Termination:** Unlike pure Datalog, `egglog` rules allocate fresh e-class IDs (existential value creation); saturation termination is therefore undecidable in general and managed via bounded schedules (`(run N)`) and rule backoff (`src/scheduler.rs`).
3. **NP-Hard DAG Extraction & Unchecked Cost Laws (`src/extract.rs`, L21–75):** Optimal tree extraction is polynomial, but optimal DAG extraction (charging shared nodes once) is **NP-hard**. `MonoidCost` (`src/extract.rs`, L26–37) explicitly warns: `"Implementations must make identity a two-sided identity and combine associative, commutative, deterministic, non-panicking, and monotone with respect to Cost's ordering. Rust cannot enforce these laws."`
4. **Term-Encoded Proofs (`src/proofs/proof_encoding.md`, L40–75; `proof_checker.rs`):** `egglog` v3 encodes union-find and congruence steps into explicit egglog rulesets (`parent`, `single_parent`, `uf_function_index`, `rebuilding`, `rebuilding_cleanup`, `delete_subsume_ruleset`) over `UF_<Sort>` tables so equality proofs can be extracted and checked independently.

### 6. Incremental View Maintenance Over Streams: Differential Dataflow and DBSP

Basis: normative (Gupta, Mumick & Subrahmanian SIGMOD 1993; McSherry, Murray, Isaacs & Isard CIDR 2013; Budiu, Chajed, McSherry, Ryzhyk & Tannen PVLDB 2023) + source (`TimelyDataflow/differential-dataflow@e7c24703`, `feldera/feldera@5a14ac52`, `tchajed/database-stream-processing-theory@fb6ff441`) + execution (`support/verify_wcoj_dbsp_and_lattices.py` Part 2).

*(For Feldera's SQL-to-circuit frontend and comparisons with demand-driven build engines like `Salsa` and `Adapton`, see `anneal-databases-networking-cloud-builds-and-tensor-survey`.)*

#### Why DRed Struggles on Cyclic Deletions

Naive reference counting fails on recursive cycles because a cycle self-supports with multiplicity $\ge 1$ even after its external entry edge is deleted. Classical **DRed** (Gupta, Mumick & Subrahmanian SIGMOD 1993, DOI `10.1145/170035.170066`) handles deletions via over-deletion followed by rederivation and semi-naive re-propagation, which can repeatedly delete and rederive entire SCCs.

#### Differential Dataflow: 2D Partially Ordered Timestamps & Manual Consolidation

**Differential Dataflow** (McSherry et al. CIDR 2013; `TimelyDataflow/differential-dataflow@e7c24703`) tags every update with a join-semilattice timestamp (`lattice.rs`, L1–10) and a weight implementing `IsZero`, `Semigroup`, `Monoid`, and `Abelian` (`difference.rs`, L14–64). Inside `iterate` (`operators/iterate.rs`, L37–59), timestamps become pairs `Product<OuterTime, InnerIter>` ordered component-wise: $(t_1, i_1) \le (t_2, i_2) \iff t_1 \le t_2 \wedge i_1 \le i_2$. Because cyclic self-support occurs at strictly larger inner iteration $i + 1$, deleting an entry edge at outer time $t_2 > t_1$ automatically retracts the entire ungrounded cycle cleanly.

Two critical operational constraints appear directly in source:
- **Canceling-Difference Livelock (`operators/iterate.rs`, L12–16, L52–55):** `iterate` does **not** automatically insert `consolidate()`. Unless every feedback path passes through `consolidate()`, `distinct()`, or `reduce()`, logically zero pairs `(+1, -1)` can circulate indefinitely and prevent termination.
- **Arrangement Memory & Compaction Frontiers:** Shared indexed traces (`arrange`) retain historical `(key, val, time, diff)` versions until the host advances the compaction `Antichain` frontier.

#### DBSP: Algebraic $\mathbb{Z}$-Set Calculus & Lean 3.51.1 Mechanization

**DBSP** (Budiu, Chajed, McSherry, Ryzhyk & Tannen, PVLDB 2023) unifies non-recursive and recursive IVM over the free abelian group of **$\mathbb{Z}$-sets** (`Z[A]`: finitely supported maps $A \to \mathbb{Z}$, `tchajed/database-stream-processing-theory@fb6ff441:src/zset.lean` L17–45) using three stream primitives (`feldera/feldera@5a14ac52:crates/dbsp/src/operator/{integrate,differentiate,delta0}.rs`):
- Delay $z^{-1}(s)[0]=0, z^{-1}(s)[t]=s[t-1]$; integration $\mathcal{I}(s)[t] = \sum_{k=0}^t s[k]$; differentiation $\mathcal{D}(s) = s - z^{-1}(s)$, satisfying $\mathcal{I}\circ\mathcal{D} = \mathcal{D}\circ\mathcal{I} = \mathrm{id}$.
- **Universal Incrementalization (`src/incremental.lean`, L28–29):** $Q^\Delta \triangleq \mathcal{D} \circ Q \circ \mathcal{I}$, compiled bottom-up via mechanized algebraic laws:
  - **Chain Rule (`chain_incremental`, L118):** $(Q_1 \circ Q_2)^\Delta = Q_1^\Delta \circ Q_2^\Delta$.
  - **Linear Time-Invariant (`lti_incremental`, L320):** $Q^\Delta = Q$ for filters, projections, union, negation, $z^{-1}$, $\mathcal{I}$, $\mathcal{D}$.
  - **Bilinear Join (`bilinear_incremental`, L597):** $(a \bowtie b)^\Delta = (\Delta a \bowtie \Delta b) + (z^{-1}(\mathcal{I}(a)) \bowtie \Delta b) + (\Delta a \bowtie z^{-1}(\mathcal{I}(b)))$.
  - **Non-Linear `distinct` (`feldera/feldera@5a14ac52:crates/dbsp/src/operator/dynamic/distinct.rs`, L644–661, L842–851):** Touches **only** keys in $\Delta$, emitting $\mathbf{1}[I_{t-1}[k]+\Delta[k]>0] - \mathbf{1}[I_{t-1}[k]>0]$; across $n$ nested recursive scopes, Feldera maintains $2^n$ accumulators per key to evaluate all partially ordered timestamp corners in one cursor sweep.
  - **2D Nested Recursion (`src/recursive.lean`, L19–44; `operator/dynamic/recursive.rs`, L19–80; `delta0.rs`, L54–60):** Imports outer deltas at inner step `0` via `delta0`, feeds back via `DelayedFeedback` ($z^{-1}$), and applies outer $Q^\Delta$ (`cycle_incremental`, `lifting_cycle`, `cycle2_incremental` in `incremental.lean` L159–304) to incrementalize arbitrary recursive fixpoints under both insertions and deletions.

**Mechanized vs. Trusted Boundary:** Direct inspection of `tchajed/database-stream-processing-theory@fb6ff441:leanpkg.toml` confirms the formalization targets **Lean 3.51.1** (`mathlib` `44b58b42`), **not** Lean 4. It proves the abstract stream, $\mathbb{Z}$-set, bilinear, aggregation, and recursive-circuit laws; Feldera's Rust `dbsp` runtime (`Spine` LSM storage, `unsafe fn typed` erasure adapters in `crates/dbsp/src/operator/recursive.rs` L23–33, multi-worker scheduler, and SQL frontend) is **not** formally linked by refinement proof.

#### Empirical Probe Receipts (`verify_wcoj_dbsp_and_lattices.py`, Part 2)

Our standalone DBSP circuit verified $\mathcal{I}(\text{TC}^\Delta(\Delta E))_t = \text{TC}_{\text{scratch}}(\mathcal{I}(\Delta E)_t)$ and $\text{TC}^\Delta(\Delta E) = \mathcal{D}(\text{TC}_{\text{scratch}}(\mathcal{I}(\Delta E)))$ across `40` dense mutation ticks (10 adversarial + 30 random) plus a 12-component sparse benchmark:

| Scenario | Mutation | $|\text{TC}|$ | $\Delta\text{TC}$ (`+`/`-`) | DBSP Ops | Scratch Ops | Regime Behavior |
| :--- | :--- | :---: | :---: | :---: | :---: | :--- |
| Tick 1 (duplicate insert) | Insert `(0,3)` `+1` (weight `1->2`) | 20 | `+0 / -0` | **`0`** | `63` | `distinct^Δ` filters no-op multiplicity change |
| Tick 2 (diamond branch delete) | Delete `(0,5)` (`(0,4)` kept via `(0,3)`) | 17 | `+0 / -3` | **`24`** | `45` | Alternative path survives automatically |
| Tick 3 (duplicate decrement) | Decrement `(0,3)` `2->1` | 17 | `+0 / -0` | **`0`** | `45` | Positive weight preserved; zero recursive work |
| Tick 4 (final path delete) | Delete `(0,3)` `1->0` | 11 | `+0 / -6` | `30` | `18` | Exact retraction of `(0,4)` and dependents |
| Tick 8 (cycle + bridge cut) | Delete `(1,2)` collapsing 50% of tiny graph | 10 | `+0 / -10` | **`135`** | **`11`** | **Cost boundary:** 2D retraction sweeps prior slices |
| 40-tick aggregate | 10 adversarial + 30 random on 10-node graph | — | exact match | **`14,300`** | **`25,518`** | `1.78x` net reduction |
| Localized sparse (12 $\times$ 6 chains) | 4 single-edge edits in component 0 | — | exact match | **`116`** | **`1,890`** | **`16.3x` reduction** proportional to affected scope |

Thus DBSP speedup scales with update locality ($|\Delta\text{affected}| \ll |E|$); catastrophic deletions collapsing dense recursive cycles can transiently cost more than scratch recomputation of the shrunken graph.

### 7. The Host–Relational FFI Boundary: Impurity, Non-Monotonicity, Marshaling Tax, and Snapshot Consistency

Basis: source (`souffle-lang/souffle@2adf8c07`, `flix/flix@4022083a`, `s-arash/ascent@e52c84b4`, `egraphs-good/egglog@d89bc58a`, `feldera/feldera@5a14ac52`) + execution (`support/verify_wcoj_dbsp_and_lattices.py` Part 3d) + derived.

1. **Impure or Non-Monotone Host Callbacks Break Fixpoint Confluence:** None of the examined production engines verify monotonicity or purity across FFI boundaries. `Soufflé` (`SouffleFunctor.h`, `Functor.cpp` L36–42) exposes both naive C ABI functors and *stateful* C++ functors receiving raw `(SymbolTable*, RecordTable*)` pointers; `egglog` (`src/sort/mod.rs`) invokes arbitrary Rust `Primitive`s inside `MergeFn::Primitive`; `Flix` checks `Pure` effect annotations but not lattice monotonicity. In probe Part 3d, a deterministic but **non-monotone** host callback (`f(1)=10, f(2)=5`) over the integer `max` lattice causes batched evaluation (`Out = f(max(1,2)) = 5`) and semi-naive incremental evaluation (`Out = max(f(1), f(2)) = 10`) to **silently disagree**.
2. **$O(N)$ EDB/IDB Marshaling Tax vs. Zero-Copy Host Integration:**

| Engine | Host–Engine Data Boundary | EDB/IDB Crossing Cost | Primary Friction |
| :--- | :--- | :--- | :--- |
| **`Soufflé`** (`SouffleInterface.h` L47–56, L697–786) | Virtual `Relation::insert` + `SymbolTable` interning (or CSV/SQLite) | **$O(N)$ copy + hash-interning** | Marshaling host IR/AST structs to/from `RamDomain` integers |
| **`Flix` `Fixpoint3`** (`Interpreter.flix` L29–63) | JVM objects mapped via `Boxing[r]` into `Int64` B+-tree keys | **$O(N)$ boxing/unboxing** | Per-tuple heap allocation & dictionary lookups |
| **`Ascent`** (`ascent_codegen.rs`) | Proc-macro generates native Rust structs & loops inline | **Zero FFI copy** | Still hashes keys into generated indices unless `byods` used (disallowed on `lattice`s) |
| **`egglog` v3** (`core-relations`, `termdag.rs`) | Numeric `Value` IDs in columnar tables + `TermDag` extraction | **$O(N)$ AST load/extract** | Re-insertion tax across outer iterative compiler passes |
| **`Feldera DBSP`** (`circuit_builder.rs`) | Typed `InputHandle`/`OutputHandle` `ZSet` / Arrow batches | **$O(|\Delta|)$ incremental batches** | External connector serialization & arrangement memory retention |

3. **Consistent Snapshot Boundaries:** Differential Dataflow exposes transient partial-epoch states unless the host explicitly tracks Timely's sealed capability frontier. Feldera `DBSP` (`circuit_builder.rs`, L7603–7657) eliminates transient views at the host API via synchronous discrete-clock barriers `CircuitHandle::step()` and `CircuitHandle::transaction()`, draining inner recursion to full fixpoint before exposing $\Delta O_t$.
4. **Positive-vs.-Negative Certificate Asymmetry:** Positive derivations admit small, linearly checkable derivation DAGs or congruence proof chains (`egglog` `src/proofs/proof_checker.rs`, `Flix` `Fixpoint3/ProvenanceReconstruct.flix`). Certifying **absence** (`not p(x)`) or fixpoint **minimality** requires a closed post-fixpoint witness $M \supseteq E$ with $T_P(M) \subseteq M$ and $p(x) \notin M$, scaling with $O(|M|)$ rather than proof depth.

### 8. Cross-Engine Architecture & Trade-Off Matrix

Basis: source (all eight pinned repositories) + normative.

| Engine | Execution Model | Join Algorithm | Recursion & Negation | Lattices / E-Graphs | Incremental Deletions | Host FFI Model | Checked vs. Unchecked Invariants |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`Soufflé`** (`2adf8c07`) | AOT Datalog $\to$ RAM $\to$ parallel C++ | Binary nested loops + Dilworth-optimal `BTree`/`Brie`/`EqRel` | Stratified negation & agg (`SemanticChecker.cpp`); subsumption | Built-in `eqrel`; subsumption; no user lattices | Batch (separate incremental forks) | C++ `SouffleInterface` + naive/stateful `extern "C"` functors | Stratification/types checked; functor purity/determinism **unchecked** |
| **`Flix`** (`4022083a`) | First-class Datalog $\to$ `Fixpoint3` JVM B+-tree interpreter | Binary B+-tree index joins | Stratified negation/fix via `UllmansAlgorithm.scala` | First-class `JoinLattice` + `PartialOrder` + `LowerBound` | Batch solve; provenance reconstruction | Pure Flix fns + JVM `Boxing` | Stratification & effect purity checked; lattice laws, monotonicity & finite height (`BigInt`) **unchecked** |
| **`Ascent`** (`e52c84b4`, v0.8.1) | Rust proc-macro $\to$ native semi-naive loops | Binary hash joins + `byods` custom traits | Stratified agg & `!rel` (`aggregators::not`, `ascent_mir.rs`) | Native Rust `Lattice`; incompatible with `byods` (`ascent_hir.rs:261`) | Batch | Zero-FFI inline Rust expressions | Stratification/types checked; `Lattice` laws, monotonicity & height **unchecked** |
| **`Free Join`** (`c020bbc7`) | Vectorized Rust query engine | Unified Free Join + Generalized Hash Tries + `COLT` lazy tries | Non-recursive conjunctive queries | None | None (batch) | Standalone prototype | AGM worst-case optimality proven (SIGMOD 2023) |
| **`egglog`** (`d89bc58a`, v3.0.0) | Semi-naive relational e-graph (`core-relations` + `egglog-bridge`) | Hypertree decomp (Yannakakis) + `Gj` / `Free Join` (`plan.rs`) | Existential rules + bounded schedules; deferred delete/subsume | Functional tables + `MergeFn::{UnionId, Primitive, Function, Old, New, Const}` | Deferred delete/subsume (not full IVM) | Rust `Sort` & `Primitive` traits | Termination undecidable; `MonoidCost` & `MergeFn` laws **unchecked**; `PureSize`/`MinCover` not strictly WCOJ |
| **`Differential Dataflow`** (`e7c24703`, v0.26.0) | Multi-worker Timely Dataflow streaming | Binary incremental `join` over LSM `arrange` traces (`dogsdogsdogs` WCOJ opt-in) | Nested `iterate` over 2D `Product` timestamps; non-monotone `reduce` | `Semigroup`/`Abelian` diffs; `Lattice` timestamps | Full streaming inserts & retractions + frontier compaction | Rust API; explicit Timely frontier tracking | Manual `consolidate()` required in `iterate` loops to avoid canceling-diff livelock |
| **`Feldera DBSP`** (`5a14ac52` + Lean 3 `fb6ff441`) | Discrete-clock streaming circuits (`crates/dbsp`) | Incremental bilinear joins + `distinct` + 2D nested `recursive` | Stratified & non-monotone recursion via `delta0` & $2^n$-corner `distinct` | $\mathbb{Z}$-sets (`ZWeight`), `IndexedZSet`, `GroupValue` | Full streaming inserts, deletions & recursive retractions | Synchronous `CircuitHandle::{step,transaction}` + Arrow/SQL | Core stream/bilinear/recursive algebra **mechanized in Lean 3.51.1**; Rust engine **unverified** |

## Boundaries

- **not examined:**
  - Native C++/Rust/JVM wall-clock benchmarks across industrial workloads (Doop/OpenJDK points-to, JOB/TPC-H); all measurements come from the deterministic Python 3 algorithmic probe (`support/verify_wcoj_dbsp_and_lattices.py`), which verifies asymptotic exponents, exact algebraic equivalence, and counterexamples rather than constant-factor native throughput.
  - Multi-node distributed recovery, RocksDB/disk-spilled `Spine` storage performance in `Feldera`, and multi-host Timely Dataflow networking.
  - ASP CDNL solvers (`clingo`/`clasp`), tabled Prolog (`XSB`), and out-of-tree incremental `Soufflé` forks (`IncSoufflé`).
- **unknown:**
  - Memory/runtime scaling of `egglog` v3's term-encoded proof checker (`src/proofs/proof_checker.rs`) on multi-million-row compiler-IR saturation traces and its exact trust boundary for custom `MergeFn::Primitive` rules.
  - Decidability of general bag-semantics conjunctive-query containment (an open problem in database theory).
- **known not to apply:**
  - **Strict AGM optimality does not automatically hold for every Free Join cover heuristic:** `egraphs-good/egglog@d89bc58a:core-relations/src/free_join/plan.rs` (L41) confirms `PureSize`/`MinCover` do not always scan the smallest side and therefore are not strictly worst-case optimal unless `PlanStrategy::Gj` or smallest-side selection is enabled.
  - **DBSP is not unconditionally faster than from-scratch recomputation on every single mutation:** Probe Part 2b (Tick 8) demonstrates a dense cycle-collapse deletion costing `135` incremental ops vs. `11` scratch ops.
  - **The DBSP Lean mechanization is Lean 3.51.1, not Lean 4, and does not verify the Rust runtime:** `tchajed/database-stream-processing-theory@fb6ff441` proves abstract stream laws only; `feldera/feldera/crates/dbsp/` remains outside the mechanization boundary and contains `unsafe` dynamic type-erasure adapters.
- **unsupported:**
  - **`Ascent` `byods` + `lattice`:** Explicitly rejected at macro expansion (`ascent_macro/src/ascent_hir.rs`, L261).
  - **Unstratified negation or cyclic aggregation in `Soufflé`, `Flix`, and `Ascent`:** Rejected statically (`SemanticChecker.cpp` L209–239; `Stratifier.scala` / `UllmansAlgorithm.scala`; `ascent_mir.rs` L284–290).
  - **Automatic loop consolidation in Differential Dataflow `iterate`:** Explicitly unsupported by design (`operators/iterate.rs`, L12–16).

## Evidence

### Pinned Source Repositories (Observed `2026-11-19`)

| Repository & Immutable 40-Char SHA | Inspected Paths & Line Ranges | Verified Artifacts |
| :--- | :--- | :--- |
| `souffle-lang/souffle` `@ 2adf8c07210fe54f235e6e2d343c49b9d131463d` | `src/ast2ram/seminaive/UnitTranslator.cpp` L169–553; `src/ram/analysis/Index.cpp` L130–378; `src/ast/transform/SemanticChecker.cpp` L209–239; `src/ast/analysis/Functor.cpp` L28–42; `src/include/souffle/{SouffleFunctor.h,SouffleInterface.h}` L47–56, L697–793; `datastructure/{BTree.h,Brie.h,EqRel.h}` | Semi-naive `@delta`/`@new`/main RAM codegen; Dilworth/Hopcroft–Karp `MinIndexSelectionStrategy::solve`; stratification error diagnostics; stateful functor detection; `SouffleProgram`/`Relation` C++ FFI; `btree_set`, `Brie` (`SparseArray`/`SparseBitMap`), `t_eqrel`. |
| `flix/flix` `@ 4022083acf86ab8b92308f2fb47ae615d5088de0` | `main/src/ca/uwaterloo/flix/language/phase/{Stratifier.scala,UllmansAlgorithm.scala}` L44–54, L544–555, L71–95; `main/src/library/{JoinLattice,PartialOrder,LowerBound}.flix`; `Fixpoint3/{Solver,Interpreter}.flix` | Row-polymorphic Ullman stratification; unchecked `JoinLattice` including infinite-height `JoinLattice[BigInt]`; `Fixpoint3` B+-tree RAM solver (`runSolver`, `ProvenanceReconstruct`, JVM `Boxing`). |
| `s-arash/ascent` `@ e52c84b4419c56976413de1cbf15d56c8c136a5c` (v0.8.1) | `Cargo.toml`; `ascent_base/src/lattice.rs` L16–99; `ascent_macro/src/{ascent_mir,ascent_codegen,ascent_hir}.rs`; `ascent/src/aggregators.rs` L19–90 | `Lattice`/`BoundedLattice` (swapped doc comments L18/L23, `i64`/`u64` impls); Tarjan SCC stratification rejecting `MirBodyItem::Agg`; `!rel` via `aggregators::not`; `Delta`/`Total`/`New` macro loops; `byods`-on-`lattice` rejection (`ascent_hir.rs:261`). |
| `SIGMOD23p561/free-join` `@ c020bbc7964ba17594299a1910ad6b65eebdf0e0` | `gj/src/{trie.rs,join.rs}` (`trie.rs` L15–70, L99–105, L186–261, L358–468) | `OnceCell<T, Z>` lazy `COLT` tries (`get_or_init`, `force_one`), `TrieRoot`/`TrieRef`, vectorized `get_many`, Free Join loops. |
| `egraphs-good/egglog` `@ d89bc58adc9b9a87a8f571c5b9ad75d686d226e6` (v3.0.0) | `Cargo.toml`; `core-relations/src/free_join/plan.rs` L1–75; `egglog-bridge/src/lib.rs` L123, L585–736, L1224–1270; `src/extract.rs` L1–75; `src/sort/mod.rs` L48–70; `src/proofs/proof_encoding.md` L40–75 | Hypertree decomposition + `PlanStrategy::{Gj, PureSize, MinCover}` (non-WCOJ caveat L41); `MergeFn` enum & `rebuild_now`; unchecked `MonoidCost` laws; `Sort`/`Primitive` FFI; term-encoded proof rulesets. |
| `TimelyDataflow/differential-dataflow` `@ e7c24703f4b1935cd6c99779ed0c140b0fea8ac6` (v0.26.0) | `Cargo.toml`; `differential-dataflow/src/{difference.rs,lattice.rs,operators/iterate.rs}` L1–75 | `IsZero`/`Semigroup`/`Monoid`/`Abelian`; `Lattice` timestamps + `Antichain`; `Iterate` manual-`consolidate()` livelock warning. |
| `feldera/feldera` `@ 5a14ac52ae141ed188ddd8861eeaed5d1f4714a3` | `crates/dbsp/src/operator/{differentiate,integrate,distinct,delta0,recursive}.rs`; `operator/dynamic/{distinct,recursive}.rs`; `circuit/circuit_builder.rs` L7602–7658 | `differentiate`, `Delta0`, incremental `distinct` sign-crossing & $2^n$-corner nested accumulators, `ChildCircuit::recursive` (`DelayedFeedback`, `unsafe fn typed`), `CircuitHandle::{step,transaction}`. |
| `tchajed/database-stream-processing-theory` `@ fb6ff4416108710448ccd87473c5513c1a1179ea` | `leanpkg.toml`; `src/{zset,incremental,recursive}.lean` | Lean 3.51.1 (`mathlib` `44b58b42`) formalization of `Z[A]`, `incremental`, `chain_incremental`, `lti_incremental`, `bilinear_incremental`, `cycle_incremental`, `lifting_cycle`, `cycle2_incremental`, `recursive_fixpoint`. |

### Primary Academic Literature (Verified DOIs & Venues)

- Jordan, Scholz & Subotić (2016), *Soufflé: On Synthesis of Program Analyzers*, CAV 2016, LNCS 9780, pp. 422–430, DOI `10.1007/978-3-319-41540-6_23`.
- Subotić, Jordan, Chang, Fekete & Scholz (2018), *Automatic Index Selection for Large-Scale Datalog Computation*, PVLDB 12(2), DOI `10.14778/3282495.3282500`.
- Jordan, Subotić, Zhao & Scholz (2019), *A Specialized B-tree for Concurrent Datalog Evaluation*, PPoPP 2019, DOI `10.1145/3293883.3295719`; *Brie: A Specialized Trie for Concurrent Datalog*, PMAM @ PPoPP 2019, DOI `10.1145/3303084.3309490`.
- Madsen, Yee & Lhoták (2016), *From Datalog to FLIX: A Declarative Language for Fixed Points on Lattices*, PLDI 2016, DOI `10.1145/2908080.2908096`.
- Sahebolamri, Gilray & Micinski (2022), *Seamless Deductive Inference via Macros*, CC 2022, DOI `10.1145/3497776.3517779`.
- Sahebolamri, Barrett, Moore & Micinski (2023), *Bring Your Own Data Structures to Datalog*, OOPSLA 2023, DOI `10.1145/3622840`.
- Arntzenius & Krishnaswami (2016, 2020), *Datafun: A Functional Datalog*, ICFP 2016, DOI `10.1145/2951913.2951948`; *Seminaïve Evaluation for a Higher-Order Functional Language*, POPL 2020, DOI `10.1145/3371090`.
- Abo Khamis, Ngo, Pichler, Suciu & Wang (2022), *Convergence of Datalog over (Pre-) Semirings*, PODS 2022, DOI `10.1145/3517804.3524140`.
- Van Gelder, Ross & Schlipf (1991), *The Well-Founded Semantics for General Logic Programs*, JACM 38(3), pp. 619–649, DOI `10.1145/116825.116838`.
- Gelfond & Lifschitz (1988), *The Stable Model Semantics for Logic Programming*, ICLP/SLP 1988, MIT Press, pp. 1070–1080.
- Atserias, Grohe & Marx (2013), *Size Bounds and Query Plans for Relational Joins*, SIAM J. Comput. 42(4), pp. 1737–1767, DOI `10.1137/110859440`.
- Veldhuizen (2014), *Leapfrog Triejoin: A Simple, Worst-Case Optimal Join Algorithm*, ICDT 2014, pp. 96–106, DOI `10.5441/002/icdt.2014.13`.
- Ngo, Porat, Ré & Rudra (2018), *Worst-Case Optimal Join Algorithms*, JACM 65(3), Article 16, DOI `10.1145/3180143`.
- Wang, Willsey & Suciu (2023), *Free Join: Unifying Worst-Case Optimal and Traditional Joins*, Proc. ACM Manag. Data 1(2) (SIGMOD 2023), DOI `10.1145/3589295`.
- Zhang, Wang, Flatt, Cao, Zucker, Rosenthal, Tatlock & Willsey (2023), *Better Together: Unifying Datalog and Equality Saturation*, Proc. ACM Program. Lang. 7(PLDI), DOI `10.1145/3591239`.
- Gupta, Mumick & Subrahmanian (1993), *Maintaining Views Incrementally*, SIGMOD 1993, pp. 157–166, DOI `10.1145/170035.170066`.
- McSherry, Murray, Isaacs & Isard (2013), *Differential Dataflow*, CIDR 2013.
- Budiu, Chajed, McSherry, Ryzhyk & Tannen (2023), *DBSP: Automatic Incremental View Maintenance for Rich Query Languages*, PVLDB 16(7), pp. 1601–1614, DOI `10.14778/3587136.3587137`.

### Preserved Runnable Execution Probe (`2026-11-19`)

- **Command:** `python3 -B reports/datalog-fixpoint-incremental-relational-and-hybrid-engines/support/verify_wcoj_dbsp_and_lattices.py` (Python 3.10+ stdlib only, deterministic seed `20261119`).
- **Result:** Exit `0` in `~0.24s` (`ALL PROBE ASSERTIONS PASSED.`): verifies skew triangle scaling (`66,305` intermediate tuples / exponent `1.98` vs. `0` intermediates / `1.00`), dense $K_{16}$ AGM tightness (`4,096 = 256^{3/2}`), `COLT` lazy trie (`2/200` sub-tries, `2,020` vs. `4,000` inserts), exact 2D-nested DBSP recursive TC equivalence across `40` ticks (`14,300` vs. `25,518` ops) plus `16.3x` sparse localized speedup (`116` vs. `1,890`) and `135` vs. `11` dense cycle-cut overhead, constant-propagation lattice semi-naive `12.5x` speedup (`50` vs. `627`), infinite-height divergence vs. threshold widening (`10` steps), SCC stratification + WFS `UNKNOWN`, and non-monotone FFI divergence (`5` vs. `10`).

## Revalidation

1. **Rerun the deterministic probe:**
   ```console
   python3 -B reports/datalog-fixpoint-incremental-relational-and-hybrid-engines/support/verify_wcoj_dbsp_and_lattices.py
   ```
   A `0` exit code re-verifies all WCOJ/Free Join, DBSP $\mathbb{Z}$-set 2D recursive IVM, lattice/widening, stratification, and FFI counterexample invariants.
2. **Diff narrow upstream implementation regions against the pinned SHAs:**
   - `souffle-lang/souffle` vs. `2adf8c07`: inspect `src/ast/transform/SemanticChecker.cpp`, `src/ram/analysis/Index.cpp`, and `src/include/souffle/SouffleFunctor.h` for user lattices, WCOJ planning, or built-in incremental deletions.
   - `flix/flix` vs. `4022083a`: inspect `main/src/library/JoinLattice.flix` and `UllmansAlgorithm.scala` for static law proofs, widening primitives, or changes to `JoinLattice[BigInt]`.
   - `s-arash/ascent` vs. `e52c84b4`: inspect `ascent_macro/src/ascent_hir.rs` (L261) and `ascent_base/src/lattice.rs` for `byods` + `lattice` support or WCOJ join codegen.
   - `egraphs-good/egglog` vs. `d89bc58a`: inspect `core-relations/src/free_join/plan.rs` (L35–42), `egglog-bridge/src/lib.rs` (`MergeFn`), and `src/proofs/` for strict smallest-side WCOJ cover selection or stabilized external proof formats.
   - `feldera/feldera` vs. `5a14ac52` & `tchajed/database-stream-processing-theory` vs. `fb6ff441`: inspect `crates/dbsp/src/operator/dynamic/{distinct,recursive}.rs` and check for any Lean 4 port or Rust-to-Lean refinement proofs.
   - `TimelyDataflow/differential-dataflow` vs. `e7c24703`: inspect `differential-dataflow/src/operators/iterate.rs` for automated loop consolidation or default WCOJ integration.
