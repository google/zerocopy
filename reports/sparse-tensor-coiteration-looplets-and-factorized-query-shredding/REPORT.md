# Sparse Tensor Coiteration, Looplet Algebras, Factorized Free Joins, Provenance Semirings, and Archetypal ECS Borrow Disjointness

## Summary

Sparse tensor compilers (`Finch`/`TACO`), worst-case-optimal relational join engines (`Free Join`), nested-multiset query compilers (`T-LINQ`), provenance-annotated databases (`K`-semirings), and archetypal Entity-Component-System memory engines (`Bevy ECS`) converge on a single mathematical structure: **algebraic concordant coiteration over hierarchical fiber tries parameterized by commutative semirings and Boolean-filter disjointness**:

1. **Finch Looplets Generalize TACO Merge Lattices to Compositional Control Flow:** While `TACO` (`tensor-compiler/taco`, OOPSLA 2017/2018) compiles sparse tensor index expressions via explicit **merge lattices** (`src/lower/merge_lattice.cpp` combining `IntersectNode`, `UnionNode`, and `ComplementNode` over per-level format iterators), `Finch` (`finch-tensor/Finch.jl`, CGO 2023 `Looplets`, `arXiv:2404.16730`) decomposes iteration into a small, composable algebra of **Looplets** (`Stepper`, `Run`, `AcceptRun`, `Spike`, `Phase`, `Sequence`, `Switch`, `Lookup`, `Jumper`, `Thunk`) combined via an explicit style priority lattice (`combine_style` in `src/looplets/*.jl`) and normalized format traits (`DenseData`, `SparseData`, `RepeatData`, `HollowData`, `ExtrudeData` in `src/interface/traits.jl`). This supports run-length encoding, triangular/banded/masked structures, and arbitrary loop control flow (`if`/`break`) within one lowering pass.
2. **Free Join Unifies Worst-Case Optimal Joins (WCOJ) and Binary Hash Joins Over Lazy Columnar Tries (`COLT`):** Wang, Willsey, and Suciu (SIGMOD 2023, `SIGMOD23p561/free-join`) prove that left-deep binary hash joins (joining 2 relations on all shared attributes) and Generic Join WCOJ (joining all relations on 1 attribute at a time) are extreme corners of one plan space (`Instruction2::Intersect` + `Instruction2::Lookup` in `gj/src/join.rs`) operating over **Generalized Hash Tries (GHTs)**. Implementing GHTs lazily as **Column-Oriented Lazy Tries (`COLT`)** (`struct Trie { inner: cell::OnceCell<Box<TrieInner>, Thunk> }` in `gj/src/trie.rs`, deferring hash-index construction via `SmallVec<[u32; 4]>` row thunks until actually probed) achieves AGM worst-case optimality on cyclic queries (100.5× fewer operations on our $N=500$ triangle probe vs. binary join) while matching hash-join speed on acyclic queries.
3. **Provenance $K$-Semirings and IEEE-754 Annihilator Boundaries Unify Tensor Contractions and Relational Joins:** Modeling every relation $R \subseteq D_1 \times \dots \times D_m$ as a sparse indicator tensor $\mathbb{I}_R : D_1 \times \dots \times D_m \to K$ over a commutative semiring $(K, \oplus, \otimes, \mathbf{0}, \mathbf{1})$ (Green, Karvounarakis & Tannen, PODS 2007) turns join-and-project into tensor contraction (`∑_j R[i,j] ⊗ S[j,k]`), subsuming sets ($\mathbb{B}$), bags ($\mathbb{N}$), tropical shortest paths, and universal why-provenance polynomials ($\mathbb{N}[X]$). Crucially, however, **IEEE-754 floating-point violates the semiring annihilator axiom** ($0.0 \times \text{NaN} = \text{NaN} \neq 0.0$ and $0.0 \times \infty = \text{NaN} \neq 0.0$); verified sparse coiteration must statically require either `FiniteFloat` preconditions or an explicit `StructuralZero` algebraic contract, and must reject sparse skipping on secret-dependent sparsity patterns to avoid timing side channels.
4. **Higher-Order Query Shredding (`T-LINQ`) and Archetypal SoA ECS (`Bevy`) Close the Host-Memory Boundary:** Cheney, Lindley & Wadler (ICFP 2013, SIGMOD 2014) prove that higher-order nested comprehensions over flat/nested multisets normalize statically to **1 flat query** (flat results, eliminating N+1 ORM loops) or **$O(d)$ flat queries** (depth-$d$ nested results via query shredding). For in-memory relational populations, `Bevy ECS` (`bevyengine/bevy`, `crates/bevy_ecs/src/query/access.rs`) partitions entities into contiguous Structure-of-Arrays (SoA) archetype tables (`Table` vs. `SparseSet` in `storage/mod.rs`) and checks query borrow disjointness using Disjunctive Normal Form (`FilteredAccess::is_compatible`). Source inspection and micro-probe benchmarking expose two exact properties of Bevy's DNF checker: (a) deliberate incompleteness on self-contradictory conjunctions like `(With<A>, Without<A>)` (`access.rs:924-931`), and (b) exponential $2^k$ clause blowup in `FilteredAccess::extend` under $k$-deep nested `Or<...>` conjunctions (`65,536` clauses / `1,228.82 ms` at $k=16$ vs. `18` CNF clauses / `0.098 ms` in a DPLL SAT checker).

## Applicability

These findings apply to the design of sparse/structured tensor compilers, relational/Datalog query engines, verified loop/join synthesis frameworks, host-embedded query languages, and data-oriented Entity-Component-System (ECS) memory runtimes.

The subjects in `REPORT.json` relate across four unified computational layers:

- **`Finch` (`finch-tensor/Finch.jl` at `7aa1ca1609054b94f3a1b56bb2221ae872513a10`, CGO 2023 & `arXiv:2404.16730`) and `TACO` (`tensor-compiler/taco` at `0e79acb56cb5f3d1785179536256e206790b2a9e`, OOPSLA 2017/2018)** define fiber-tree storage abstractions, merge lattices, and composable Looplet coiteration lowering for sparse and structured tensors.
- **`Free Join` (`SIGMOD23p561/free-join` at `c020bbc7964ba17594299a1910ad6b65eebdf0e0`, SIGMOD 2023 & `arXiv:2301.10841`) and Green, Karvounarakis & Tannen (PODS 2007)** establish the relational join unification (binary hash joins + WCOJ Generic Join), lazy columnar tries (`COLT`), and commutative $K$-semiring provenance semantics that align relational queries identically with sparse tensor contractions.
- **Cheney, Lindley & Wadler (`T-LINQ`, ICFP 2013; `Query Shredding`, SIGMOD 2014)** establish the higher-order host-to-relational normalization and bounded-query shredding guarantees needed to embed relational queries safely inside a host language without N+1 cliffs.
- **`Bevy ECS` (`bevyengine/bevy` at `779770720e6ad916c1de38cf66a67d0e079ed1e3`)** provides a production Rust implementation of archetypal SoA relational memory tables, dense-vs-sparse storage policies (`Table` vs. `SparseSet`), and Boolean-filter query borrow disjointness (`FilteredAccess`).

All source observations reflect the exact repository commits inspected on `2026-11-19`. Derived cross-system syntheses—including the Finch-Looplet-to-Free-Join correspondence, the IEEE-754 annihilator refinement boundary, and the DNF-vs-CNF SAT borrow-checking comparison—are labeled `Basis: derived` and backed by the reproducible micro-probe in **Evidence**.

## Findings

### 1. Sparse Tensor Coiteration: From TACO Merge Lattices to Finch Looplets

**Basis:** normative specification (Kjolstad et al., OOPSLA 2017, `10.1145/3133901`; Chou et al., OOPSLA 2018, `10.1145/3276493`; Ahrens et al., CGO 2023, `10.1145/3579990.3580020`; Ahrens et al., `arXiv:2404.16730`) + source (`tensor-compiler/taco` at `0e79acb56cb5f3d1785179536256e206790b2a9e`; `finch-tensor/Finch.jl` at `7aa1ca1609054b94f3a1b56bb2221ae872513a10`).

#### 1.1 TACO Format Abstraction and Merge Lattices (`tensor-compiler/taco`)

TACO introduced two foundational abstractions for compiling arbitrary sparse tensor algebra expressions (e.g., `C(i,k) = A(i,j) * B(j,k)`) across combinations of dense, CSR, CSC, DCSR, CSF, and COO layouts:
1. **Per-Level Fiber-Tree Storage Formats (`include/taco/format.h`, OOPSLA 2018):** Every tensor dimension is modeled independently as a level format characterized by six orthogonal properties (`Full`, `Ordered`, `Unique`, `Branchless`, `Compact`, `Zeroless`) and a uniform level-iterator capability interface (coordinate iteration, position iteration, random-access locate, append/insert assembly).
2. **Merge Lattice Construction (`src/lower/merge_lattice.cpp:22-156`):** To coiterate over multiple sparse operands in a single fused loop without materializing intermediate tensors, `MergeLatticeBuilder` builds a finite bounded lattice of `MergePoint`s for each index variable `i`:
   - `IntersectNode` (`merge_lattice.cpp:130-140`) intersects operand lattices (`intersectLattices(a, b)`), corresponding to multiplicative annihilators (`A[i] * B[i]`: skip unless both iterators are non-zero).
   - `UnionNode` (`merge_lattice.cpp:142-155`) unions operand lattices (`unionLattices(a, b)`), corresponding to additive identities (`A[i] + B[i]`: emit subloops for every nonempty subset of active iterators until exhausted).
   - `ComplementNode` (`merge_lattice.cpp:102-128`) flips lattice points and injects the full dimension iterator `iterators.modeIterator(i)` to handle non-zero-preserving operations.

**Structural Limit of Static Merge Lattices:** Because a merge lattice enumerates subsets of active iterators for an *entire* index domain upfront, it struggles with **piecewise, structured, or value-dependent iteration** (such as run-length encoded intervals, banded/triangular matrices, masked early exits, or `if`/`break` control flow inside kernels) without exploding lattice point counts (`O(2^M)` for $M$-way unions).

#### 1.2 Finch Looplets and Style-Priority Coiteration (`finch-tensor/Finch.jl`)

Finch (`Looplets`, CGO 2023; `Finch`, `arXiv:2404.16730`) solves TACO's rigidity by separating **what each fiber exposes over a sub-interval `[start, stop]`** from **how loops lower**. Every tensor level (dense, `SparseList`, `SparseCOO`, `SparseBytemap`, `SparseHash`, `SparseBand`, `SparseInterval`, `SparseRLE`, `DenseRLE`, `SparseVBL`, `Pattern` in `src/tensors/levels/`) yields a nested expression tree of **Looplet combinators** (`src/looplets/`):

| Looplet Combinator | Source File (`Finch.jl`) | Semantic Meaning Over `[start, stop]` | Coiteration Lowering Action |
|---|---|---|---|
| **`Run(body)`** | `src/looplets/runs.jl:1-50` | Constant subfiber `body` across the entire interval `[start, stop]` | Substitutes `body` directly; if algebraic simplification reduces `0 * x → 0`, skips entire interval in **$O(1)$**! |
| **`AcceptRun(body)`** | `src/looplets/runs.jl:53-110` | Output target accepting a constant run over `[start, stop]` | If loop index vanishes from simplified body (`root.idx ∉ body`), emits the body **once** instead of looping (`runs.jl:90-96`) |
| **`Spike(body, tail)`** | `src/looplets/spikes.jl:1-93` | Constant `body` on `[start, stop - 1]`, distinct `tail` at single point `stop` | Splits loop into `[start, stop - 1]` (with `Run(body)`) followed by point `[stop, stop]` (`Run(tail)`); `truncate` dynamically selects `Run(body)` vs. `Spike` via `Switch` |
| **`Stepper(preamble, stop, chunk, next, body, seek)`** | `src/looplets/steppers.jl:5-160` | Sequential cursor yielding contiguous sub-intervals up to `stop(ctx, ext)` and advancing via `next` | Computes minimum phase boundary `ext_2 = mapreduce(stepper_range, virtual_intersect, ...)`, runs inner coiteration over `ext_2`, then emits `Switch` on `node.stop == getstop(ext_2)` to advance only exhausted steppers |
| **`Phase`** / **`Sequence`** | `src/looplets/phases.jl`, `sequences.jl` | Partition of `[start, stop]` into statically ordered contiguous sub-ranges (e.g., before/inside/after a band or triangle) | Emits sequential specialized loops per phase; zero per-iteration bounds checks inside each phase |
| **`Lookup`** / **`Jumper`** | `src/looplets/lookups.jl`, `jumpers.jl` | $O(1)$ random-access indexing (`Dense` / `Bytemap`) or galloping/binary-search jump (`seek`) | Provides direct coordinate probe when another operand drives iteration (`combine_style(LookupStyle, StepperStyle) = StepperStyle`) |
| **`Switch`** / **`Thunk`** | `src/looplets/switches.jl`, `thunks.jl` | Guarded conditional sub-looplet / deferred epilogue code (`Thunk(body, epilogue)`) | Hoists branches out of inner loops and schedules post-chunk pointer increments cleanly |

**Algebraic Style Composition (`combine_style`):** Instead of hard-coding $O(K^2)$ pairwise format kernels, `src/looplets/steppers.jl:21-33`, `runs.jl:16-21`, and `spikes.jl:17-24` define a commutative associative priority join (`combine_style`) across styles:

$$\text{SimplifyStyle} \succ \text{ThunkStyle} \succ \text{SwitchStyle} \succ \text{SequenceStyle} \succ \text{PhaseStyle} \succ \text{JumperStyle} \succ \text{SpikeStyle} \succ \text{RunStyle} \succ \text{StepperStyle} \succ \text{LookupStyle} \succ \text{DefaultStyle}$$

Lowering repeatedly picks the highest-priority style present in a loop body, applies its single rewrite rule (peeling a `Sequence`, splitting a `Spike`, stepping `Stepper`s to the minimum `stop`, substituting a `Run`), runs algebraic simplification (`0 * x → 0`, `x + 0 → x`), and recurses. In `src/interface/traits.jl:1-138`, Finch tracks symbolic format traits (`SparseData`, `RepeatData`, `DenseData`, `ExtrudeData`, `HollowData`, `ElementData`) normalized via `collapse_rep` (`DenseData(HollowData(L)) → SparseData(L)`) to infer sparsity and concordant traversal statically.

#### 1.3 Semiring Annihilator Soundness and the IEEE-754 `0.0 * NaN` Trap

**Basis:** derived + execution (`probe_coiter_freejoin_ecs.py` Part A).

Both TACO and Finch achieve asymptotic speedups by rewriting `0 ⊗ x → 0` across empty `Run(0)` intervals (`ZeroRun ⊗ Any → Skip`). Mathematically, this rewrite is valid **if and only if** the value algebra $(R, \oplus, \otimes, \mathbf{0}, \mathbf{1})$ satisfies the **annihilator axiom** $\forall x \in R.\; \mathbf{0} \otimes x = \mathbf{0}$ and **additive identity** $\forall x \in R.\; \mathbf{0} \oplus x = x$.

Standard **IEEE-754 floating-point arithmetic violates the annihilator axiom**:
$$0.0 \times \text{NaN} = \text{NaN} \neq 0.0, \qquad 0.0 \times (+\infty) = \text{NaN} \neq 0.0, \qquad (-0.0) + (+0.0) = +0.0$$

In micro-probe Part A (`A = [0.0, 0.0, 0.0, 2.0]` stored as `Run(0.0)` + `{3: 2.0}`, `B = [10.0, NaN, +inf, 5.0]`):
- Exact IEEE-754 dense dot product returns **`NaN`**;
- Naive zero-skipping Looplet returns **`10.0`** — a silent semantic divergence!

**Verified Refinement Contract:** A certified coiteration compiler must refuse silent zero-skipping over IEEE-754 floats unless the specification explicitly selects either:
1. **`FiniteFloat` Refined Precondition:** Static/runtime proof that $\forall j.\; \text{isFinite}(B[j])$ (discharging $0.0 \times x = \pm 0.0$, plus `-0.0` sign policy); or
2. **`StructuralZero` Algebraic Semantics:** Explicit semantic definition in the specification that structural zeros denote algebraic absence (`Option<f64>` / $K$-relation absence) rather than IEEE-754 `0.0`, recording the exact refinement boundary!

*(Security Collision — Constant-Time Non-Interference):* Sparse coiteration (`Stepper`, `Spike`, `Run(0)` skipping) leaks the exact positions of non-zeros through branch counts, execution time, and memory access addresses. Any type system enforcing constant-time secrecy (`Sec<T>`) must statically reject sparse compression over secret-dependent zero patterns (`SecretIndexError`).

---

### 2. Free Join, Worst-Case Optimal Joins, and Provenance $K$-Semirings

**Basis:** normative specification (Green, Karvounarakis & Tannen, PODS 2007, `10.1145/1265530.1265535`; Wang, Willsey & Suciu, SIGMOD 2023, `10.1145/3589295` / `arXiv:2301.10841`) + source (`SIGMOD23p561/free-join` at `c020bbc7964ba17594299a1910ad6b65eebdf0e0`: `gj/src/join.rs`, `gj/src/trie.rs`) + execution (micro-probe Part B).

#### 2.1 The Exact Mathematical Identity Between Sparse Tensors and $K$-Relations

Green, Karvounarakis, and Tannen (PODS 2007) defined **$K$-relations**: functions $R : \text{Tuple} \to K$ with finite support mapping tuples to annotations in a commutative semiring $(K, \oplus, \otimes, \mathbf{0}, \mathbf{1})$:

| Semiring $(K, \oplus, \otimes, \mathbf{0}, \mathbf{1})$ | Relational Interpretation | Tensor-Algebra Equivalent |
|---|---|---|
| **Boolean** $(\mathbb{B}, \lor, \land, \bot, \top)$ | Set semantics (Datalog / classical relational algebra) | Binary sparsity pattern contraction |
| **Counting / Bag** $(\mathbb{N}, +, \times, 0, 1)$ | SQL multiset (bag) multiplicity semantics | Integer sparse tensor contraction |
| **$\mathbb{Z}$-Sets** $(\mathbb{Z}, +, \times, 0, 1)$ | Incremental View Maintenance (DBSP / Differential Dataflow retractions) | Signed sparse delta tensor contraction |
| **Tropical** $(\mathbb{R}_{\ge 0} \cup \{\infty\}, \min, +, \infty, 0)$ | Shortest-path / Viterbi / Bellman-Ford optimization | Min-plus sparse matrix multiplication (`GraphBLAS`) |
| **Universal Provenance** $(\mathbb{N}[X], +, \times, 0, 1)$ | Why- and How-provenance polynomials over base tuple indeterminates $X$ | Polynomial-valued sparse tensor contraction |

Under this correspondence, a multi-way conjunctive query with projection (e.g., triangle counting $Q_\triangle() = \sum_{a,b,c} R(a,b) \otimes S(b,c) \otimes T(c,a)$) is **literally a sparse tensor contraction** over the $K$-semiring!

#### 2.2 Why Binary Joins Blow Up on Cyclic Queries and How Free Join Unifies Both Worlds

Traditional binary hash joins evaluate two relations at a time, joining on *all* shared attributes between them. On the cyclic triangle query $Q_\triangle(a,b,c) = R(a,b) \bowtie S(b,c) \bowtie T(c,a)$ where each relation has size $|R|=|S|=|T|=2N+1$ (a star of $N$ outgoing and $N$ incoming edges around vertex `0` plus `(0,0)`):
- Any binary join plan `(R ⋈ S) ⋈ T` materializes $\Theta(N^2)$ intermediate triples `(x, 0, z)` before filtering against `T(z, x)`.
- The **Atserias–Grohe–Marx (AGM) bound** proves the maximum possible triangle output is $O(N^{3/2})$; Worst-Case Optimal Join (WCOJ) algorithms such as Leapfrog Triejoin and Generic Join iterate **one variable at a time** (`a`, then `b`, then `c`), intersecting all relations containing the current variable via smallest-first trie probes, staying within $O(N^{3/2})$ (and $O(N)$ on the star instance).
- Conversely, pure Generic Join underperforms binary hash joins on *acyclic* queries because it builds full multi-level hash tries over every join attribute upfront and processes only one attribute per loop level.

**Free Join (Wang, Willsey & Suciu, SIGMOD 2023)** unifies binary join and Generic Join into a single plan representation and execution engine (`SIGMOD23p561/free-join`):
1. **Generalized Hash Trie (GHT, Definition 3.1 of `arXiv:2301.10841`):** A tree whose internal nodes are hash maps keyed by **tuples of one or more attributes** `[y₀, y₁, ..., y_ℓ]` and whose leaves are vectors of tuples. A binary hash table is a 2-level GHT; a Generic Join trie is an $m$-level 1-attribute-per-level GHT.
2. **Free Join Plans (`gj/src/join.rs:10-180`):** Plans consist of `Instruction2::Intersect(Vec<Intersection2>)` (multi-way intersection across relations sharing an attribute set) and `Instruction2::Lookup(Vec<Lookup2>)` (batched hash probes). `merge_occurrences` and `combine_lookups` optimize a traditional binary plan into a hybrid Free Join plan that shares probes across relations while preserving WCOJ bounds on cyclic subqueries.
3. **COLT — Column-Oriented Lazy Trie (`gj/src/trie.rs:19-160`):** Rather than eagerly hashing every trie level upfront (which wastes work on unprobed branches in acyclic queries), `struct Trie` wraps an `UnsafeCell`-based `OnceCell<Box<TrieInner>, Thunk>`:
   ```rust
   struct Trie {
       inner: cell::OnceCell<Box<TrieInner>, Thunk>,
   }
   struct Thunk(SmallVec<[u32; 4]>);
   enum TrieInner {
       Map(HashMap<Id, u32>, Vec<Trie>),
       Set(HashSet<Id>, Box<Trie>),
       DenseSet(DenseMap<()>, Box<Trie>),
       Data(Thunk),
   }
   ```
   Unprobed sub-tries remain compact `Thunk` vectors of row indices (`SmallVec<[u32; 4]>`); only when a probe actually lands on a sub-trie does `get_or_init` materialize its `Map` / `Set` / `DenseSet` level!

#### 2.3 Exact Correspondence: Finch Looplets $\equiv$ Free Join Coiteration

**Basis:** derived from `Finch.jl` (`src/looplets/steppers.jl`, `lookups.jl`) + `free-join` (`gj/src/trie.rs`, `gj/src/join.rs`) + execution (micro-probe Part B).

| Concept | Finch / Looplet Formulation | Free Join / WCOJ Formulation |
|---|---|---|
| **Storage Hierarchy** | Nested fiber levels (`SparseList` / `SparseHash` / `Dense` / `Element`) | Generalized Hash Trie / COLT (`Map` / `DenseSet` / `Set` / `Data(Thunk)`) |
| **Single-Variable Multi-Way Intersection** | Concordant `Stepper` + `Jumper` (`seek` to $\max(\text{pos}_i)$) + `Run(0)` annihilator skip | `Instruction2::Intersect` (iterate smallest sub-trie, probe peers via `Lookup` / `HashMap`) |
| **Multi-Attribute Batched Lookup** | Composite multi-key level / `Lookup` style over flat key tuple | `Instruction2::Lookup` on multi-attribute GHT key `y_k` |
| **Lazy Specialization / Control Flow** | `Thunk(body, epilogue)` + `Switch` + `Phase` | `OnceCell<TrieInner, Thunk>` lazy trie expansion + vectorized batching |
| **Payload Semantics** | Parameterized by semiring `(+, *, 0, 1)` (`fill_value`, annihilator/identity traits) | $K$-relation semiring annotation (`Bool`, `Bag`, `Tropical`, `N[X]`) |

In micro-probe Part B (`N=500`, $|R|=|S|=|T|=1,001$ edges), unified trie coiteration executes the cyclic triangle query across all four $K$-semirings simultaneously in **`2,502` steps (`5.54 ms`)** vs. **`251,501` intermediate tuples (`363.25 ms`)** for binary join—a **`100.5×` work reduction** and **`65.6×` wall-clock speedup**, returning exact agreeing outputs (`Bool=True`, `Bag=5,030`, `Tropical=1.5`, `Why-Prov=['r_0_1', 's_1_0', 't00']`).

---

### 3. Higher-Order Query Normalization and Bounded Query Shredding (`T-LINQ`)

**Basis:** normative specification (Cheney, Lindley & Wadler, ICFP 2013, `10.1145/2500365.2500586`; SIGMOD 2014, `10.1145/2588555.2612186`).

Embedding relational queries cleanly inside a general-purpose host language—without stringly-typed SQL, N+1 ORM lazy-loading cliffs, or SQL's 3-valued `NULL` anomalies—relies on two mechanized normalization theorems established by Cheney, Lindley, and Wadler:

1. **Guaranteed-Flat Normal Form (`T-LINQ`, ICFP 2013):** Using quotation stratification (`Q[τ]`) to separate host-language higher-order abstractions (lambdas, reusable predicates, nested comprehensions) from query-safe primitives, a **confluent, strongly normalizing rewrite system** reduces *every* well-typed flat-result query (output type `Bag<Record<BaseTypes>>`) to **exactly one flat relational algebra / SQL query**. Crucially:
   - Higher-order host helpers are completely eliminated at compile time (zero UDF optimization barrier when helpers are pure quoted terms);
   - Any effectful or un-normalizable host call fails **statically at compile time** rather than silently degrading into an $O(N)$ runtime N+1 query loop;
   - Missing values use algebraic `Option<T>` / tagged sums instead of SQL's non-compositional 3-valued `NULL` logic.
2. **Bounded Query Shredding (`SIGMOD 2014`):** Real application queries routinely return *nested* collections (e.g., `Bag<(DeptName, Bag<(EmpName, Bag<Skill>)>)>`), which flat SQL cannot represent directly and ORMs evaluate via $O(N)$ nested round-trips. Query Shredding proves that any nested multiset query of collection nesting depth $d$ compiles into **at most $O(d)$ flat relational queries** (one flat query per collection type node, linked by synthetic flat parent-index keys) whose results reassemble into the exact nested host data structure in a single linear pass—preserving multiset (`Bag` / $\mathbb{N}$-semiring) equivalence (`Shred(Q) ≅ Q`)!

**Host-Boundary Limitations:** Normalization and shredding require host UDFs invoked inside query predicates to be **pure and inspectable** (or algebraically typed as pure/monotone); opaque foreign FFI callbacks inside filter/join predicates break both flat normalization and pushdown optimization. When targeting external RDBMS engines (PostgreSQL, MySQL, Spanner) rather than an in-memory semiring/ECS engine, engine-specific quirks (collations, integer overflow, empty string vs. `NULL`) remain an explicit dialect-codec trust boundary.

---

### 4. Archetypal Relational-ECS Memory Algebra and Borrow-Disjointness Checking (`Bevy ECS`)

**Basis:** source (`bevyengine/bevy` at `779770720e6ad916c1de38cf66a67d0e079ed1e3`: `crates/bevy_ecs/src/archetype.rs`, `crates/bevy_ecs/src/storage/mod.rs`, `crates/bevy_ecs/src/query/access.rs`, `crates/bevy_ecs/src/query/filter.rs`) + execution (micro-probe Part C).

#### 4.1 Hybrid Dense-Archetype (`Table`) vs. `SparseSet` Storage Architecture

Archetypal Entity-Component-Systems organize dynamic entity populations relationally in memory without pointer-chasing object graphs or GC pauses:
- **Archetypes (`archetype.rs`):** Entities sharing the exact same set of component types $A \subseteq \Sigma$ belong to one `Archetype`.
- **Dual Storage Policies (`storage/mod.rs`):** To address the classic **$O(2^K)$ archetype fragmentation trade-off** when entities carry many transient/sparse tags, `bevy_ecs` separates components into two storage tiers:
  1. **`StorageType::Table` (Dense SoA):** Contiguous Structure-of-Arrays columns indexed densely by `TableRow` inside each archetype table—ideal for SIMD/GPU/cache-line streaming over stable component combinations.
  2. **`StorageType::SparseSet` (Sparse Indexed Columns):** Indirect sparse-to-dense index arrays allowing $O(1)$ component insertion/removal *without* moving all of an entity's dense columns across archetype tables—directly analogous to Finch's hybrid dense/sparse fiber storage!
- **Epoch-Staged Structural Transitions:** Adding/removing components or despawning entities relocates archetype rows and invalidates borrowed column slices; ECS schedulers defer structural mutations into command buffers flushed at explicit synchronization barriers between parallel execution phases.

#### 4.2 Query Borrow Disjointness: Bevy's DNF Checker vs. Complete Propositional SAT

To safely execute parallel systems (or multiple mutable queries within one system, e.g., `Query<&mut Pos, With<Player>>` alongside `Query<&mut Pos, Without<Player>>`) without aliasing UB, `bevy_ecs` models each query's access footprint as `FilteredAccess` (`crates/bevy_ecs/src/query/access.rs:586-935`):

```rust
pub struct FilteredAccess {
    pub(crate) access: Access,                 // reads & writes bitsets (InvertibleComponentIdSet)
    pub(crate) required: ComponentIdSet,       // components unconditionally present
    pub(crate) filter_sets: Vec<AccessFilters>,// DNF: OR of (with: BitSet, without: BitSet)
}
```

Two queries `Q₁` and `Q₂` are compatible (`FilteredAccess::is_compatible`, `access.rs:769-787`) iff either:
1. Their unfiltered component `Access`es do not conflict (`self.writes ∩ other.reads == ∅` and `other.writes ∩ self.reads == ∅`), **or**
2. Their archetype filters are provably disjoint: every DNF clause `f₁ ∈ Q₁.filter_sets` and `f₂ ∈ Q₂.filter_sets` satisfies `f₁.is_ruled_out_by(f₂)`, defined at `access.rs:924-931` as:
   ```rust
   !self.with.is_disjoint(&other.without) || !self.without.is_disjoint(&other.with)
   ```

Direct source audit and micro-probe Part C (`probe_coiter_freejoin_ecs.py`) establish **three exact properties** of Bevy's DNF algorithm vs. full Boolean SAT checking of $\text{UNSAT}\big(\Phi_1 \land \Phi_2 \land \bigvee_{c \in \text{Conflict}(Q_1, Q_2)} \text{With}(c)\big)$:

| Property | Bevy DNF (`bevy_ecs/src/query/access.rs`) | Complete Propositional SAT / CNF Checker |
|---|---|---|
| **Soundness** | **Sound** (never permits aliasing; false conflicts only) | **Sound and Complete** over Boolean filter algebra |
| **Self-Contradictory Single Clause** (e.g., `Query<&mut Pos, (With<A>, Without<A>)>` vs. `Query<&mut Pos>`) | **Deliberately incomplete** (`access.rs:924-928`: explicitly skips checking `self.with ∩ self.without != ∅` because a contradictory query is almost always a programmer bug) | Proves `UNSAT` (`disjoint = True`); must emit a separate dead-query lint if empty queries are undesired |
| **Filter Composition Complexity** (`AND` of $k$ binary `Or<(With<A_i>, Without<B_i>)>` clauses) | **Exponential $O(2^k)$** via Cartesian product in `FilteredAccess::extend` (`access.rs:818-827`) | **Linear $O(k)$** CNF representation; fast DPLL/unit propagation |
| **Measured Benchmark (`probe_coiter_freejoin_ecs.py`)** | `k=4`: 16 clauses (`0.16 ms`); `k=8`: 256 (`10.25 ms`); `k=12`: 4,096 (`409.15 ms`); **`k=16`: 65,536 clauses (`1,228.82 ms`)** | `k=4`: 6 CNF clauses (`0.109 ms`); `k=8`: 10 (`0.057 ms`); `k=12`: 14 (`0.087 ms`); **`k=16`: 18 CNF clauses (`0.098 ms`)** — **12,500× faster at $k=16$** |
| **Runtime vs. Compile-Time Checking** | Checked at **system initialization / schedule build time** (panics if incompatible queries appear in one system; dynamically registers `ComponentId`s) | Can run at **compile time** for statically known component sets, or as an $O(k)$ **load-time link gate** for dynamically loaded plugin components |

*Engineering nuance:* For typical game/simulation queries with $k \le 3$ `Or<...>` combinators, Bevy's bitset DNF check is extremely fast (`<0.2 ms`) and simple; the exponential blowup surfaces specifically under macro-generated, query-shredded, or programmatic filter composition where CNF/SAT checking eliminates catastrophic compile/startup latency.

## Boundaries

- **Known not to apply (Dense/SIMT Load Balancing Without Flattening):** Concordant sparse coiteration (`Finch` `Stepper`s, `TACO` merge lattices, `Free Join` tries) produces variable-length inner loops across outer fibers; mapping irregular sparse coiteration directly onto lockstep SIMT GPU warps or BSP accelerators causes severe warp divergence and stragglers unless composed with dynamic load-balancing schedules (e.g., merge-path partitioning or segmented prefix-scan flattening).
- **Known not to apply (Zero-Skipping on Strict IEEE-754 Floats Without Preconditions):** As verified in micro-probe Part A, `0.0 * NaN = NaN` and `0.0 * inf = NaN` invalidate sparse `Run(0)` skipping under strict IEEE-754 unless `FiniteFloat` preconditions or `StructuralZero` semantics are declared.
- **Known not to apply (Dynamic In-Place Mutation During Compressed Fiber Iteration):** Compressed sorted formats (`CSR`, `CSF`, `SparseList`, `COLT` hash tries) are structurally incompatible with simultaneous $O(1)$ random insertion during active `Stepper` borrows; mutation requires an explicit typestate phase transition (`Builder → Sort/Compress → FrozenFiber`) or command-buffer epoch barrier (as in `Bevy ECS`).
- **Unsupported (Compile-Time Closed-World ECS Disjointness Under Dynamic `dlopen` Plugins):** Static SAT disjointness checking requires knowing the filter formulas of all concurrently scheduled systems; dynamically loaded plugins introducing opaque component IDs require either capability-scoped sub-worlds or a load-time SAT verification gate prior to schedule activation.
- **Unknown (Optimal Variable Ordering / Trie Schema Selection Under Skewed Data):** Free Join guarantees AGM worst-case optimality for *any* valid plan structure, but selecting the lowest-cost variable ordering and attribute grouping for large multi-way schemas remains NP-hard and sensitive to runtime cardinality skew.
- **Not examined (Non-Monotone Recursive Queries, Stratified Negation, and DBSP Incremental Maintenance):** While $K$-semirings extend naturally to $\mathbb{Z}$-set deltas (DBSP), recursive fixpoints with stratified negation/aggregation and incremental view maintenance frontier protocols were not examined at source level in this report.
- **Not examined (Mechanized Lean/Coq Proof-Certificate Size for Arbitrary Multi-Way Looplets):** While every Looplet rewrite (`Run`, `Spike`, `Stepper`, `Phase`) has an algebraic interval denotation suitable for compositional proof checking, no end-to-end mechanized proof assistant implementation of Finch's full compiler pipeline was audited.

## Evidence

### Primary Specifications and Peer-Reviewed Papers

1. **Ahrens, Donenfeld, Kjolstad, and Amarasinghe (CGO 2023):** *Looplets: A Language for Structured Coiteration*, CGO 2023, DOI `10.1145/3579990.3580020`.
2. **Ahrens, Collin, Patel, Deeds, Hong, and Amarasinghe (`arXiv:2404.16730`, v2 Jan 2025):** *Finch: Sparse and Structured Tensor Programming with Control Flow*, `arXiv:2404.16730` (verified on `2026-11-19`: unified representation of control flow and structured tensors—sparsity, RLE, symmetry, triangles, padding, blocks).
3. **Kjolstad, Kamil, Chou, Lugato, and Amarasinghe (OOPSLA 2017) & Chou et al. (OOPSLA 2018):** *The Tensor Algebra Compiler*, OOPSLA 2017, DOI `10.1145/3133901`; *Format Abstraction for Sparse Tensor Algebra Compilers*, OOPSLA 2018, DOI `10.1145/3276493`.
4. **Wang, Willsey, and Suciu (SIGMOD 2023):** *Free Join: Unifying Worst-Case Optimal and Traditional Joins*, Proc. ACM Manag. Data (SIGMOD 2023), DOI `10.1145/3589295`, `arXiv:2301.10841` (full PDF verified on `2026-11-19`: Definition 3.1 Generalized Hash Trie, §2.3 Generic Join vs. left-deep linear binary plans, §4.2 COLT Column-Oriented Lazy Trie).
5. **Cheney, Lindley, and Wadler (ICFP 2013 & SIGMOD 2014):** *A Practical Theory of Language-Integrated Query*, ICFP 2013, DOI `10.1145/2500365.2500586`; *Query Shredding: Efficient Relational Evaluation of Queries over Nested Multisets*, SIGMOD 2014, DOI `10.1145/2588555.2612186`.
6. **Green, Karvounarakis, and Tannen (PODS 2007):** *Provenance Semirings*, PODS 2007, DOI `10.1145/1265530.1265535` ($K$-relations over commutative semirings, universal provenance polynomials $\mathbb{N}[X]$).

### Pinned Upstream Repository Source Inspections (Observed `2026-11-19`)

- `finch-tensor/Finch.jl` @ `7aa1ca1609054b94f3a1b56bb2221ae872513a10`:
  - `src/looplets/steppers.jl:1-160`: `Stepper` struct (`preamble`, `stop`, `chunk`, `next`, `body`, `seek`), `combine_style` priority lattice, `stepper_body` `Thunk`/`Switch` truncation lowering.
  - `src/looplets/runs.jl:1-110`: `Run` and `AcceptRun` lowering (`root.idx in PostOrderDFS(body)` constant-body hoist).
  - `src/looplets/spikes.jl:1-93`: `Spike(body, tail)` splitting into `[start, stop-1]` + `[stop, stop]` and `truncate` dynamic `Switch`.
  - `src/interface/traits.jl:1-160`: `SparseData`, `RepeatData`, `DenseData`, `ExtrudeData`, `HollowData`, `ElementData`, and `collapse_rep` normalization rules.
- `tensor-compiler/taco` @ `0e79acb56cb5f3d1785179536256e206790b2a9e`:
  - `src/lower/merge_lattice.cpp:22-156`: `MergeLatticeBuilder` (`RegionNode`, `ComplementNode`, `IntersectNode`, `UnionNode`).
  - `include/taco/format.h`: level format abstraction interfaces.
- `SIGMOD23p561/free-join` @ `c020bbc7964ba17594299a1910ad6b65eebdf0e0`:
  - `gj/src/join.rs:10-180`: `Instruction2::Intersect`/`Lookup`, `merge_occurrences`, `combine_lookups`.
  - `gj/src/trie.rs:19-160`: COLT lazy trie (`struct Trie { inner: cell::OnceCell<Box<TrieInner>, Thunk> }`, `Thunk(SmallVec<[u32; 4]>)`, `TrieInner::{Map, Set, DenseSet, Data}`).
- `bevyengine/bevy` @ `779770720e6ad916c1de38cf66a67d0e079ed1e3`:
  - `crates/bevy_ecs/src/query/access.rs:430-465,586-935`: `Access::is_compatible`, `FilteredAccess` DNF `filter_sets`, `FilteredAccess::is_compatible`, `FilteredAccess::extend` Cartesian product (`L818-827`), `AccessFilters::is_ruled_out_by` deliberate self-contradiction incompleteness comment (`L924-931`).
  - `crates/bevy_ecs/src/archetype.rs` & `crates/bevy_ecs/src/storage/mod.rs`: archetypal `Table` vs. `SparseSet` dual storage architecture.

### Executable Micro-Probe (`Basis: execution`, Observed `2026-11-19`)

Self-contained Python 3 probe verifying (Part A) IEEE-754 `0.0 * NaN` / `0.0 * inf` annihilator divergence under sparse zero-skipping; (Part B) cyclic triangle query $Q_\triangle$ ($N=500$, $|R|=|S|=|T|=1,001$) comparing binary hash join vs. unified trie coiteration across 4 $K$-semirings (`Bool`, `Bag`, `Tropical`, `Why-Prov`); and (Part C) Bevy's exact DNF `FilteredAccess::extend`/`is_ruled_out_by` vs. DPLL CNF SAT checking on both self-contradictory filters and $k$-nested `Or<...>` conjunctions ($k \in \{4, 8, 12, 16\}$):

```python
import math
# Part A: IEEE-754 annihilator violation
A_dense, A_sparse = [0.0, 0.0, 0.0, 2.0], {3: 2.0}
B_dense = [10.0, float("nan"), float("inf"), 5.0]
exact_ieee = sum(a * b for a, b in zip(A_dense, B_dense))       # -> nan
naive_looplet = sum(v * B_dense[i] for i, v in A_sparse.items()) # -> 10.0

# Part C: Exact model of bevy_ecs/src/query/access.rs:781-786,818-827,930
class BevyFilter:
    def __init__(self, clauses): self.clauses = clauses
    def extend(self, other):
        return BevyFilter([(w1 | w2, wo1 | wo2) for w1, wo1 in self.clauses for w2, wo2 in other.clauses])
    def bevy_is_disjoint(self, other):
        return all(bool(w1 & wo2) or bool(wo1 & w2) for w1, wo1 in self.clauses for w2, wo2 in other.clauses)
```

Recorded execution output (`python3 probe_coiter_freejoin_ecs.py`, exit code `0`):

```text
[Part A] IEEE-754 Sparse Annihilator Probe:
  Exact IEEE-754 dot(A_dense, B_dense) : nan (isnan=True)
  Naive zero-skipping Looplet dot      : 10.0 (DIVERGENT!)
  Precondition FiniteFloat(B) holds?   : False -> skipping REJECTED under strict IEEE-754
[Part B] Triangle Join (N=500, |R|=|S|=|T|=1001):
  Binary Join intermediates : 251,501 tuples (363.25 ms)
  WCOJ / Looplet steps      : 2,502 steps  (5.54 ms), output=1501 tuples
  Work reduction ratio      : 100.5x fewer operations
  K-Semiring outputs        : Bool=True, Bag(N)=5030, Tropical(min,+)=1.5, Why-Prov(sample)=['r_0_1', 's_1_0', 't00']
[Part C] Self-contradictory filter (With<A>, Without<A>) vs Unfiltered:
  Bevy is_ruled_out_by : disjoint=False (deliberately incomplete per access.rs:924)
  Complete SAT UNSAT   : disjoint=True
[Part C] Nested conjunction of k clauses: AND_{i=1..k} Or<(With<A_i>, Without<B_i>)>:
  k= 4 | Bevy DNF clauses=    16 (  0.16 ms) | CNF clauses= 6, SAT disjoint=True (0.109 ms)
  k= 8 | Bevy DNF clauses=   256 ( 10.25 ms) | CNF clauses=10, SAT disjoint=True (0.057 ms)
  k=12 | Bevy DNF clauses=  4096 (409.15 ms) | CNF clauses=14, SAT disjoint=True (0.087 ms)
  k=16 | Bevy DNF clauses= 65536 (1228.82 ms) | CNF clauses=18, SAT disjoint=True (0.098 ms)
```

## Revalidation

1. **Check Finch Looplet Combinator & Algebra Evolution:** Diff `finch-tensor/Finch.jl` against `7aa1ca1609054b94f3a1b56bb2221ae872513a10` in `src/looplets/` and `src/interface/traits.jl` for new Looplet styles, GPU/parallel load-balancing lowerings, or explicit IEEE-754 `NaN`/annihilator guards.
2. **Check Bevy `FilteredAccess` Disjointness Algorithm:** Diff `bevyengine/bevy` (`crates/bevy_ecs/src/query/access.rs`) against `779770720e6ad916c1de38cf66a67d0e079ed1e3` to verify whether `FilteredAccess` retains Cartesian-product DNF expansion (`extend`) and deliberate self-contradiction incompleteness (`is_ruled_out_by`), or adopts BDD/SAT-based filter checking.
3. **Check Free Join / COLT Integration in Production Engines:** Check follow-up Free Join implementations (e.g., DuckDB / DataFusion / `arXiv:2505.19918`) against `SIGMOD23p561/free-join` (`c020bbc7964ba17594299a1910ad6b65eebdf0e0`) for adaptive variable-ordering selection and vectorized COLT trie layout refinements.
4. **Rerun Sparse Annihilator & Disjointness Probes:** Whenever introducing a new sparse semiring optimization or ECS filter combinator, re-run `probe_coiter_freejoin_ecs.py` with `NaN`/`±inf`/`-0.0` edge cases and $k$-nested `Or` filters to detect silent IEEE-754 miscompilations or exponential filter blowups immediately.
