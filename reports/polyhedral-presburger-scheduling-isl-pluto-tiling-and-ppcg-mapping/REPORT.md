# Parametric Presburger Scheduling, Farkas Affine Loop Tiling, Accelerator Promotion, and Translation Validation

## Summary

Polyhedral compilers lift Static Control Parts (SCoPs) from syntax-bound loop nests into parametric Presburger sets and relations over unbounded mathematical integers $\mathbb{Z}$, compute exact element-wise dataflow dependences via lexicographic Parametric Integer Programming (PIP), synthesize communication-minimizing tilable hyperplane bands via the affine Farkas lemma, map outer bands and array footprints onto CPU vector units or SIMT GPU memory hierarchies, and lower transformed schedule trees back to imperative ASTs or MLIR/LLVM IR. Across the reference stack examined—`isl`, `Pluto`, `PPCG`, `Polygeist`, and `LLVM Polly`—soundness and scalability rest on five structural invariants:

1. **Exact $\mathbb{Z}$-Polyhedra vs. Rational Relaxation:** Presburger sets in `isl` (`struct isl_basic_map`) supplement equality and inequality matrices with explicit existentially quantified floor-division rows (`div`) representing $\lfloor f(\vec{p}, \vec{i}) / d \rfloor$, solved exactly via dual-simplex tableaus with parametric Gomory cuts and context splitting (`isl_tab_pip.c`). Rational LP relaxation (`ISL_BASIC_MAP_RATIONAL`) overapproximates parity- and stride-constrained accesses, creating spurious dependences (blocking parallelization) when used conservatively, or unsound emptiness conclusions if negated.
2. **Coefficient Growth and Deterministic Operation Quotas:** Fourier–Motzkin elimination, Gomory cuts, and schedule-tree AST separation exhibit worst-case doubly exponential coefficient or basic-set growth. `isl` prevents silent coefficient wraparound by pairing tagged 32-bit small-integer arithmetic (`isl_sioimath` over $[-2^{31}+1, 2^{31}-1]$, deliberately excluding `INT32_MIN`) with automatic promotion to heap `imath`/`GMP` arbitrary-precision integers, while bounding solver stalls through deterministic per-context operation counters (`isl_ctx_set_max_operations` returning `isl_error_quota`).
3. **Farkas Linearization of Permutability and Concurrent Tile Startup:** `Pluto` converts universally quantified dependence-satisfaction ($\phi_T(\vec{j}) - \phi_S(\vec{i}) \ge 0$) and parametric distance-bounding ($u(\vec{N}) + w - (\phi_T(\vec{j}) - \phi_S(\vec{i})) \ge 0$) predicates over each convex dependence polyhedron $\mathcal{D}_e$ into pure linear constraints on unknown schedule coefficients via the affine Farkas lemma (`farkas_lemma_affine`), eliminating non-negative Farkas multipliers $\lambda_k \ge 0$ by Fourier–Motzkin projection while enforcing non-triviality via orthogonal subspace constraints $H_S^\perp$. On stencils with negative spatial dependence components (such as $\vec{d} = (1, -1)$), rectangular time-space bands fail permutability; wavefront skewing ($\phi = ((1, 0), (1, 1))$) restores permutability at the cost of serialized corner startup, whereas diamond tiling ($\phi = ((1, -1), (1, 1))$) aligns the tile wavefront sum $\vec{w} = \phi_1 + \phi_2 = (2, 0)$ purely along time to enable concurrent spatial tile execution.
4. **Accelerator Tile Footprints and Uniform Barrier Placement:** `PPCG` partitions references into `gpu_array_ref_group` equivalence classes, bounds parametric tile footprints `tile_offset(i) <= a <= tile_offset(i) + tile_size - 1`, prefers register (`private`) over `__shared__` promotion at equal schedule depth, and inserts `sync` filter nodes into `isl` schedule trees before and after core compute bands (`gpu_tree_move_left_to_sync`, `gpu_tree_ensure_sync_after_core`). Conversely, raising existing GPU kernels with barriers into polyhedral MLIR (`Polygeist`) requires continuation-splitting parallel thread loops around `polygeist.barrier` (`BarrierRemovalContinuation.cpp`) so each barrier-free epoch becomes an atomic polyhedral statement.
5. **The $\mathbb{Z}$-to-Machine Soundness Chasm (Bit-Width Overflow, Aliasing, and Reductions):** Polyhedral schedule legality ($\forall (u \to v) \in D,\; \theta(u) \prec_{\text{lex}} \theta(v)$) holds over unbounded $\mathbb{Z}$ and disjoint named array spaces. Lowering back to C, LLVM IR, or CUDA is **unsound** unless three gaps are discharged: (a) **signed induction-variable and bound overflow** when skewing ($\text{ub}_{\text{skew}} = 2(N-1)$) exceeds 32-bit `nsw` bitvectors despite overflow-free input loops ($N = 2^{30}+2$), requiring type widening or runtime overflow tracking (`Polly` `IslExprBuilder::OverflowState`); (b) **pointer aliasing** between distinct syntactic base pointers (`A` vs. `B`), requiring `restrict` proofs or synthesized `MinMax` pointer-disjointness runtime alias checks (`PollyUseRuntimeAliasChecks`); and (c) **non-associative IEEE 754 floating-point reductions**, which static affine equivalence checkers (`Verdoolaege et al., TOPLAS 2012`) validate only up to algebraic commutativity and associativity over $\mathbb{R}$.

## Applicability

This report characterizes the coupled polyhedral representation, dependence analysis, scheduling, accelerator lowering, and verification pipeline across five pinned upstream implementations and four foundational specifications:

- **`PollyLabs/isl`** at commit `b822a2105dfe3c36f5d9c31071e61446bc88c0bc` (implementing Verdoolaege, ICMS 2010, `DOI: 10.1007/978-3-642-15582-6_49`): core C library providing parametric Presburger sets/relations, exact PIP lexicographic optimization, value-based dataflow (`isl_flow.c`), integrated Pluto/Feautrier schedule-tree synthesis (`isl_scheduler.c`), and polyhedral AST generation (`isl_ast_build.c`, `isl_ast_codegen.c`).
- **`bondhugula/pluto`** at commit `2b6fd99c976e4fec340cb227c8048bcd40864755` (implementing Bondhugula et al., PLDI 2008, `DOI: 10.1145/1375581.1375595`): source-to-source and library (`libpluto`) polyhedral optimizer formulating Farkas-multiplier ILPs for tilable band extraction, SCC fusion/cutting, and concurrent-start diamond tiling.
- **`Meinersbur/ppcg`** at commit `5e07c52e13fc8ea9fac7c1daf247d81d60822a93` (implementing Verdoolaege et al., ACM TACO 2013, `DOI: 10.1145/2400682.2400713`): `isl` schedule-tree-based C-to-CUDA and C-to-OpenCL compiler performing grid/thread mapping, register/shared-memory tile promotion, coalesced copy synthesis, and barrier insertion.
- **`llvm/Polygeist`** at commit `77c04bb2a7a2406ca9480bcc9e729b07d2c8d077` (Moses et al., PACT 2021, `DOI: 10.1109/PACT52795.2021.00011`): C/C++/CUDA frontend to MLIR `scf` and `affine` dialects, including `RaiseToAffine`, continuation-based SIMT barrier removal (`BarrierRemovalContinuation`), and the `Polymer` OpenScop/`isl`/`libpluto` bridge (`tools/polymer/`).
- **`llvm/llvm-project`** at commit `d1ee282181f8f83e7552136c344706c0e5400c9a` (`polly/` and `mlir/include/mlir/Dialect/Affine/`): production LLVM IR polyhedral optimizer (`Polly`) and MLIR `affine` dialect infrastructure, examined specifically for low-level IR soundness guards (SCEV validation, `nsw` overflow tracking, and runtime pointer-aliasing checks).
- **Static Affine Equivalence Specification** (Verdoolaege, Janssens, and Bruynooghe, ACM TOPLAS 2012, `DOI: 10.1145/2362389.2362393`): formal translation-validation algorithm for proving input-output equivalence between unoptimized and polyhedrally transformed static affine programs, including affine widening over loop-carried recurrences.

The architectural relationships among these subjects form a layered compilation and verification pipeline:

```text
C / CUDA / LLVM IR / MLIR scf
   |-- [Polygeist RaiseToAffine + BarrierRemovalContinuation] --> MLIR affine dialect
   |-- [LLVM Polly ScopDetection + SCEVValidator + Alias/Overflow RTCs] --> isl SCoP
   v
Presburger Domain, Access Relations, and Exact Dataflow (isl_basic_map, isl_flow.c, PIP)
   v
Farkas Affine Hyperplane & Band Synthesis (Pluto libpluto / isl_scheduler.c)
   v
Hierarchical Schedule Tree Transformations (isl_schedule_tree: tile, diamond, PPCG shared/sync)
   v
Polyhedral AST Scanning & Target Lowering (isl_ast_build -> C/OpenMP, CUDA/OpenCL, LLVM IR)
   v
Translation Validation & Equivalence Proof Obligations (TOPLAS 2012 dataflow DAG + widening)
```

Findings apply to affine and quasi-affine loop programs whose loop bounds, conditionals, and array subscripts are Presburger formulas in outer loop iterators and symbolic structure/scalar parameters (optionally extended with `Polly` boxed non-affine subregions). Claims regarding `isl` internal bit layouts apply specifically when compiled with `--with-int=sioimath` vs. `--with-int=gmp` or `--with-int=imath`.

## Findings

### 1. Parametric Presburger Sets, Existential Floor-Divisions, and Exact PIP Optimization in `isl`

`Basis: normative + source + execution`

#### 1.1 Internal Representation of Quasi-Affine Basic Maps (`struct isl_basic_map`)

Unlike classical polyhedral libraries (such as PolyLib) that pair constraint matrices with Chernikova vertex/ray dual generators, `isl` operates purely on constraint representations augmented with explicit integer floor-division variables (`PollyLabs/isl`, `isl_map_private.h:36-113`). Every `isl_set` is internally an `isl_map` with zero input dimensions (`n_in == 0`), and every `isl_map` is a finite union of `n` `isl_basic_map` conjuncts (`p[0 .. n-1]`, tagged with `ISL_MAP_DISJOINT` when pairwise disjoint).

A single `struct isl_basic_map` over $n_{\text{param}}$ symbolic parameters $\vec{p} \in \mathbb{Z}^{n_{\text{param}}}$, $n_{\text{in}}$ domain iterators $\vec{i} \in \mathbb{Z}^{n_{\text{in}}}$, $n_{\text{out}}$ range iterators $\vec{j} \in \mathbb{Z}^{n_{\text{out}}}$, and $n_{\text{div}}$ existentially quantified local variables $\vec{\alpha} \in \mathbb{Z}^{n_{\text{div}}}$ represents the Presburger relation:

$$\mathcal{R} = \left\{ (\vec{i} \to \vec{j}) \in \mathbb{Z}^{n_{\text{in}}} \times \mathbb{Z}^{n_{\text{out}}} \;\middle|\; \exists \vec{\alpha} \in \mathbb{Z}^{n_{\text{div}}}:\; E \begin{bmatrix} 1 \\ \vec{p} \\ \vec{i} \\ \vec{j} \\ \vec{\alpha} \end{bmatrix} = \vec{0} \;\land\; A \begin{bmatrix} 1 \\ \vec{p} \\ \vec{i} \\ \vec{j} \\ \vec{\alpha} \end{bmatrix} \ge \vec{0} \right\}$$

where:
- `eq` (`n_eq` rows) and `ineq` (`n_ineq` rows) store homogeneous affine rows of `isl_int` coefficients with column `0` holding the constant term.
- `div` (`n_div` rows) stores known explicit witnesses for the existential variables $\alpha_k$. When row `div[k]` has non-zero denominator $d_k = \text{div}[k][0] > 0$, $\alpha_k$ is functionally pinned to the unique integer floor division:
  $$\alpha_k = \left\lfloor \frac{c_{k,0} + \vec{c}_{k,p}\cdot\vec{p} + \vec{c}_{k,\text{in}}\cdot\vec{i} + \vec{c}_{k,\text{out}}\cdot\vec{j} + \sum_{m < k} c_{k,m}\alpha_m}{d_k} \right\rfloor \iff 0 \le f_k(\vec{p}, \vec{i}, \vec{j}, \alpha_{<k}) - d_k \alpha_k \le d_k - 1$$
  Notice the strict triangular ordering $m < k$: `div` definitions are acyclic, allowing `ISL_BASIC_MAP_NORMALIZED_DIVS` (`isl_map_private.h:45`) to canonicalize modulo/stride constraints (`i % 4 == 0`, `t_tile = floor(i / 32)`) and decide syntactic equality of witnesses without full quantifier elimination. When `div[k][0] == 0`, $\alpha_k$ is an unconstrained existential variable awaiting witness extraction or Fourier–Motzkin/Omega-style projection.
- Setting flag `ISL_BASIC_MAP_RATIONAL` (`1 << 4`, `isl_map_private.h:42`) reinterprets $\vec{i}, \vec{j}, \vec{\alpha}$ over $\mathbb{Q}$ rather than $\mathbb{Z}$. Over $\mathbb{Z}$, parity-disjoint accesses such as `Write A[2*i]` ($0 \le i \le 7$) and `Read A[2*j + 1]` ($0 \le j \le 7$) yield an empty intersection ($\emptyset$), whereas the $\mathbb{Q}$-relaxation admits rational witness $(i, j) = (1/2, 0)$ (verified by execution probe in Evidence). Any analysis that substitutes rational feasibility for integer feasibility introduces false dependences on strided/interleaved memory layouts.

#### 1.2 Parametric Integer Programming (PIP), Gomory Cuts, and Coalescing

`isl` decides emptiness, sample-point generation, projection, and lexicographic extremum (`isl_basic_map_lexmin` / `isl_map_lexmax`) using Feautrier's Parametric Integer Programming algorithm (`DOI: 10.1051/ro/1988220302431`) implemented over exact rational simplex tableaus in `isl_tab.c` and `isl_tab_pip.c`.

1. **Dual-Simplex + Context Tableau Architecture (`isl_tab_pip.c:155-215, 3870-3915`):** Variables are shifted to be non-negative via big-$M$ symbolic representation ($M + x$ for `lexmin`, $M - x$ for `lexmax`, `isl_tab_pip.c:168-170`). A *main tableau* tracks primal variables $(\vec{x}, \vec{\alpha})$ as affine functions of symbolic parameters $\vec{p}$, while a companion *context tableau* tracks the currently active feasibility chamber on $\vec{p}$.
2. **Parametric Sign Splitting:** Whenever a row in the main tableau has a parametric sample constant term $c(\vec{p})$ whose sign is undetermined on the current context chamber—i.e., both $c(\vec{p}) < 0$ and $c(\vec{p}) \ge 0$ are feasible in the context tableau—`find_solutions` (`isl_tab_pip.c:3872-3910`) snapshots the context tableau, branches into two sub-chambers ($c(\vec{p}) \ge 0$ vs. $c(\vec{p}) \le -1$), and pivots only on the negative branch.
3. **Parametric Gomory Fractional Cuts (`add_cut`, `isl_tab_pip.c:1815-1897`):** Once all rows are lexicographically positive over $\mathbb{Q}$ for the active parameter chamber, `next_non_integer_var` checks whether the rational optimum assigns non-integral values. If a row has fractional constant/parameter entries, `add_cut` synthesizes a parametric Gomory cut—introducing a fresh integer floor-division parameter row `pdiv` ($\lfloor g(\vec{p})/d \rfloor$) into the context tableau when parameter coefficients are fractional—and calls `restore_lexmin` (`isl_tab_pip.c:1892`) to re-establish dual-simplex lexicographic optimality. The resulting piecewise quasi-affine solution (`isl_pw_multi_aff`) partitions the parameter space into disjoint chambers, each mapping $\vec{p}$ to the exact lexicographic minimum over $\mathbb{Z}^n$.
4. **Coalescing Disjunctive Explosion (`isl_coalesce.c`):** Set difference, complementation, and PIP context splitting partition maps into many `isl_basic_map` pieces. Left unchecked, $k$ sequential subtractions produce $O(2^k)$ basic maps. `isl_map_coalesce` (`isl_coalesce.c`) inspects pairs of basic maps $(B_1, B_2)$ and merges them into a single basic map whenever one is a subset of the other, their union is convex along an adjacent opposing facet ($a(\vec{x}) \ge 0$ vs. $a(\vec{x}) \le -1$ with identical remaining constraints), or the integer hull of $B_1 \cup B_2$ contains no extraneous lattice points (`wrapping` check).

#### 1.3 Arbitrary-Precision Integer Backends (`gmp`, `imath`, `sioimath`) and Deterministic Quotas

`Basis: source`

Polyhedral Pivoting and Gomory cuts routinely amplify constraint coefficients beyond 64 bits on deeply nested or large-stride loops. `isl` supports three compile-time `isl_int` backends:
- **`gmp` (`isl_int_gmp.h`):** Wraps GNU MP `mpz_t`; exact, fast on huge limbs, but incurs heap metadata/allocation overhead for small coefficients ($0, \pm 1$) that dominate >99% of polyhedral rows.
- **`imath` (`isl_int_imath.h`):** MIT-licensed arbitrary-precision C library bundled in `imath_wrap/`, slower than GMP on multi-limb arithmetic.
- **`sioimath` (`isl_int_sioimath.h:31-115`):** Small-Integer Optimization wrapper over `imath` (used by LLVM `Polly`). Each `isl_sioimath` is an 8-byte word (`uint64_t` or `uintptr_t`) discriminated by bit `0` (LSB):
  - **Small inline representation (`val & 1 == 1`):** Upper 32 bits store a signed `int32_t` in the symmetric closed range `[-INT32_MAX, INT32_MAX] = [-2147483647, +2147483647]`. Crucially, `isl_int_sioimath.h:78-92` **excludes `INT32_MIN` (`-2147483648`)** from inline storage (`#define ISL_SIOIMATH_SMALL_MIN (-INT32_MAX)`) because `abs(INT32_MIN)`, `-INT32_MIN`, and `INT32_MIN / -1` overflow `int32_t`; any result equal to `-2147483648` or outside `[-2147483647, 2147483647]` widens in `int64_t` scratch arithmetic and promotes seamlessly to heap `mp_int*`.
  - **Big heap representation (`val & 1 == 0`):** Aligned non-null `mp_int*` pointer (`malloc` guarantees $\ge 2$-byte alignment so LSB is `0`).
- **Deterministic Operation Quota (`isl_ctx.c:51-56, 360-378`):** Rather than wall-clock timeouts (which make compiler code generation non-deterministic across CPU loads and break reproducible builds), `isl_ctx` increments `ctx->operations` on every core tableau/constraint step. When `ctx->max_operations > 0` and `ctx->operations >= ctx->max_operations`, `isl` aborts the pass deterministically with `isl_error_quota` (`"maximal number of operations exceeded"`), allowing callers such as LLVM `Polly` to bail out cleanly and keep the unoptimized loop nest.

---

### 2. Exact Value-Based Array Dataflow Analysis vs. Memory-Based Dependences

`Basis: normative + source`

Polyhedral optimizers distinguish **memory-based dependences** (any two accesses touching the same array cell) from **value-based (exact dataflow) dependences** (Feautrier, 1991, `DOI: 10.1007/BF01407931`, implemented in `PollyLabs/isl`, `isl_flow.c:633-665, 1127-1210`).

Given iteration domain $I$, an initial lexical execution schedule $\theta_{\text{init}} : I \to \mathbb{Z}^d$, must-write access relation $W_{\text{must}} \subseteq I \times M$, may-write access relation $W_{\text{may}} \subseteq I \times M$ (with $W_{\text{must}} \subseteq W_{\text{may}}$, capturing predicated stores or coarse subregions), and read access relation $R \subseteq I \times M$:

1. **Memory-Based Dependences** pair every conflicting access regardless of intervening overwrites:
   $$D_{\text{RAW}}^{\text{mem}} = \left\{ (w \to r) \in W_{\text{may}} \circ R^{-1} \;\middle|\; \theta_{\text{init}}(w) \prec_{\text{lex}} \theta_{\text{init}}(r) \right\}$$
   $$D_{\text{WAR}}^{\text{mem}} = \left\{ (r \to w) \in R \circ W_{\text{may}}^{-1} \;\middle|\; \theta_{\text{init}}(r) \prec_{\text{lex}} \theta_{\text{init}}(w) \right\}, \quad D_{\text{WAW}}^{\text{mem}} = \left\{ (w_1 \to w_2) \in W_{\text{may}} \circ W_{\text{may}}^{-1} \;\middle|\; \theta_{\text{init}}(w_1) \prec_{\text{lex}} \theta_{\text{init}}(w_2) \right\}$$
   Memory-based WAW and WAR edges are *false* (storage-related) dependences, and $D_{\text{RAW}}^{\text{mem}}$ includes dead transitive writes overwritten before $r$ executes.

2. **Exact Value-Based Flow (`compute_val_based_dependences`, `isl_flow.c:1127`):** For each read $(r, m) \in R$, the true producer of the value read at $(r, m)$ is the **lexicographically latest** write under $\theta_{\text{init}}$ that precedes $r$ and writes $m$:
   $$D_{\text{must-flow}} = \left\{ (w \to r) \in W_{\text{must}} \circ R^{-1} \;\middle|\; \theta_{\text{init}}(w) \prec_{\text{lex}} \theta_{\text{init}}(r) \;\land\; \neg \exists w' \in I:\; (w \to r) \text{ shares } m \text{ with } (w' \to r) \in W_{\text{may}} \circ R^{-1} \;\land\; \theta_{\text{init}}(w) \prec_{\text{lex}} \theta_{\text{init}}(w') \prec_{\text{lex}} \theta_{\text{init}}(r) \right\}$$
   In `isl_flow.c`, `last_source` (`L633`) computes the latest must-write via parametric `isl_map_lexmax` in PIP, subtracts covered sink instances, and iteratively processes earlier may-writes until all remaining reads fall into `must_no_source` (live-in reads from array values initialized prior to the SCoP) or `may_no_source` (reads potentially unkilled due to conditional `may_writes`).
   - **Optimization Consequence:** If scalar/array privatization or live-out memory expansion is allowed, only $D_{\text{flow}}$ constrains producer-consumer order. When in-place memory is retained (standard `Pluto`, `PPCG`, and `Polly` mode), both exact flow ($D_{\text{flow}}$) and killed-memory anti/output dependences ($D_{\text{WAR}}, D_{\text{WAW}}$, pruned of transitive killed pairs) enter the validity relation `validity`.

---

### 3. Farkas-Multiplier Affine Hyperplane Synthesis, Pluto Tiling, and Schedule Trees

`Basis: normative + source + execution`

#### 3.1 Pluto Permutability, Distance Bounding, and `farkas_lemma_affine`

Given statement $S$ with $d_S$-dimensional iteration vector $\vec{i}_S$ and global structural parameter vector $\vec{N} \in \mathbb{Z}^{n_{\text{par}}}$, a 1D affine scheduling hyperplane assigns execution timestamp:

$$\phi_S(\vec{i}_S, \vec{N}) = \vec{c}_S \cdot \vec{i}_S + \vec{p}_S \cdot \vec{N} + c_{S,0}$$

Under `bondhugula/pluto` (`DOI: 10.1145/1375581.1375595`), a band of $k$ independent hyperplanes $(\phi^{(1)}, \dots, \phi^{(k)})$ is ** rectangularly tilable** (permutable without loop-reversal or negative-face hazards) if and only if every dependence $e = (S \to T)$ with convex dependence polyhedron $\mathcal{D}_e(\vec{i}_S, \vec{j}_T, \vec{N}) \ge \vec{0}$ is **weakly satisfied** across every dimension $r \in \{1, \dots, k\}$:

$$\forall (\vec{i}_S, \vec{j}_T, \vec{N}) \in \mathcal{D}_e:\quad \phi_T^{(r)}(\vec{j}_T, \vec{N}) - \phi_S^{(r)}(\vec{i}_S, \vec{N}) \ge 0$$

To simultaneously maximize tile-level locality and outer parallelism (minimizing inter-tile communication volume and reuse distance), `Pluto` upper-bounds the forward dependence distance by an affine function of the global parameters $\vec{u} \cdot \vec{N} + w$ with $\vec{u} \ge \vec{0}, w \ge 0$:

$$\forall (\vec{i}_S, \vec{j}_T, \vec{N}) \in \mathcal{D}_e:\quad (\vec{u} \cdot \vec{N} + w) - \left(\phi_T^{(r)}(\vec{j}_T, \vec{N}) - \phi_S^{(r)}(\vec{i}_S, \vec{N})\right) \ge 0$$

and minimizes the lexicographic objective $\text{lexmin}(\vec{u}, w, \dots)$ over non-negative schedule coefficients (extended to sign-unrestricted coefficients via `Pluto+` bounds when loop reversal is required).

- **Why Global Parameter Context Aggregation Is Required (`pluto/lib/pluto.c:1138-1208`):** Suppose dependence $e_1$ has distance $\le N$ (independent of parameter $M$) and dependence $e_2$ has distance $\le M$ (independent of $N$). A single affine upper bound $u_1 N + u_2 M + w$ requires $u_1 N + u_2 M + w \ge N$ on $\mathcal{D}_{e_1}$, which is impossible over unconstrained $M \in \mathbb{Z}$ unless $M \ge 0$ is known inside $\mathcal{D}_{e_1}$! `normalize_domains` (`pluto.c:1138`) solves this by projecting iterators out of every statement domain via `fourier_motzkin_eliminate`, aggregating the resulting parameter inequalities into `param_context`, and appending `param_context` to every `deps[i]->bounding_poly`.
- **Exact Linearization via Affine Farkas' Lemma (`pluto/lib/constraints.c:213-280`):** Both inequalities have the universal form $\forall \vec{x} \in \mathcal{D}_e = \{\vec{x} \mid G\vec{x} + \vec{g} \ge \vec{0}\},\; \psi(\vec{x}) \ge 0$ where $\mathcal{D}_e \neq \emptyset$. By the affine Farkas lemma, an affine form $\psi(\vec{x})$ is non-negative everywhere on a non-empty polyhedron $G\vec{x} + \vec{g} \ge \vec{0}$ if and only if $\psi(\vec{x})$ is a non-negative affine combination of the faces:
  $$\psi(\vec{x}) \equiv \lambda_0 + \sum_{m=1}^{q} \lambda_m (G_{m,\cdot} \vec{x} + g_m), \qquad \lambda_0 \ge 0, \dots, \lambda_q \ge 0$$
  In `farkas_lemma_affine` (`constraints.c:213`), `Pluto` converts `dom` to pure $\ge 0$ inequalities (`idom`), appends a synthetic constant row `1 >= 0` (`constraints.c:229-230`) for $\lambda_0$, equates the coefficients of each iterator, parameter, and constant `1` (`idom->ncols` equalities, `constraints.c:250-259`), enforces $\lambda_j \ge 0$ (`constraints.c:262-265`), and eliminates all `idom->nrows` Farkas multipliers via `fourier_motzkin_eliminate_smart` (`constraints.c:267-274`). The surviving system contains *only* linear inequalities over $(\vec{c}_S, \vec{p}_S, c_{S,0}, \vec{u}, w)$ solvable by a single ILP call.
- **Preventing the Trivial Zero Schedule (`pluto/lib/pluto.c:698-725`):** Without rank constraints, $\phi_S \equiv 0, \vec{u} = \vec{0}, w = 0$ trivially optimizes the ILP. After finding $r-1$ hyperplanes for $S$ collected as rows of $H_S$, `Pluto` computes the orthogonal subspace basis $H_S^\perp = I - H_S^T (H_S H_S^T)^{-1} H_S$ (scaled to integers) and constrains $\sum_j |(H_S^\perp \vec{c}_S)_j| \ge 1$ (`orthcst` in `EAGER` or `LAZY` linear-independence mode). When no tilable hyperplane exists across all statements, `cut_smart` (`pluto.c:592-615`) cuts edges between Strongly Connected Components (SCCs) of the Data Dependence Graph (`ddg`) according to `FusionType` (`kNoFuse`, `kMaximalFuse`, `kSmartFuse`, `kTypedFuse`, `kHybridFuse`, `pluto.h:30-45`).

#### 3.2 Negative-Orthant Stencils: Wavefront Skewing vs. Diamond Tiling

Consider the 1D 3-point Jacobi time-iterated stencil $S(t, i)$ with dependence vectors $\vec{d}_1 = (1, -1)$, $\vec{d}_2 = (1, 0)$, and $\vec{d}_3 = (1, +1)$:
1. **Unskewed Rectangular Band $H = \begin{bmatrix} 1 & 0 \\ 0 & 1 \end{bmatrix}$:** Fails Farkas permutability on the second hyperplane because $\phi^{(2)}(\vec{d}_1) = 0\cdot 1 + 1\cdot(-1) = -1 < 0$; rectangular tile $(t_B, i_B)$ both depends on $(t_B, i_B+1)$ (via $\vec{d}_1$) and feeds $(t_B, i_B+1)$ (via $\vec{d}_3$ within the same time tile), creating a cycle between adjacent spatial tiles.
2. **Standard Pluto Skewed Wavefront $H = \begin{bmatrix} 1 & 0 \\ 1 & 1 \end{bmatrix}$:** Yields $\phi(\vec{d}_k) \in \{(1, 0), (1, 1), (1, 2)\} \ge \vec{0}$. Permutable and tilable, but the tile-space wavefront normal $\vec{w} = \vec{h}_1 + \vec{h}_2 = (2, 1)$ has non-zero spatial slope (`w_i = 1`): execution starts at a single corner tile $(0, 0)$ and ramps up/down sequentially, starving parallel cores at small $T$ or narrow spatial grids.
3. **Diamond Tiling (`--diamondtile`, `pluto/lib/tile.c:85-105`):** Replaces the time hyperplane $(1, 0)$ (`evicted_hyp` in `pluto_diamond_tile_reschedule`) with the opposing face normal $(1, -1)$, giving $H_{\text{diamond}} = \begin{bmatrix} 1 & -1 \\ 1 & 1 \end{bmatrix}$. All dependence deltas remain strictly non-negative—$\phi(\vec{d}_1) = (2, 0)$, $\phi(\vec{d}_2) = (1, 1)$, $\phi(\vec{d}_3) = (0, 2)$—while the outer wavefront normal $\vec{w} = \vec{h}_1 + \vec{h}_2 = (2, 0)$ has **zero spatial component (`w_i = 0`)**. For tile size $B$, scheduling tiles by $(\tau_1 + \tau_2,\; \tau_1)$ with $\tau_1 = \lfloor(t - i)/B\rfloor, \tau_2 = \lfloor(t + i)/B\rfloor$ launches every spatial diamond at wavefront $w = \tau_1 + \tau_2$ concurrently at $t = 0$ with **zero intra-wavefront cross-tile dependences** (verified empirically in Evidence Probe 1).

#### 3.3 `isl` Schedule Constraints, Schedule Trees, and AST Code-Size Hazards

`PollyLabs/isl` integrates a generalized Pluto-plus-Feautrier scheduler (`isl_scheduler.c:60-145`) producing first-class **Schedule Trees** (`isl_schedule_tree.h:54-110`):
- **Constraint Taxonomy (`isl_scheduler.c`):** Separates hard `validity` edges ($\theta(u) \preceq \theta(v)$), soft locality `proximity` edges (minimized in LP distance bounds), parallel/SIMD `coincidence` edges (enforcing $\theta_r(u) - \theta_r(v) = 0$ to mark `coincident[r] = 1`, `isl_scheduler.c:122`), and `conditional_validity` pairs `(condition, validity)` used to forbid live-range overlap of local scalars across parallel/tiled iterations without serializing iterations when scalars are privatized. When the Pluto-style LP fails to carry a cyclic dependence across a tilable band, `isl` falls back locally to Feautrier's multidimensional scheduling LP (maximizing the count of strongly satisfied dependences $\theta_r(v) - \theta_r(u) \ge 1$) to break SCC cycles cleanly.
- **Schedule Tree Grammar (`isl_schedule_tree.h:58-72`):** Replaces flat scattering matrices (`2d+1` union maps) with explicit tree nodes: `domain` (root instance set), `band` (partial `isl_multi_union_pw_aff` + `permutable` flag + per-member `coincident` bits + AST build options), `filter` (subset restriction), `sequence` (ordered children, equivalent to loop distribution/fission), `set` (unordered children), `context` (parameter assumptions), `guard` (enforced outer AST `if`), `mark` (backend annotation such as `"kernel"` or `"shared"`), `expansion`, and `extension` (injecting synthetic copy/sync statements).
- **Polyhedral AST Scanning Blowup (`isl_ast_build.c`, `isl_ast_codegen.c`; Bastoul, `DOI: 10.1109/PACT.2004.1342537`; Grosser et al., `DOI: 10.1145/2743016`):** Generating loop nests over union domains with boundary peels, skewed tiles, or unaligned strides splits iteration polyhedra into exponential chamber combinations if overlapping domains are separated unconditionally. `isl` exposes four per-dimension AST build options on `band` nodes: `default`, `atomic` (forces a single loop per schedule dimension with internal `if` guards, bounding code size to $O(1)$ copies at the cost of inner-loop branches), `separate` (eliminates inner `if` guards by peeling disjoint full-tile chambers, risking exponential code duplication on high-dimensional tiles), and `unroll` (enumerates point slices explicitly). Production pipelines (`PPCG`, `Polly`) pin tile-loop bands to `separate` only on bounded interior full tiles (`isolate` option) while keeping boundary cleanup loops `atomic`.

---

### 4. Accelerator Tile Promotion, SIMT Barrier Insertion, and MLIR Affine Raising/Lowering

`Basis: source`

#### 4.1 GPU Grid/Thread Mapping, Shared/Private Promotion, and `sync` Insertion in `PPCG`

`Meinersbur/ppcg` (`DOI: 10.1145/2400682.2400713`) lowers an `isl_schedule` into host orchestration plus CUDA/OpenCL kernels by rewriting the schedule tree directly (`gpu.c`, `gpu_group.c`, `gpu_tree.c`):

1. **Grid and Thread Band Mapping (`gpu.c`, `gpu_tree.c:20-85`):** Outer tilable band dimensions with `coincident == 1` are tiled by `grid_size` and `tile_size` (`read_tile_sizes`, `gpu.c:601`). Tile iterators map modulo `grid_size` to CUDA block indices `(b0, b1)` beneath a `mark("kernel")` node; intra-tile parallel point dimensions map modulo `block_size` to CUDA thread indices `(t0, t1, t2)` beneath `mark("thread")` nodes (`gpu_tree.c:60-79`).
2. **Array Reference Grouping and Promotion Priority (`gpu_group.c:71-110`):** References to the same base array inside a kernel are clustered into `gpu_array_ref_group` sets when their tile footprints coalesce cleanly. For each group, `PPCG` computes candidate `private_tile` (per-thread register array; valid only if references are thread-private along parallel dimensions and `requires_unroll` holds so register indices resolve to compile-time constants, `gpu_group.c:107-115`) and `shared_tile` (per-block `__shared__` memory array bounded by affine `tile_offset(i) <= a <= tile_offset(i) + tile_size - 1`, `gpu.c:857-885`). Selection follows `gpu_array_ref_group_type` (`gpu_group.c:78-88`):
   - If both `private_tile` and `shared_tile` exist, the tile at the **smaller schedule depth** (outermost reuse loop) wins; if depths are equal, **`ppcg_access_private` wins** over `ppcg_access_shared`.
   - `check_shared_memory_bound` (`gpu.c:952-975`) greedily deducts promoted group byte footprints from `options->max_shared_memory`, demoting excess groups back to global memory.
3. **Coalesced Copy Synthesis and Barrier Placement (`gpu.c:920-937, 2006-2127`, `gpu_tree.c:566-610`):** Promoted `__shared__` groups inject `extension` nodes into the schedule tree for cooperative block-wide `read` (global $\to$ shared) and `write` (shared $\to$ global) statements, wrapping the innermost array dimension across `t0` (`threadIdx.x`) for DRAM burst coalescing. To prevent RAW/WAR/WAW data races across warps sharing `__shared__` tiles, `gpu_tree_move_left_to_sync` (`gpu_tree.c:591`) and `gpu_tree_ensure_sync_after_core` (`gpu_tree.c:566`) insert synthetic domain filter nodes named `"sync..."` (`ppcg_kernel_sync`, lowered to `__syncthreads()` or `barrier(CLK_LOCAL_MEM_FENCE)`) strictly *outside* the `"thread"` mark node—structurally guaranteeing that generated barriers never execute inside thread-divergent conditionals unless an AST guard depends directly on `t0..t2` (which `PPCG` prevents by placing `thread` filters inside synchronization sequences).

#### 4.2 C/CUDA-to-MLIR `affine` Raising and Continuation Barrier Splitting in `Polygeist`

`llvm/Polygeist` bridges raw C/C++/CUDA ASTs into MLIR's structured `affine` dialect (`mlir/include/mlir/Dialect/Affine/IR/AffineOps.td`) and external `isl`/`Pluto` schedulers (`Polymer`):
- **`RaiseToAffine` and `AffineCFG` (`lib/polygeist/Passes/RaiseToAffine.cpp`, `AffineCFG.cpp`):** Converts lowered `scf.for` / `scf.if` loops with `arith.cmpi` bounds (`slt`, `sle`, `sgt`, `sge`, `RaiseToAffine.cpp:74-82`) and pointer/index arithmetic into `affine.for`, `affine.if`, `affine.load`, and `affine.store` operations whose index operands satisfy MLIR's `AffineScope` dimensional/symbolic separation (`dim` for loop IVs vs. `symbol` for region-invariant parameters).
- **SIMT Barrier Removal via Continuations (`lib/polygeist/Passes/BarrierRemovalContinuation.cpp:39-89`):** In CUDA/OpenCL inputs, `__syncthreads()` (`polygeist.barrier`) appears inside thread-parallel `scf.parallel` bodies—a construct illegal to reorder or fuse across as an ordinary statement. Following Karrenberg and Hack, `BarrierRemovalContinuation` identifies `scf.parallel` ops with immediate `polygeist.barrier` ops (`hasImmediateBarriers`, `L39-46`), wraps their bodies in `scf.execute_region`, lowers intra-body `scf.for`/`scf.if` control flow around the barrier into CFG basic blocks (`applyCFGConversion`, `L74-89`), splits the parallel loop across each barrier boundary with explicit state `memref` spill arrays for live SSA values across epochs, and re-raises each barrier-free parallel loop into a pure `affine.parallel` / `affine.for` nest amenable to polyhedral fusion and tiling.
- **OpenScop Round-Tripping (`tools/polymer/lib/Transforms/PlutoTransform.cc:46-106`):** `Polymer` serializes `affine` functions into OpenScop (`createOpenScopFromFuncOp`), invokes `libpluto` configured with `options->isldep = 1` (forcing `isl` exact flow dependence analysis in place of legacy `candl`, `PlutoTransform.cc:62-66`) and optional `diamondtile`, and reconstructs MLIR `affine` loops via CLooG/`isl` AST lowering (`createFuncOpFromOpenScop`).

---

### 5. Polyhedral Schedule Equivalence Validation and Soundness Hazards

`Basis: normative + source + execution + derived`

#### 5.1 Cross-System Architecture and Soundness Matrix

| Subsystem / Property | `PollyLabs/isl` | `bondhugula/pluto` | `Meinersbur/ppcg` | `llvm/Polygeist` (`Polymer`) | `LLVM Polly` (`llvm-project`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Core Representation** | `isl_basic_map` (`eq`, `ineq`, `div`) + `isl_schedule_tree` | `PlutoConstraints` (`int64_t` matrix) + `Band` | `pet` SCoP + `isl_schedule_tree` | MLIR `affine` dialect $\leftrightarrow$ `OslScop` | LLVM `SCEV` $\to$ `isl_set`/`isl_schedule` |
| **Coefficient Arithmetic** | `gmp`, `imath`, or tagged `sioimath` (`[-2^31+1, 2^31-1]` + big) | Fixed `int64_t` rows in FM/ILP (`lib/constraints.c`) | `isl` (`gmp`/`imath`) | MLIR `int64_t` `FlatAffineValueConstraints` + `Pluto` | `isl` (`sioimath`) |
| **Dependence Engine** | Exact value flow (`isl_flow.c` PIP `lexmax`) | `isl` (`--isldep`, default) or `candl` | `isl` exact flow + live-range `conditional_validity` | `isl` (`options->isldep = 1` forced) | `isl_union_access_info_compute_flow` |
| **Signed IV / Bound Overflow** | Models mathematical $\mathbb{Z}$ only | Models $\mathbb{Z}$; emits C `int` / `long` loop headers | Models $\mathbb{Z}$; emits C/CUDA `int` indices | Raises C signed `nsw` ops directly to $\mathbb{Z}$-`affine` | Emits `IslExprBuilder` `OverflowState` RTCs + `i64` widening |
| **Pointer Aliasing Soundness** | Caller supplies disjoint `isl_space` names | Assumes distinct C array names do not alias | Assumes distinct C array names do not alias | Assumes distinct `memref` args do not alias unless lowered | Synthesizes `MinMax` runtime alias checks (`PollyUseRuntimeAliasChecks`) |
| **Accelerator Barrier Safety** | Agnostic (`mark`/`filter` nodes only) | CPU OpenMP `#pragma omp parallel for` | Inserts `sync` nodes outside `thread` mark (`gpu_tree.c`) | Splits `polygeist.barrier` via `scf` continuations | Offloads via `PPCGCodeGeneration` (optional) |

*(Notice a subtle implementation asymmetry revealed by `lib/constraints.c`: whereas `isl` uses arbitrary-precision `isl_int`, `Pluto`'s internal `PlutoConstraints` stores matrix entries in fixed 64-bit `int64_t` during `fourier_motzkin_eliminate_smart`, which can overflow on pathological multi-step Farkas projections even when `isldep` computed exact dependences.)*

#### 5.2 Translation Validation of Affine Schedules (`Verdoolaege et al., TOPLAS 2012`)

`Basis: normative + derived`

There are two distinct levels of polyhedral verification:

1. **Schedule-Legality Witness Checking (Dependence Preservation):** Given fixed statement bodies, exact dependence relation $D = D_{\text{RAW}} \cup D_{\text{WAR}} \cup D_{\text{WAW}}$, and transformed schedule relation $\Theta \subseteq I \times \mathbb{Z}^k$ (total and single-valued on $I$), $\Theta$ preserves sequential memory semantics over $\mathbb{Z}$ if and only if the Presburger emptiness query holds:
   $$\left\{ (u \to v) \in D \;\middle|\; \neg\left(\Theta(u) \prec_{\text{lex}} \Theta(v)\right) \right\} = \emptyset$$
   and for every dimension $r$ marked parallel (`coincident[r] == 1` or SIMT thread-mapped):
   $$\left\{ (u \to v) \in D \;\middle|\; \Theta_{1..r-1}(u) = \Theta_{1..r-1}(v) \;\land\; \Theta_r(u) \neq \Theta_r(v) \right\} = \emptyset$$
   This check requires only Presburger set difference and `isl_map_is_empty` (PIP), completely bypassing trusted Farkas/ILP solver code, *provided* $D$ was extracted soundly and statement bodies were not algebraically mutated, peeled, or privatized.
2. **Full Input-Output Equivalence Checking (`DOI: 10.1145/2362389.2362393`):** When an optimizer applies scalar privatization, array expansion (`shared_tile` / `private_tile` copies in `PPCG`), loop peeling, or reduction reordering, $D$-preservation on the original memory space no longer applies directly. Verdoolaege, Janssens, and Bruynooghe construct a **Dynamic Dataflow Equivalence Graph** backwards from live-out array elements $A_{\text{out}}[\vec{a}]$ of the original program $P_1$ and transformed program $P_2$. Nodes carry proof obligations of the form:
   $$\forall (\vec{i}_1, \vec{i}_2) \in R_{v}:\quad \text{val}_{P_1}(S_1, \vec{i}_1) = \text{val}_{P_2}(S_2, \vec{i}_2)$$
   Using exact value-based dataflow (`isl_flow.c`), each read operand is propagated backward across its piecewise quasi-affine producer relation. On loop-carried recurrences ($x[i] = f(x[i-1])$) where backward induction would unfold unboundedly along parametric trip counts $N$, the verifier computes a mismatch domain $M_v$ (pairs $(\vec{i}_1, \vec{i}_2) \in R_v$ where outputs could diverge) and applies **polyhedral widening** (dropping shifting facet bounds across successive backward iterations to overapproximate the transitive dependence cone) until $R_v$ reaches an inductive invariant disjoint from mismatched base cases. Commutative-associative reductions (`+=`) are handled by matching bijective Presburger correspondences between reduction operand domains—which is sound over $(\mathbb{Z}, +)$ or $(\mathbb{Q}, +)$, but **known not to apply** to strict IEEE 754 floating-point addition (`(a + b) + c != a + (b + c)`).

#### 5.3 Concrete Soundness Hazards at the C / LLVM IR / MLIR Boundary

`Basis: source + execution`

1. **Hazard A — Signed Bit-Vector Overflow Introduced by $\mathbb{Z}$-Valid Skewing:**
   Consider a 2D C/LLVM loop `for (int32_t i = 0; i < N; i++) for (int32_t j = 0; j < N; j++)` with runtime parameter $N = 2^{30} + 2 = 1073741826 \le \text{INT32\_MAX}$ ($2147483647$). Every iteration of the input program executes strictly within `int32_t` without signed overflow ($\max(i, j) = 1073741825$). Applying `Pluto`'s legal wavefront skew $(t_0, t_1) = (i,\; i + j)$ generates transformed upper bound `t1 <= 2 * N - 2`. Over $\mathbb{Z}$, $2N - 2 = 2147483650$; in 32-bit two's-complement `int32_t`, `2 * N - 2` wraps to **`-2147483646`** (or triggers immediate C/LLVM `nsw` poison UB), causing the loop guard `t1 <= -2147483646` to skip all iterations (or loop infinitely if `t1++` wraps at `INT32_MAX`).
   - *Mitigation in LLVM `Polly` (`polly/lib/CodeGen/IslExprBuilder.cpp:22-165`):* `IslExprBuilder` promotes synthesized loop iterators and affine expressions to `i64` (or wider `APInt` bitwidths) and, when `setTrackOverflow(true)` is enabled (`IslExprBuilder.cpp:62-75, 130-162`), lowers `Add`/`Sub`/`Mul` via `@llvm.sadd.with.overflow` / `@llvm.ssub.with.overflow` / `@llvm.smul.with.overflow`, OR-accumulating overflow flags into `polly.overflow.state` to branch into the unoptimized scalar fallback loop before executing the transformed SCoP. Source-to-source `Pluto` and `PPCG` emit unguarded `int` loop bounds (`t1 <= 2*N - 2`) unless manually widened.

2. **Hazard B — Silent Carried-Dependence Erasure Under Unverified Pointer Aliasing:**
   Consider `void step(int *A, const int *B, int N) { for (int i = 1; i < N; i++) A[i] = B[i-1] + 1; }`. `Pluto`, `PPCG`, and `Polymer` assign `A` and `B` to distinct `isl_space` tuple names (`"A"` vs. `"B"`), deriving $D_{\text{RAW}} = \emptyset$. `PPCG` promotes `B[t .. t+7]` into `shared_B[8]` once per tile before writing `A[t .. t+7]`. When a caller invokes `step(buf, buf, 8)` in place (`A == B`), the sequential loop computes prefix propagation `buf[7] == 17` (`buf[0] = 10` plus 7 increments), whereas the tile-promoted schedule reads stale `buf` values and produces **`buf[7] == 1`** (verified in Evidence Probe 2).
   - *Mitigation in LLVM `Polly` (`polly/lib/Analysis/ScopDetection.cpp:155-162, 503-535`):* Unless `-polly-ignore-aliasing` is forced, `Polly` enables `PollyUseRuntimeAliasChecks` (`init(true)`, `ScopDetection.cpp:160`), computes parametric minimum and maximum accessed byte addresses `[min_A, max_A)` and `[min_B, max_B)` via `isl` `lexmin`/`lexmax` (`buildMinMaxAccess`), and guards the optimized SCoP on the runtime disjointness predicate `max_A <= min_B || max_B <= min_A`.

3. **Hazard C — Speculative Guard Hoisting and Out-of-Bounds / Trap Introduction:**
   Separating union polyhedra (`separate`) or hoisting invariant loads into `PPCG` cooperative `shared_tile` pre-loads must intersect the copy domain with the exact footprint of *active* domain instances (`group_tile`, `ppcg/gpu.c:881`). Overapproximating a triangular or predicated footprint by its bounding box `[0, tile_size - 1]` causes threads with $t + k \ge N$ to issue out-of-bounds global DRAM reads (triggering `CUDA_ERROR_ILLEGAL_ADDRESS` page faults) unless guarded by the hull of live statement accesses.

## Boundaries

- **Dynamic/Indirect Subscripts (`A[B[i]]`) and Unbounded `while` Loops (`unsupported`):** Exact Presburger dependence analysis in `isl`, `Pluto`, and `PPCG` explicitly does not support data-dependent array subscripts or non-affine loop trip counts. (`LLVM Polly` supports coarse `AllowNonAffineSubRegions` black-box regions for inner branches, `ScopDetection.cpp:183`, by overapproximating writes via `W_may`, which prevents inner tiling across the boxed region.)
- **Strict IEEE 754 Bitwise Equivalence Under Reduction Parallelization (`known not to apply`):** Neither `Pluto`/`PPCG` reduction parallelization nor the TOPLAS 2012 static affine equivalence checker (`DOI: 10.1145/2362389.2362393`) preserves IEEE 754 floating-point rounding order; reordering `sum += A[i]` across tiles or warps alters rounding errors and can turn finite sums into `Inf` or `NaN` when intermediate cancellation order changes.
- **Arbitrary-Precision Protection Inside `Pluto`'s Internal Farkas Eliminator (`known not to apply`):** While `PollyLabs/isl` protects against integer overflow via `gmp`/`imath`/`sioimath`, `bondhugula/pluto`'s native `PlutoConstraints` matrix in `lib/constraints.c` uses fixed 64-bit `int64_t` entries during `farkas_lemma_affine` Fourier–Motzkin projection.
- **CUDA Warp-Synchronous Cooperative Groups and Asynchronous Tensor-Core Barrier Pipelines (`not examined`):** `PPCG` (`5e07c52e13fc8ea9fac7c1daf247d81d60822a93`) models block-wide `__syncthreads()` (`ppcg_kernel_sync`) and global/shared/private memory tiers; Hopper/Blackwell `cp.async.bulk` (`mbarrier` producer-consumer warp specialization) and `wgmma` tensor-core schedules were not examined and are outside `PPCG`'s 3-tier model.
- **Optimal Multi-Level Cache + Register Tile-Size Co-Search (`unknown`):** While `Pluto` (`lib/tile_size_selection_model.cpp`) and `PPCG` (`--sizes`) provide analytical reuse heuristics and manual tile overrides, closed-form optimality of tile sizes jointly coupling register pressure, shared-memory bank conflicts, and L2 residency across arbitrary imperfectly nested SCoPs remains unresolved statically without empirical autotuning.

## Evidence

### Primary Repositories and Source Coordinates

1. **`PollyLabs/isl`** (`revision: b822a2105dfe3c36f5d9c31071e61446bc88c0bc`):
   - `isl_map_private.h:36-113`: `struct isl_basic_map` (`eq`, `ineq`, `div` existential floor-division matrix, `ISL_BASIC_MAP_RATIONAL`, `ISL_BASIC_MAP_NORMALIZED_DIVS`) and `struct isl_map`.
   - `isl_int_sioimath.h:31-115`: 64-bit LSB-tagged small-integer representation over `[-INT32_MAX, INT32_MAX]`, explicit exclusion of `INT32_MIN` at `L89`, and heap `mp_int*` promotion.
   - `isl_ctx.c:51-56, 221-223, 360-378`: deterministic `ctx->max_operations` quota enforcement raising `isl_error_quota`.
   - `isl_tab_pip.c:157-175, 1815-1897, 3872-3910`: parametric dual-simplex PIP solver, `add_cut` parametric Gomory cuts, `restore_lexmin`, and context tableau branching `find_solutions`.
   - `isl_coalesce.c:1-120`: union-of-basic-maps facet and integer-wrapping coalescing.
   - `isl_flow.c:633-665, 1127-1210`: `last_source` and `compute_val_based_dependences` exact Feautrier array dataflow analysis.
   - `isl_schedule_tree.h:54-110` and `isl_scheduler.c:60-145`: explicit `isl_schedule_tree` node union (`band`, `domain`, `filter`, `sequence`, `set`, `guard`, `mark`, `extension`, `expansion`) and `struct isl_sched_node` (`indep`, `vmap`, `coincident`, `compress`).
2. **`bondhugula/pluto`** (`revision: 2b6fd99c976e4fec340cb227c8048bcd40864755`):
   - `include/pluto/pluto.h:30-145`: `FusionType` (`kNoFuse`..`kHybridFuse`) and `struct plutoOptions` (`tile`, `diamondtile`, `fulldiamondtile`, `per_cc_obj`, `hybridcut`).
   - `lib/constraints.c:213-280`: `farkas_lemma_affine` constructing homogeneous Farkas equality/non-negativity constraints with synthetic `1 >= 0` translation row and eliminating $\lambda$ via `fourier_motzkin_eliminate_smart`.
   - `lib/pluto.c:592-615, 698-715, 1138-1250`: `cut_smart` SCC cutting, `EAGER`/`LAZY` orthogonal subspace independence (`orthcst`), and `normalize_domains` global parameter context projection into `bounding_poly`.
   - `lib/tile.c:85-115`: `pluto_diamond_tile_reschedule` (`evicted_hyp` hyperplane swap) and `pluto_tile_band`.
3. **`Meinersbur/ppcg`** (`revision: 5e07c52e13fc8ea9fac7c1daf247d81d60822a93`):
   - `gpu_group.c:71-115`: `gpu_array_ref_group` memory tier selection (`private_tile` vs. `shared_tile` depth priority) and `requires_unroll` constraint.
   - `gpu.c:601-620, 857-975, 2006-2127`: `group_tile` parametric footprint map, `compute_sched_to_copy`, `check_shared_memory_bound`, and `create_sync_leaf` (`ppcg_kernel_sync`).
   - `gpu_tree.c:20-85, 566-610`: `kernel`/`shared`/`thread` schedule-tree mark invariants, `gpu_tree_ensure_sync_after_core`, and `gpu_tree_move_left_to_sync`.
4. **`llvm/Polygeist`** (`revision: 77c04bb2a7a2406ca9480bcc9e729b07d2c8d077`):
   - `lib/polygeist/Passes/RaiseToAffine.cpp:1-90`: raising `scf.for` signed comparisons into MLIR `affine.for`.
   - `lib/polygeist/Passes/BarrierRemovalContinuation.cpp:39-89`: `hasImmediateBarriers`, `wrapPersistingLoopBodies`, and `applyCFGConversion` continuation splitting around `polygeist.barrier`.
   - `tools/polymer/lib/Transforms/PlutoTransform.cc:46-106`: `polymer::plutoTransform` OpenScop + `isl` (`isldep = 1`) + `libpluto` round-trip.
5. **`llvm/llvm-project`** (`revision: d1ee282181f8f83e7552136c344706c0e5400c9a`):
   - `polly/lib/Analysis/ScopDetection.cpp:155-162, 503-535`: `PollyUseRuntimeAliasChecks` and multi-pointer `AliasAnalysis` validation.
   - `polly/lib/CodeGen/IslExprBuilder.cpp:22-165`: `OverflowTrackingChoice`, `setTrackOverflow`, `CreateNSWAdd`/`Sub`/`Mul`, and `polly.overflow.state` runtime overflow flag accumulation.

### Peer-Reviewed Specifications and Papers

- Paul Feautrier, *"Parametric Integer Programming"*, RAIRO - Operations Research 22(3), pp. 243–268, 1988 (`DOI: 10.1051/ro/1988220302431`).
- Paul Feautrier, *"Dataflow Analysis of Array and Scalar References"*, International Journal of Parallel Programming 20(1), pp. 23–53, 1991 (`DOI: 10.1007/BF01407931`).
- Cédric Bastoul, *"Code Generation in the Polyhedral Model Is Easier Than You Think"*, PACT 2004, pp. 7–16 (`DOI: 10.1109/PACT.2004.1342537`).
- Uday Bondhugula, Albert Hartono, J. Ramanujam, and P. Sadayappan, *"A Practical Automatic Polyhedral Parallelizer and Locality Optimizer"*, PLDI 2008, pp. 101–113 (`DOI: 10.1145/1375581.1375595`).
- Sven Verdoolaege, *"isl: An Integer Set Library for the Polyhedral Model"*, ICMS 2010, LNCS 6327, pp. 299–302 (`DOI: 10.1007/978-3-642-15582-6_49`).
- Sven Verdoolaege, Gerda Janssens, and Maurice Bruynooghe, *"Equivalence Checking of Static Affine Programs Using Widening to Handle Recurrences"*, ACM TOPLAS 34(3), Article 11, 2012 (`DOI: 10.1145/2362389.2362393`).
- Tobias Grosser, Armin Größlinger, and Christian Lengauer, *"Polly — Performing Polyhedral Optimizations on a Low-Level Intermediate Representation"*, Parallel Processing Letters 22(4), 2012 (`DOI: 10.1142/S0129626412500107`).
- Sven Verdoolaege, Juan Carlos Juega, Albert Cohen, José Ignacio Gómez, Christian Tenllado, and Francky Catthoor, *"Polyhedral Parallel Code Generation for CUDA"*, ACM TACO 9(4), Article 54, 2013 (`DOI: 10.1145/2400682.2400713`).
- Tobias Grosser, Sven Verdoolaege, and Albert Cohen, *"Polyhedral AST Generation Is More Than Scanning Polyhedra"*, ACM TOPLAS 37(4), Article 12, 2015 (`DOI: 10.1145/2743016`).
- William S. Moses, Lorenzo Chelini, Ruizhe Zhao, and Oleksandr Zinenko, *"Polygeist: Raising C to Polyhedral MLIR"*, PACT 2021, pp. 45–59 (`DOI: 10.1109/PACT52795.2021.00011`).

### Executable Probe 1: Farkas Permutability, Diamond-Tile Concurrent Startup, and $\mathbb{Q}$-vs-$\mathbb{Z}$ Parity Emptiness

Executed on Linux (`Python 3.13`, standard library `fractions` and `ctypes` only; observed `2026-11-19`):

```bash
python3 - <<'EOF'
from fractions import Fraction
import ctypes

deps = [(1, -1), (1, 0), (1, 1)]

def check_band(name, H):
    deltas = [[h[0]*d[0] + h[1]*d[1] for d in deps] for h in H]
    permutable = all(v >= 0 for row in deltas for v in row)
    w_t, w_i = sum(h[0] for h in H), sum(h[1] for h in H)
    concurrent_space = permutable and (w_t > 0) and (w_i == 0)
    print(f"{name}: H={H} -> dep_deltas={deltas}, permutable={permutable}, "
          f"tile_wavefront=({w_t},{w_i}), concurrent_space_start={concurrent_space}")

check_band("unskewed_rect", [(1, 0), (0, 1)])
check_band("pluto_skewed_wavefront", [(1, 0), (1, 1)])
check_band("pluto_diamond_tile", [(1, -1), (1, 1)])

T, N, B = 12, 18, 4
def run_seq():
    A = [[Fraction((i * 7 + 3) % 19, 1) for i in range(N)] for _ in range(2)]
    for t in range(T):
        for i in range(1, N - 1):
            A[(t + 1) % 2][i] = (A[t % 2][i - 1] + A[t % 2][i] + A[t % 2][i + 1]) / 3
    return A[T % 2][1:N-1]

def run_diamond_tiled():
    A = [[Fraction((i * 7 + 3) % 19, 1) for i in range(N)] for _ in range(2)]
    pts = [(t, i) for t in range(T) for i in range(1, N - 1)]
    sched_key = lambda pt: ((pt[0]-pt[1])//B + (pt[0]+pt[1])//B, (pt[0]-pt[1])//B, pt[0]-pt[1], pt[0]+pt[1])
    by_step = {}
    for pt in pts:
        k = sched_key(pt)
        by_step.setdefault(k[0], {}).setdefault(k[1], []).append(pt)
    violations = 0
    for w, tiles in by_step.items():
        tile_sets = {tau1: set(p_list) for tau1, p_list in tiles.items()}
        for tau1, p_list in tiles.items():
            for (t, i) in p_list:
                for dt, di in deps:
                    for other_tau1, other_set in tile_sets.items():
                        if other_tau1 != tau1 and (t + dt, i + di) in other_set:
                            violations += 1
    for t, i in sorted(pts, key=sched_key):
        A[(t + 1) % 2][i] = (A[t % 2][i - 1] + A[t % 2][i] + A[t % 2][i + 1]) / 3
    return A[T % 2][1:N-1], violations

ref = run_seq()
got, violations = run_diamond_tiled()
print(f"diamond_equivalence={ref == got}, same_wavefront_cross_tile_deps={violations}")

int_sols = [(i, j) for i in range(8) for j in range(8) if 2 * i == 2 * j + 1]
rat_sol = (Fraction(1, 2), Fraction(0, 1))
print(f"parity_dep: rational_witness={rat_sol} (2*i==2*j+1: {2*rat_sol[0] == 2*rat_sol[1]+1}), integer_solutions={len(int_sols)}")

N32 = (1 << 30) + 2
print(f"bv32_skew_hazard: N={N32}, max_orig_iv={N32-1}, skewed_ub_Z={2*(N32-1)}, wrapped_i32={ctypes.c_int32(2*(N32-1)).value}")
EOF
```

Recorded output:

```text
unskewed_rect: H=[(1, 0), (0, 1)] -> dep_deltas=[[1, 1, 1], [-1, 0, 1]], permutable=False, tile_wavefront=(1,1), concurrent_space_start=False
pluto_skewed_wavefront: H=[(1, 0), (1, 1)] -> dep_deltas=[[1, 1, 1], [0, 1, 2]], permutable=True, tile_wavefront=(2,1), concurrent_space_start=False
pluto_diamond_tile: H=[(1, -1), (1, 1)] -> dep_deltas=[[2, 1, 0], [0, 1, 2]], permutable=True, tile_wavefront=(2,0), concurrent_space_start=True
diamond_equivalence=True, same_wavefront_cross_tile_deps=0
parity_dep: rational_witness=(Fraction(1, 2), Fraction(0, 1)) (2*i==2*j+1: True), integer_solutions=0
bv32_skew_hazard: N=1073741826, max_orig_iv=1073741825, skewed_ub_Z=2147483650, wrapped_i32=-2147483646
```

### Executable Probe 2: Compiled C Counterexample for Unchecked Pointer Aliasing and 32-Bit Skewed Bound Wraparound

Executed with `gcc -O2` on Linux x86_64 (`observed_at: 2026-11-19`):

```bash
cat <<'EOF' > /tmp/probe_polyhedral_c.c
#include <stdio.h>
#include <stdint.h>

static void step_sequential(int *A, const int *B, int N) {
    for (int i = 1; i < N; i++) A[i] = B[i - 1] + 1;
}

static void step_tile_promoted_no_rtc(int *A, const int *B, int N) {
    int shared_B[8];
    for (int t = 0; t < N; t += 8) {
        for (int k = 0; k < 8 && (t + k) < N; k++) shared_B[k] = B[t + k];
        for (int k = 0; k < 8 && (t + k) < N; k++) {
            int i = t + k;
            if (i >= 1) A[i] = ((k > 0) ? shared_B[k - 1] : B[i - 1]) + 1;
        }
    }
}

int main(void) {
    int buf_seq[8] = {10, 0, 0, 0, 0, 0, 0, 0};
    int buf_opt[8] = {10, 0, 0, 0, 0, 0, 0, 0};
    step_sequential(buf_seq, buf_seq, 8);
    step_tile_promoted_no_rtc(buf_opt, buf_opt, 8);
    printf("aliased_seq[7]=%d aliased_tile_no_rtc[7]=%d mismatch=%d\n",
           buf_seq[7], buf_opt[7], buf_seq[7] != buf_opt[7]);

    int32_t N = (1 << 30) + 2;
    int32_t s_ub_wrapped = (int32_t)(2u * (uint32_t)(N - 1));
    int64_t s_ub_widened = 2LL * (int64_t)(N - 1);
    printf("skew_bound: N=%d i32_wrapped=%d i64_widened=%lld\n",
           N, s_ub_wrapped, (long long)s_ub_widened);
    return 0;
}
EOF
gcc -O2 /tmp/probe_polyhedral_c.c -o /tmp/probe_polyhedral_c && /tmp/probe_polyhedral_c
```

Recorded output:

```text
aliased_seq[7]=17 aliased_tile_no_rtc[7]=1 mismatch=1
skew_bound: N=1073741826 i32_wrapped=-2147483646 i64_widened=2147483650
```

## Revalidation

To cheaply revalidate these findings when upgrading `isl`, `Pluto`, `PPCG`, `Polygeist`, or `LLVM Polly`:

1. **`isl` Small-Integer & Quota Invariants:** Diff `isl_int_sioimath.h` around `ISL_SIOIMATH_SMALL_MIN` (`-INT32_MAX`) and `isl_ctx.c` around `ctx->max_operations`. Verify `struct isl_basic_map` in `isl_map_private.h` retains explicit `div` floor-division matrices and `isl_tab_pip.c` retains `add_cut` Gomory cuts.
2. **`Pluto` Farkas Linearization & Fixed-Width Constraints:** Diff `lib/constraints.c` (`farkas_lemma_affine`) and `lib/pluto.c` (`normalize_domains`) to check whether `PlutoConstraints` has migrated from `int64_t` to arbitrary-precision `isl_int`/`mpz_t` or altered global parameter context injection.
3. **`PPCG` Promotion Priority & Barrier Uniformity:** Diff `gpu_group.c` (`gpu_array_ref_group_type`) and `gpu_tree.c` (`gpu_tree_move_left_to_sync`, `gpu_tree_ensure_sync_after_core`) to confirm `private` still wins ties against `shared` at equal schedule depth and `sync` filter nodes remain outside `mark("thread")` subtrees.
4. **IR Lowering Soundness Guards:** Rerun Executable Probes 1 and 2 above (< 1 second total) and inspect `polly/lib/CodeGen/IslExprBuilder.cpp` (`OverflowState`) and `polly/lib/Analysis/ScopDetection.cpp` (`PollyUseRuntimeAliasChecks`) to confirm runtime overflow and alias checks remain enabled by default.
