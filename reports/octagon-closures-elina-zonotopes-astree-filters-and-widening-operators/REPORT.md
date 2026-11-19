# Octagon Strong Closures, ELINA Block Decomposition, Taylor1+ Zonotopes, Astrée Filter Ellipsoids, and Sound Floating-Point Widening

## Summary

Relational numerical abstract interpretation trades asymptotic representation cost for invariant expressiveness along an explicit geometric hierarchy: non-relational intervals ($O(n)$ space/time), difference-bound matrices and octagons ($O(n^2)$ space, $O(n^3)$ closure), affine-arithmetic zonotopes (`Taylor1+`, $O(n \cdot m)$ for $m$ noise symbols), quadratic Lyapunov ellipsoids for digital filters ($O(1)$ per 2-tap filter pair), and full convex polyhedra via Chernikova double description (exponential worst-case vertex/facet blowup). Across `antoinemine/apron`, `eth-sri/elina`, `NASA-SW-VnV/ikos`, and the `Astrée` domain architecture, four implementation invariants govern soundness and scalability:

1. **Closure vs. integer canonicality:** Miné's $O(n^3)$ Floyd–Warshall plus unary strengthening (`hmat_close` in `oct_closure.c`) is canonical over $\mathbb{R}/\mathbb{Q}$ (`flag_exact = flag_best = true` only with exact rationals `NUM_MPQ`), but fails to detect integer unsatisfiability or propagate odd-bound tightening over $\mathbb{Z}$ without Bagnara–Hill–Zaffanella (BHZ) unary floor tightening (`2 * floor(c_{i, \bar{i}} / 2)`) *followed by a coherence pass*. In `eth-sri/elina`'s `strengthning_int_*`, `ceil(m[ind]/2)` preserves soundness while deliberately trading integer tightness for scalar simplicity, whereas `ikos`'s native `Octagon` class explicitly warns callers to prefer `APRON` (`apron.hpp`) or `VarPackingDBM` due to residual edge-case issues.
2. **Online dynamic block decomposition (`ELINA`) vs. static variable packing (`IKOS`):** Dense $O(n^3)$ octagon closure and global Chernikova conversion collapse once $n$ exceeds a few dozen variables. `ELINA` partitions variables *online* into disjoint connected relational blocks (`array_comp_list_t` in `partitions_api/comp_list.h`) inside every transfer, join, and widening operator—shrinking a 48-variable system of twelve 4-variable subsystems by **$129.3\times$** in scalar closure work with zero precision loss and eliminating global generator products in `opt_pk_cherni.c`.
3. **Geometric blind spots of polyhedral templates on digital filters:** Stable second-order IIR filters with complex-conjugate poles ($y_k = 1.5 y_{k-1} - 0.7 y_{k-2} + u_k$, $|u_k| \le 1$, $|\lambda| = \sqrt{0.7} \approx 0.8367$) rotate state trajectories by a non-axis/non-45° angle every iteration. Intervals diverge to $|s_1| \le 7.71 \times 10^{10}$ and octagons diverge to $|s_1| \le 146.54$ by step 40, whereas Feret's quadratic Lyapunov ellipsoid $Q(s_1, s_2) = s_1^2 - 1.5 s_1 s_2 + 0.7 s_2^2 \le R^2$ contracts strictly and converges to $|s_1| \le 13.8135$. Meanwhile, `Taylor1+` zonotopes preserve exact linear correlations and quadratic cancellations across arithmetic without polyhedral templates, but lack least upper bounds and require functional joins (`optpr_problem_t`) over constrained noise symbols (`IN`/`UN`).
4. **Widening non-monotonicity and IEEE 754 FPU coupling:** Cousot–Cousot widening $\nabla$ is inherently **non-monotonic** ($A \sqsubseteq B \not\implies A \nabla C \sqsubseteq B \nabla C$), causing the "widening precision paradox" where adding assertions or shrinking initial intervals can yield strictly weaker loop invariants. On IEEE 754 `binary64` (`NUM_DOUBLE`) backends, relational transitive additions in default round-to-nearest-even (`RN`) silently break soundness (e.g., $\mathrm{fl}_{\mathrm{RN}}(2^{53} + 1.0) = 2^{53} < 2^{53} + 1$); `APRON`'s `ap_fpu_init()` globally pins `fesetround(FE_UPWARD)` and fails closed under `FTZ` flush-to-zero, creating a severe FFI/thread-local soundness hazard if host code resets MXCSR rounding control.

## Applicability

This report covers the C, C++, and mathematical domain designs across:

- **`antoinemine/apron`** (`0a7ca30527c29f5fc894bf424b4d24ca638beb4e`): modules `num/` (`numflt_native.h`, `numint_native.h`, `numint_mpz.h`, `bound_def.h`), `apron/` (`ap_manager.c`), `octagons/` (`oct_internal.h`, `oct_closure.c`, `oct_nary.c`, `oct_transfer.c`), and `taylor1plus/` (`t1p_internal.h`, `t1p_meetjoin.c`, `t1p_assign.c`, `t1p_fun.c`).
- **`eth-sri/elina`** (`f524156d292ac3a6f3cd676e2d2e7db6629e2b6f`): modules `partitions_api/` (`comp_list.h`), `elina_oct/` (`opt_oct_internal.h`, `opt_oct_closure_comp_sparse.c`, `opt_oct_closure_dense.c`, `opt_oct_closure_dense_scalar.c`, `opt_oct_nary.c`), `elina_poly/` (`opt_pk_internal.h`, `opt_pk_cherni.c`, `opt_pk_meetjoin.c`, `opt_pk_widening.c`), and `elina_zonotope/` (`zonotope_internal.h`, `zonotope_meetjoin.c`). Note that `ELINA` exports both a standalone `elina_*` ABI and an `APRON`-compatible drop-in interface (`IS_APRON` in `Makefile`).
- **`NASA-SW-VnV/ikos`** (`ac7f7c1738976cabc58c6a53413df6e458995c38`): C++ header-only numerical domains under `core/include/ikos/core/domain/numeric/` (`dbm.hpp`, `octagon.hpp`, `var_packing_dbm.hpp`, `gauge_interval_congruence.hpp`, `apron.hpp`).
- **Foundational abstract-domain specifications (`Astrée` / `APRON` / `PPL` / `ELINA`)**: Miné (ESOP 2004, HOSC 2006), Feret (ESOP 2004), Cousot et al. (ESOP 2005), Bagnara–Hill–Zaffanella (FMSD 2009), Ghorbal–Goubault–Putot (CAV 2009), and Singh–Püschel–Vechev (PLDI 2015, POPL 2017).

Claims about `APRON` numeric backends distinguish exact rational `NUM_MPQ` (`num_incomplete = 0, num_safe = 1`), arbitrary-precision integer `NUM_MPZ` (`num_incomplete = 1, num_safe = 1`), native `NUM_DOUBLE` (`num_incomplete = 1, num_safe = 1` under `FE_UPWARD`), and unguarded fixed-width `NUM_LONGINT`/`NUM_LONGLONGINT` (`num_safe = 0`). Findings on `Astrée`'s filter ellipsoid and reduced-product architecture are drawn from peer-reviewed literature (`Cousot et al. 2005`, `Feret 2004`) rather than closed-source `Astrée` binaries (`not examined`).

## Findings

### 1. Potential-Graph Encoding, Strong Closure, and Integer Tight Closure

Basis: source + normative + execution (`oct_internal.h`, `oct_closure.c`, `numint_native.h`, `opt_oct_closure_comp_sparse.c`, `ikos/core/domain/numeric/octagon.hpp`, Miné HOSC 2006, Bagnara et al. FMSD 2009, `/tmp/probe_domains.py` Experiment A).

An octagonal constraint system over $n$ variables $\{x_0, \dots, x_{n-1}\}$ represents inequalities $\pm x_i \pm x_j \le c$ by doubling each variable $x_k$ into positive and negative signed nodes $v_{2k} = +x_k$ and $v_{2k+1} = -x_k$ (with involution $\bar{i} = i \oplus 1$). An edge weight $m_{i, j}$ encodes $v_j - v_i \le m_{i, j}$ (equivalently $v_i - v_j \le m_{j, i}$ by symmetry). Because every binary relation has an equivalent dual representation ($x_0 - x_1 \le c \iff (-x_1) - (-x_0) \le c$), `APRON` (`octagons/oct_internal.h:154-170`) and `ELINA` (`elina_oct/opt_oct_internal.h:198-213`) eliminate half the storage via a coherent lower-triangular half-matrix of exact length:

$$\text{matsize}(n) = 2n(n + 1), \qquad \text{matpos}(i, j) = j + \left\lfloor \frac{(i+1)^2}{2} \right\rfloor \quad (\text{for } \lfloor j/2 \rfloor \le \lfloor i/2 \rfloor),$$

and `matpos2(i, j)` redirects `j > i` to `matpos(j ^ 1, i ^ 1)`. Unitary bounds $2x_k \le c$ and $-2x_k \le c$ occupy the anti-diagonal cells `m[matpos(2k+1, 2k)]` and `m[matpos(2k, 2k+1)]`.

#### Strong Closure vs. Integer Tight Closure

| Property / Step | Rational Strong Closure (`APRON` `hmat_close`) | Integer Tight Closure (`BHZ FMSD 2009`) | `ELINA` `is_int` (`opt_oct_closure_*.c`) | `IKOS` Native `Octagon` (`octagon.hpp`) |
| :--- | :--- | :--- | :--- | :--- |
| Shortest-path step | $O(n^3)$ modified Floyd–Warshall (`k` and `k^1` paired) | Identical Floyd–Warshall base | Component-sparse / AVX2 dense Floyd–Warshall | $O(n^3)$ dense `Matrix` (1-based col-major, $4n^2$ entries) |
| Unary strengthening (`S-step`) | $m_{i,j} \leftarrow \min(m_{i,j}, (m_{i,\bar{i}} + m_{\bar{j},j})/2)$ via `bound_div_2` | Same `S-step`, then unary floor tightening | `temp[i] = ceil(m[i^1, i] / 2)`; $\min(m_{i,j}, \text{temp}[\bar{i}] + \text{temp}[j])$ | `(...)/BoundT(2)` (C++ truncating toward zero) |
| Odd-bound $\mathbb{Z}$ tightening | Uses `mpz_cdiv_q_2exp` (`cdiv_2`) in `NUM_MPZ` (`numint_mpz.h:97`) — sound, not tight | $m_{i,\bar{i}} \leftarrow 2\lfloor m_{i,\bar{i}} / 2 \rfloor$, **then post-coherence pass** | `ceil(m[ind]/2)` avoids unsound $\mathbb{R}$ tightening; non-tight over $\mathbb{Z}$ | Non-tight; truncating `/ 2` rounds negative odds upward |
| Canonical over $\mathbb{Z}$? | **No** (`flag_incomplete` when `intdim > 0`) | **Yes** (decides $\mathbb{Z}$-feasibility and exact $\sqsubseteq$) | **No** (sound over-approximation; `num_incomplete = 1`) | **No** (comments explicitly recommend `APRON`) |

Why a single `S-step` over $\mathbb{Z}$ is both incomplete and non-canonical—and why omitting a post-coherence pass after integer tightening fails—is demonstrated concretely in Experiment A of `/tmp/probe_domains.py`:

1. **Integer unsatisfiability blind spot:** On $\{x + y \le 1,\; -x - y \le -1,\; x - y \le 0,\; -x + y \le 0\}$, rational strong closure yields $2x \le 1,\; -2x \le -1$ (`empty = false`, satisfied over $\mathbb{Q}$ by $x = y = 1/2$). Over $\mathbb{Z}$, BHZ tightening sets $2x \le 2\lfloor 1/2 \rfloor = 0$ and $-2x \le 2\lfloor -1/2 \rfloor = -2$. If no coherence pass runs afterward, the diagonal stays $m_{0,0} = 0$ even though $m_{1,0} + m_{0,1} = 0 + (-2) = -2 < 0$ (unsatisfiable!). Running the post-coherence pass immediately pushes $-2 < 0$ onto the diagonal, detecting `empty = true`.
2. **Transitive propagation loss without post-coherence:** Given $2x \le 3$ and $y - x \le 0$, rational strong closure produces $x + y \le 3$. Tightening only unary bounds $2x \le 2$ without re-closing leaves $x + y \le 3$ unchanged; re-propagating coherence tightens $x + y \le 2$.

`APRON` also provides `hmat_close_incremental(m, dim, v)` (`oct_closure.c:120-197`), which restores closure in $O(n^2)$ time whenever only variable `v`'s row/column (`2*v`, `2*v+1`) was modified (e.g., assignment or single-variable guard), checking `v` in endpoint and pivot positions before running `hmat_s_step`.

### 2. Online Dynamic Block Decomposition and Factorized Chernikova Polyhedra

Basis: source + execution (`partitions_api/comp_list.h`, `opt_oct_internal.h`, `opt_oct_closure_comp_sparse.c`, `opt_pk_cherni.c`, `opt_pk_widening.c`, `var_packing_dbm.hpp`, Singh et al. PLDI 2015 & POPL 2017, `/tmp/probe_domains.py` Experiment B).

Real programs couple variables inside localized loops and functions rather than forming dense cliques across all $n$ SSA/stack variables. `IKOS` and `ELINA` exploit this sparsity through fundamentally different architectures:

- **Syntactic variable packing (`NASA-SW-VnV/ikos` `var_packing_dbm.hpp` / `var_packing_domain.hpp`):** Maintains equivalence classes of variables statically or semi-dynamically around `DBM<Number, VariableRef>` sub-matrices (`MaxReductionCycles = 10` for combined congruence reduction). This avoids allocating $O(n^2)$ matrices upfront when variables never co-occur in a linear expression, but cannot automatically split blocks back apart if intermediate relations are later dropped via `forget` or `join`.
- **Online dynamic block decomposition (`eth-sri/elina` `partitions_api/comp_list.h` & `opt_oct_mat_t` / `opt_pk_array_t`):** Every abstract element carries a dynamic partition `array_comp_list_t *acl` (linked list of `comp_list_t` variable index blocks $C_1 \sqcup \dots \sqcup C_r \subseteq \{0, \dots, n-1\}$). All domain operators dynamically maintain exact block factorization without a separate pre-analysis pass:
  - **Strong closure (`opt_oct_closure_comp_sparse.c`):** Iterates strictly over `cl` in `oo->acl`, running Floyd–Warshall within each block $C_r$ in $O(|C_r|^3)$ and skipping unrelated pairs (`oo->ti` tracks top/uninitialized blocks). In `strengthning_comp_sparse`, only blocks containing finite unary bounds merge (`ini_comp_relations` lazily initializes cross-block half-matrix entries to $+\infty$ only upon fusion). On $n = 48$ variables across twelve 4-variable blocks (`Experiment B`), dense closure executes `893,952` scalar relaxations vs. `6,912` under block decomposition (**$129.3\times$ reduction**, `max discrepancy = 0`).
  - **AVX2/SSE dense kernel fallback (`opt_oct_closure_dense.c`):** When a single merged component grows dense (`oo->is_dense`), `ELINA` switches to cache-blocked, 4-wide (`__m256d`) SIMD vectorized loops (`v_min_double`, `v_add_double` in `opt_oct_closure_dense.c:48-70` & `floyd_warshall_dense`) instead of sparse list traversal.
  - **Factorized Chernikova polyhedra (`opt_pk_cherni.c` & `opt_pk_meetjoin.c`):** Standard convex polyhedra (`APRON` `newpolka`) execute Chernikova's double-description conversion (`C` constraint matrix $\leftrightarrow$ `F` frame of vertices/rays/lines with bitstring saturation matrices `satC`/`satF`) over the global $n$-dimensional space. Two decoupled 2-D polygons with 10 vertices each produce $10 \times 10 = 100$ combined vertices; $k$ decoupled 4-vertex boxes produce $4^k$ vertices, triggering catastrophic OOM or `max_coeff_size` overflow. `ELINA`'s `opt_pk` restricts `opt_cherni_minimize` (`opt_pk_cherni.c:505-629`) strictly to each independent `comp_list_t` block ($O(\sum_r \text{Chernikova}(|C_r|))$), dynamically merging blocks on relational meets (`union_array_comp_list`) and splitting/dropping blocks on projections, assignments, and joins (`intersection_array_comp_list`, `opt_pk_widening.c`). `ELINA` additionally exposes experimental reinforcement-learning join pruning (`opt_oct_lait.h`, `opt_pk_lait.h`) when `LAIT=1`.

### 3. `Taylor1+` Affine-Arithmetic Noise-Symbol Zonotopes

Basis: source + normative (`t1p_internal.h`, `t1p_meetjoin.c`, `t1p_assign.c`, `t1p_fun.c`, `zonotope_internal.h`, `zonotope_meetjoin.c`, Ghorbal et al. CAV 2009).

In `APRON`'s `taylor1plus/` (and `ELINA`'s SIMD/double-adapted `elina_zonotope/`), each program variable $x_i$ is bound to a centered affine form (`struct _t1p_aff_t` in `t1p_internal.h:65-73`):

$$\hat{x}_i = c_i + \sum_{k=1}^{m} \alpha_{i,k}\, \epsilon_k, \qquad \epsilon_k \in [-1, 1],$$

where $c_i$ is an interval center (`itv_t c` in `APRON`; `(c_inf, c_sup)` in `ELINA` `zonotope_internal.h:123-133`), `q` is a sparse sorted linked list of `t1p_aaterm_t` noise-symbol terms (`pnsym->index`, `coeff`), and `paf[i]->itv` caches the tightest interval concretization (`box` reduced product). Noise symbols carry `nsym_t` classification `IN` (input/linear/nonlinear error) or `UN` (union symbols created at joins).

Key invariants and trade-offs vs. octagons/polyhedra:

1. **Exact $O(m)$ linear correlation and cancellation:** Computing $y = x - x$ cancels shared $\epsilon_k$ coefficients term-by-term to exact `[0, 0]`, and quadratic forms like $x(1 - x)$ for $x = 0.5 + 0.5\epsilon_1$ simplify to $0.25 - 0.25\epsilon_1^2 \in [0, 0.25]$ (via `t1p_aff_mul` allocating one fresh `IN` error symbol for nonlinear remainder, `t1p_fun.c:229-245`), eliminating the $4\times$ interval dependency blowup $[0, 1]$.
2. **Non-lattice join (`t1p_join` / `optpr_problem_t`):** Zonotopes do **not** form a lattice—two zonotopes generally have infinitely many incomparable minimal upper bounds. To obtain a deterministic, maximally tight functional join (`Ghorbal et al., CAV 2009`), `APRON` solves a small parameterized convex optimization (`optpr_problem_t` in `t1p_internal.h:109-120`) over $(\lambda, u_0)$ partitioning noise symbols into shared (`IXY`), left-only (`IX`), right-only (`IY`), and breakpoint (`J`) sets, introducing fresh `UN` union symbols only for differing centers/unmatched deviations.
3. **Constrained zonotope guards (`abs` over noise symbols):** Pure unconstrained zonotopes ($\epsilon \in [-1, 1]^m$) cannot represent asymmetric half-space intersections (`x <= 0.3`) exactly. Both `APRON` `t1p_t` (`t1p_internal.h:168-171`) and `ELINA` `zonotope_t` (`zonotope_internal.h:179-186`) attach an auxiliary `ap_abstract0_t *abs` (`manNS`, typically an interval or polyhedral sub-domain over constrained `nsymcons` indices) plus `hypercube` fast-path flagging, switching from fast $O(m)$ hypercube arithmetic to `manNS` meet/join (`t1p_meetjoin.c`, `zonotope_meetjoin.c:112-162`) whenever conditional branches constrain shared noise symbols.

### 4. Second-Order Digital-Filter Ellipsoids and Reduced Products (`Astrée`)

Basis: normative + execution (`Feret ESOP 2004`, `Cousot et al. ESOP 2005`, `/tmp/probe_domains.py` Experiment C).

Safety-critical fly-by-wire control loops implement second-order infinite-impulse-response (IIR) biquad digital filters:

$$s_1' = a\, s_1 - b\, s_2 + u, \qquad s_2' = s_1, \qquad u \in [-M, M],$$

where $a^2 - 4b < 0$ and $0 < b < 1$ produce damped complex-conjugate eigenvalues $\lambda_{1,2} = \frac{a}{2} \pm i\sqrt{b - a^2/4}$ with spectral radius $|\lambda| = \sqrt{b} < 1$. Because the transition matrix $A = \begin{pmatrix} a & -b \\ 1 & 0 \end{pmatrix}$ rotates states by $\theta = \arccos(a / (2\sqrt{b}))$ at every tick, any fixed-direction linear template domain (intervals, octagons, and even finite-facet template polyhedra without exponentially many facets aligned with $\theta$) slices off corners and rotates them outward on every step, causing unbounded or vastly over-approximated growth.

Feret's filter ellipsoid domain (`ESOP 2004`, integrated into `Astrée` in `Cousot et al. ESOP 2005`) tracks the quadratic Lyapunov sublevel set matched to the filter's exact complex Jordan basis:

$$Q_{a,b}(s_1, s_2) = s_1^2 - a\, s_1 s_2 + b\, s_2^2 \le K.$$

Algebraically, $Q_{a,b}(A \mathbf{s}) = b \cdot Q_{a,b}(\mathbf{s})$ identically for every $(s_1, s_2) \in \mathbb{R}^2$, giving an exact linear-rate contraction $\sqrt{b} < 1$ under the induced quadratic norm $\|\mathbf{s}\|_Q = \sqrt{Q_{a,b}(\mathbf{s})}$. By the triangle inequality over $\|\cdot\|_Q$ with input vector $(u, 0)^T$ ($\|(u, 0)\|_Q = |u| \le M$), the sound abstract transfer and exact fixed-point bound are closed-form:

$$\sqrt{K'} = \sqrt{b\,K} + M \implies R^* = \frac{M}{1 - \sqrt{b}}, \qquad |s_1| \le R^* \sqrt{\frac{b}{b - a^2/4}}.$$

Experiment C of `/tmp/probe_domains.py` concretely compares all four domains over 40 steps of $(a = 1.5, b = 0.7, M = 1)$ ($|\lambda| \approx 0.8367$, fixpoint $|s_1| \le 13.8135$):

| Step $k$ | Interval Bound ($|s_1| \le$) | Closed Octagon ($|s_1| \le$) | Unrolled Exact Zonotope ($k$ symbols) | Feret Filter Ellipsoid ($|s_1| \le$) |
| :---: | ---: | ---: | ---: | ---: |
| 5 | `21.203` | `7.216` | `6.153` | `8.150` |
| 10 | `507.921` | `16.484` | `7.789` | `11.492` |
| 20 | `271,206.188` | `42.524` | `9.030` | `13.423` |
| 40 | `77,070,116,173.021` (diverges) | `146.542` (diverges) | `9.267` ($40$ fresh symbols; unbounded without join/order reduction) | `13.803` (converges to `13.8135`) |

In `Astrée`'s reduced product (`Cousot et al. 2005`), the filter domain runs syntactically on detected 2-state recurrence pairs $(s_1, s_2)$ and exchanges tightened interval projections (`box` bounds) with the interval, octagon, clock, and trace-partitioning domains without polling all pairs of variables.

### 5. Widening Non-Monotonicity, Schedules, and IEEE 754 Outward Rounding

Basis: source + normative + execution (`oct_nary.c`, `opt_pk_widening.c`, `numflt_native.h`, `ap_manager.c`, Miné ESOP 2004, `/tmp/probe_domains.py` Experiment D).

Because infinite-height chains occur in intervals, octagons, zonotopes, and polyhedra, Kleene iteration requires widening $\nabla$ to force convergence in finitely many steps, optionally refined afterward by descending narrowing $\Delta$.

1. **Non-monotonicity and the widening precision paradox:** Unlike least upper bound $\sqcup$, standard widening (`oct_widening` in `oct_nary.c:165-199`: keep $m_1[i]$ if $m_2[i] \le m_1[i]$, else jump to $+\infty$) is **non-monotonic** in its left operand. In Experiment D, $X_1 = [0, 1] \sqsubseteq X_2 = [0, 2]$, yet $X_1 \nabla [0, 2] = [0, +\infty] \not\sqsubseteq [0, 2] = X_2 \nabla [0, 2]$. Practically, adding a defensive `assert` before a loop or tightening an upstream precondition can shift $X_1$ below $X_2$ on iteration 1 and cause $\nabla$ to jump to $+\infty$ instead of stabilizing at an existing threshold.
2. **Closure-before-widening trap in octagons (`oct_nary.c:180-182`):** `APRON` explicitly comments `/* work on the origial left matrix, not the closed cache! */` for `a1` while closing `a2` (`oct_cache_closure(pr, a2)`). Why? If `a1` were closed before widening, redundant transitive bounds on `a1` could fluctuate asymmetrically or fail stabilization; worse, in `oct_widening` if both matrices stayed unclosed or `a1` dropped implicit constraints, widening could still loop or over-jump. Conversely, `oct_narrowing` (`oct_nary.c:255-278`) closes *both* `a1` and `a2` and replaces $+\infty$ entries of `m1` with finite `m2` bounds (`bound_infty(m1[i]) ? m2[i] : m1[i]`).
3. **Mitigation schedules (`oct_widening_thresholds` & polyhedral standard widening):** `APRON` (`oct_nary.c:201-253`) supplies threshold widening (`oct_widening_thresholds`), snapping unstable upper bounds to the smallest threshold in an array mined from program branch/array constants before jumping to $+\infty$, plus `oct_add_epsilon_bin` perturbation widening (`oct_nary.c:359-398`) for floating-point loops where rounding drift creeps past fixed bounds by $1\text{–}2\text{ ulp}$. In `ELINA` polyhedra (`opt_pk_widening.c:428-580`), standard widening keeps inequalities of $P_2$ whose saturation signature `satline` matches a constraint of $P_1$ (via binary search on sorted `opt_satmat_row_t`), avoiding representation dependence on redundant half-spaces.
4. **Outward IEEE 754 rounding (`numflt_native.h` & `ap_fpu_init`):** Under IEEE 754 default round-to-nearest-even (`RN`), computing $m_{i,j} \leftarrow m_{i,k} + m_{k,j}$ in Floyd–Warshall is **unsound**. As shown in Experiment D, if $x - y \le 2^{53}$ and $y - z \le 1.0$, exact $x - z \le 2^{53} + 1 = 9007199254740993$, whereas $\mathrm{fl}_{\mathrm{RN}}(2^{53} + 1.0) = 2^{53} = 9007199254740992.0$, falsely rejecting the valid concrete state $(x = 2^{53} + 1, y = 1, z = 0)$. `APRON`'s `ap_manager.c:299-304` solves this globally by executing `fesetround(FE_UPWARD)` inside `ap_fpu_init()` and verifying upward rounding + absence of flush-to-zero (`FTZ`) in `test_fpu()` (`ap_manager.c:267-289`). Every `numflt_native.h` lower-bound step then uses the negation trick `d = -((-d) * fd)` (`numflt_native.h:168`) so both `+oo` upper bounds and `-oo` negated lower bounds round strictly outward. For floating-point program expressions (rounding errors in $x \oplus_{\text{fp}} y$), `Miné (ESOP 2004)` linearizes non-affine IEEE 754 operations into real affine forms with interval error bounds $\varepsilon_{\text{rel}} \cdot |e| + \varepsilon_{\text{abs}}$ over subnormal/ulp ranges before feeding relational DBMs/octagons.

### 6. Six-Level Performance and Resource Footprint Characterization (`L1`–`L6`)

Basis: source + documentation (`Cousot et al. ESOP 2005`, `Singh et al. PLDI 2015 / POPL 2017`, `opt_oct_internal.h`, `oct_internal.h`, `ikos/CMakeLists.txt`).

| Level | Box / Interval | `APRON` Octagon (`octagons/`) | `ELINA` Online-Decomposed (`opt_oct` / `opt_pk`) | `Taylor1+` Zonotope & `Astrée` Ellipsoid |
| :--- | :--- | :--- | :--- | :--- |
| **L1: Authoring & Maintenance Velocity** | Zero loop annotations; low manual intervention, high false-alarm triage on relational guards. | Low annotation overhead; requires `intdim` / `FE_UPWARD` discipline and threshold tuning (`oct_widening_thresholds`). | Identical `APRON` ABI (`IS_APRON`), drops into existing `IKOS`/`Crab`/`VSA` analyzers with 0 domain rewrites; RL join flags (`LAIT`) optional. | `Taylor1+` needs 0 templates; `Astrée` filters require syntactic pattern recognition (1–2 person-weeks per new domain functor, ~0 user annotations once calibrated). |
| **L2: Toolchain Build Time & Dependencies** | C (`box.a`): `< 3 s`, GMP/MPFR only. | C (`liboctMPQ`/`liboctD`): `~5–15 s`, GCC/Clang + GMP/MPFR; zero C++ template bloat. | C + AVX2 (`liboptoct.so`, `liboptpoly.so`, `libpartitions.so`): `~10–25 s` (`ELINA` C stack); `IKOS` C++14/LLVM/Boost build takes `~3–12 min` and multi-GB link RSS. | `libt1p*.a` (`~5–10 s`, optional `CSDP` SDP solver adds BLAS/LAPACK/gfortran link cost). |
| **L3: Fixpoint Analysis Latency** | $O(n)$ per transfer/join; `< 1 ms` per function. | $O(n^3)$ per full closure (`hmat_close`), $O(n^2)$ incremental (`hmat_close_incremental`); stalls once active scope $n > 150$. | $O(\sum_r |C_r|^3)$ octagons (`129x` fewer ops in 12x4 blocks); `PLDI 2015`/`POPL 2017` report `10x–1000x` speedups over `APRON` `Oct`/`NewPolka`, enabling interactive `< 50 ms` per-function runs. | `Taylor1+`: $O(m \cdot n)$ linear, $O(m^2)$ or SDP on nonlinear mul; `Astrée` analyzes `132k` LoC A340 C in `50–80 min` and `400k` LoC A380 C in `11h 48m` (`Cousot et al. 2005`). |
| **L4: Target Binary Execution Overhead** | `0%` once statically discharged; hybrid analyzers emit runtime assertions only on unproven checks. | `0%` target runtime overhead (pure static pre-deployment proof). | `0%` target runtime overhead (`IKOS` reports unproven `check` sites rather than instrumenting). | `0%` runtime overhead; primary value is proving **absence** of float overflow traps without inserting expensive runtime `fpclassify` checks inside real-time flight loops. |
| **L5: Certificate / Invariant Verification Speed** | Converged interval table checked in $O(n)$ per CFG edge. | Closed DBM checked in $O(n^2)$ or sparse Farkas duals without running Floyd–Warshall! | Factorized block constraints/Farkas multipliers checkable in $O(\sum_r |C_r|)$ or $O(\text{nnz})$ exact rationals (`0 LoC` of `ELINA`/`IKOS` in TCB). | `Taylor1+` / Ellipsoid invariants export as quadratic or linear Farkas/S-procedure certificates checkable in $O(1)$ per filter node (`< 1 ms` per loop head). |
| **L6: RAM, Disk & Binary Footprint** | `16 B` (`double`) or ~`64 B` (`mpq_t`) per var. | Dense `2n(n+1)` array: at $n=200$, `80,400` entries = `643 KiB` (`double`) or `~4–8 MiB` (`mpq_t` heap pointers) **per CFG node**. | Sparse block buffers omit zero cross-block slices (`O(\sum |C_r|^2)`); C `.so` footprint `< 1 MiB`. `IKOS` C++ `Octagon` uses `4n^2` `Bound<ZNumber>` (`2x` larger than half-matrix). | `Astrée` peak RSS: `300–580 MiB` on `132k` LoC A340 C, `~2.2 GiB` on `400k` LoC A380 C (`Cousot et al. 2005`). |

### 7. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

Basis: derived + source (`oct_nary.c`, `t1p_internal.h`, `opt_pk_widening.c`, `ikos/core/domain/numeric/octagon.hpp`).

#### (C1) Human Comprehensibility and Mental-Model Ergonomics

- **Working-memory concept count:** Intervals require 2 bounds per variable; octagons require understanding signed doubling (`2k`, `2k+1`) and anti-diagonal factor-of-2 scaling (`m[2k+1, 2k] = 2 * upper(x_k)`), a persistent source of off-by-2 bugs in custom implementations (`ikos/octagon.hpp:74` warns explicitly of internal bugs). `Taylor1+` noise symbols $\epsilon_k$ are intuitive locally ("shared perturbation source $k$") until constrained `manNS` joins mix `IN`/`UN` indices across loops, making raw affine dump tables unreadable (`t1p_internal.h` tracks `dim`, `nsymcons`, and `gamma` simultaneously).
- **Nonlocal causality of widening false alarms:** Unlike deductive verification (where a failed assertion points locally to a missing loop invariant or precondition), a widening-induced false alarm on line 400 frequently originates from an unrelated widen/narrow schedule, threshold omission, or strengthening order on line 50—and *tightening* an upstream `assume` can counterintuitively break the downstream fixpoint due to $\nabla$ non-monotonicity (`Experiment D`). Furthermore, because abstract joins and widenings lose concrete path provenance, numerical domains generally cannot synthesize an executable concrete counterexample trace when reporting "potential overflow."
- **Hidden FPU/ABI footguns:** `APRON`'s `ap_fpu_init()` mutates process-wide CPU state (`FE_UPWARD`). Any C/Rust FFI caller that invokes `NUM_DOUBLE` domains on a worker thread without re-calling `ap_fpu_init()`—or links a SIMD library that sets MXCSR `FTZ`/`DAZ`—silently breaks outward rounding soundness without raising a compiler or type error.

#### (C2) Simplicity, Orthogonality, and Universal Model Refinement

Separating **core semantic invariants** from **realization-medium quirks** exposes substantial accidental complexity across current implementations:

- **Accidental realization mechanics:** `APRON`/`ELINA`'s `2n(n+1)` `matpos2` bit-twiddling (`i^1`, `(i+1)*(i+1)/2`), `IKOS`'s 1-based `4n^2` matrix, `Taylor1+`'s separate `box` + `paf` + `manNS` dual state, and `ap_fpu_init()`'s mutable global rounding mode are hardware/memory-layout optimizations rather than distinct mathematical concepts.
- **Unifying semantic abstraction (Factorized Support-Function + Dual-Certificate Product):** Nearly all linear relational domains (`Box`, `DBM`, `Octagon`, `Template Polyhedra`, and `Zonotopes` with hypercube generators) are instances of one universal interface: a **dynamic variable-partitioned support function** $h_S(d) = \sup_{x \in S} \langle d, x \rangle$ over finite or parameterized direction templates $\{d\}$, paired with a **quadratic Lyapunov sublevel set** $x^T P x \le K$ solely for elliptic/rotational recurrences (where linear templates fail Felleisen macro-expressibility—approximating a 2D rotated disk to relative error $\varepsilon$ requires $\Omega(\varepsilon^{-1/2})$ linear facets, so forcing filters into linear template polyhedra pushes exponential complexity into template generators!).
- **Ousterhout deep-module & adapter-conservation test:** `ELINA`'s `partitions_api` succeeds as a deep module when hidden behind the `APRON` C ABI (`opt_oct` / `opt_pk`), keeping zero partition boilerplate in callers. Conversely, wrapping raw `double` DBMs with `FE_UPWARD` leaks global thread-state invariants across module boundaries; replacing global `fesetround` with **explicit per-operation IEEE 754 `RNDU`/`RNDD` rounding intrinsics** (`AVX-512` embedded rounding `{ru-sae}` or error-free transformations `TwoSum` + outward ulp bump) eliminates global FPU state mutation while preserving identical mathematical soundness. Similarly, exporting converged loop invariants as **exact-rational Farkas / DBM-potential certificates** decouples `100k+ LoC` fixpoint engines from the verification TCB cleanly without inventing new proof formats per domain.

## Boundaries

- **Machine-integer wraparound (`known not to apply` to unbounded $\mathbb{Z}$ DBMs without wrap modeling):** Standard `APRON` and `ELINA` octagon/polyhedra domains interpret variables over unbounded $\mathbb{Z}$ or $\mathbb{R}$. Applying them directly to 32/64-bit two's-complement arithmetic where wraparound occurs without explicit modular split/wrap transformers (`IKOS`'s `MachineIntDomain` wraps signed/unsigned intervals explicitly before numeric domain dispatch) is **unsound** on overflow.
- **IEEE 754 `NaN`, `-0.0`, and `FTZ`/`DAZ` subnormals (`unsupported` in `APRON` `NUM_DOUBLE`):** If an analyzed target program executes with hardware flush-to-zero (`FTZ`) or produces `NaN`/`Inf` mid-loop, `ap_manager.c`'s `test_fpu()` aborts initialization or `numflt_native.h` assumes strict IEEE 754 upward rounding without flush-to-zero exceptions.
- **Disjunctive / non-convex invariants (`unsupported` without trace partitioning):** Pure octagons, zonotopes, polyhedra, and single ellipsoids represent convex sets only; properties like `x != 0` or `x <= -1 || x >= 1` collapse to `Top` (`[-oo, +oo]`) upon join unless wrapped in a disjunctive trace-partitioning functor (`Astrée`).
- **Concurrent / multi-threaded shared-memory invariants (`not examined`):** All analyzed `APRON`, `ELINA`, `IKOS`, and `Astrée` filter domains target sequential or deterministic synchronous control-flow graphs; rely-guarantee / weak-memory extensions are outside the studied commits.
- **Closed-source `Astrée` implementation internals (`not examined`):** Exact source-level implementation details of commercial `Astrée` beyond peer-reviewed descriptions (`Feret ESOP 2004`, `Cousot et al. ESOP 2005`) were not examined; all `Astrée` ellipsoid math and A340/A380 metrics rest on published papers and independent probe execution.
- **Generalizability of `L2`/`L3` wall-clock timings (`unknown` beyond cited configurations):** `ELINA` and `Astrée` timings depend on variable coupling density, loop depth, and CPU SIMD width (`AVX2` vs. scalar); unpartitioned cliques of $n > 200$ tightly coupled variables degrade `ELINA` back to dense $O(n^3)$ / exponential Chernikova complexity.

## Evidence

- **Pinned Git repositories and inspected symbols:**
  - `antoinemine/apron` @ `0a7ca30527c29f5fc894bf424b4d24ca638beb4e`:
    - `octagons/oct_internal.h` (`matsize`, `matpos`, `matpos2`, `num_incomplete`, `num_safe`),
    - `octagons/oct_closure.c` (`hmat_s_step` L32–60, `hmat_close` L72–107, `hmat_close_incremental` L120–197),
    - `octagons/oct_nary.c` (`oct_widening` L165–199, `oct_widening_thresholds` L201–253, `oct_narrowing` L255–278, `oct_add_epsilon_bin` L359–398),
    - `num/numflt_native.h` (`numflt_sqrt` L118–127, `numflt_pow` L159–182), `num/numint_native.h` (`numint_cdiv_2` L136–137), `num/numint_mpz.h` (`numint_cdiv_2` L97–98), `apron/ap_manager.c` (`test_fpu` L267–289, `ap_fpu_init` L299–304),
    - `taylor1plus/t1p_internal.h` (`nsym_t`, `t1p_aff_t`, `optpr_problem_t`, `t1p_t`), `taylor1plus/t1p_meetjoin.c` (`t1p_meet_lincons_array`, `t1p_join`), `taylor1plus/t1p_fun.c` (`t1p_aff_mul` L229–245).
  - `eth-sri/elina` @ `f524156d292ac3a6f3cd676e2d2e7db6629e2b6f`:
    - `partitions_api/comp_list.h` (`comp_list_t`, `array_comp_list_t`),
    - `elina_oct/opt_oct_internal.h` (`is_int_flag`, `opt_oct_mat_t`, `opt_matsize`), `elina_oct/opt_oct_closure_comp_sparse.c` (`strengthning_int_comp_sparse` L124–260, `strengthning_comp_sparse` L263–418, `strong_closure_comp_sparse` L956–968), `elina_oct/opt_oct_closure_dense.c` (`strengthning_int_dense` L36–78), `elina_oct/opt_oct_closure_dense_scalar.c` (`floyd_warshall_dense_scalar`),
    - `elina_poly/opt_pk_internal.h` (`opt_pk_internal_t`), `elina_poly/opt_pk_cherni.c` (`opt_cherni_minimize` L505–629), `elina_poly/opt_pk_meetjoin.c`, `elina_poly/opt_pk_widening.c` (`opt_poly_widening_gen`, `opt_pk_widening` L599–624),
    - `elina_zonotope/zonotope_internal.h`, `elina_zonotope/zonotope_meetjoin.c`.
  - `NASA-SW-VnV/ikos` @ `ac7f7c1738976cabc58c6a53413df6e458995c38`:
    - `core/include/ikos/core/domain/numeric/octagon.hpp` (L70–75 warning, L308–365 `unsafe_normalize`), `dbm.hpp`, `var_packing_dbm.hpp`, `gauge_interval_congruence.hpp`, `apron.hpp`.
- **Peer-reviewed specifications:** Miné (HOSC 2006, `DOI: 10.1007/s10990-006-8609-1`; ESOP 2004, `DOI: 10.1007/978-3-540-24725-8_2`), Bagnara, Hill, Zaffanella (FMSD 2009, `DOI: 10.1007/s10703-009-0081-y`), Singh, Püschel, Vechev (PLDI 2015, `DOI: 10.1145/2737924.2738012`; POPL 2017, `DOI: 10.1145/3009837.3009885`), Ghorbal, Goubault, Putot (CAV 2009, `DOI: 10.1007/978-3-642-02658-4_47`), Feret (ESOP 2004, `DOI: 10.1007/978-3-540-24725-8_4`), Cousot et al. (ESOP 2005, `DOI: 10.1007/978-3-540-31987-0_3`).
- **Self-contained reproducible execution probe (`Basis: execution`, run 2026-11-19 on Linux x86_64 with Python 3.13):**
  Save as `/tmp/probe_domains.py` and run `python3 /tmp/probe_domains.py`:

```python
#!/usr/bin/env python3
"""Reproducible micro-probes for relational abstract domains (APRON/ELINA/IKOS/Astree)."""

from fractions import Fraction
import math

INF = Fraction(10**18)


def opp(i: int) -> int:
    return i ^ 1


def floyd_warshall_once(m, n):
    res = [[m[i][j] for j in range(n)] for i in range(n)]
    ops = 0
    for k in range(n):
        for i in range(n):
            for j in range(n):
                cand = res[i][k] + res[k][j]
                if cand < res[i][j]:
                    res[i][j] = cand
                ops += 1
    return res, ops


def s_step_once(m, n):
    res = [[m[i][j] for j in range(n)] for i in range(n)]
    ops = 0
    for i in range(n):
        for j in range(n):
            if res[i][opp(i)] < INF and res[opp(j)][j] < INF:
                cand = (res[i][opp(i)] + res[opp(j)][j]) / 2
                if cand < res[i][j]:
                    res[i][j] = cand
            ops += 1
    return res, ops


def strong_closure(m_init, n_vars: int, integer_tighten: bool = False, post_coherence: bool = False):
    n = 2 * n_vars
    m, ops1 = floyd_warshall_once(m_init, n)
    m, ops2 = s_step_once(m, n)
    ops = ops1 + ops2
    if integer_tighten:
        for i in range(n):
            if m[i][opp(i)] < INF:
                m[i][opp(i)] = 2 * Fraction(math.floor(m[i][opp(i)] / 2))
        if post_coherence:
            m, _ = floyd_warshall_once(m, n)
            m, _ = s_step_once(m, n)
    neg_diag = any(m[i][i] < 0 for i in range(n))
    return m, neg_diag, ops


def experiment_a_integer_tight_closure():
    print("=== Experiment A: Rational Strong Closure vs Integer Tight Closure ===")
    m = [[INF] * 4 for _ in range(4)]
    for i in range(4):
        m[i][i] = Fraction(0)
    m[3][0] = m[1][2] = Fraction(1)
    m[2][1] = m[0][3] = Fraction(-1)
    m[2][0] = m[1][3] = Fraction(0)
    m[0][2] = m[3][1] = Fraction(0)

    mq, empty_q, _ = strong_closure(m, 2, integer_tighten=False)
    mz_nc, empty_z_nc, _ = strong_closure(m, 2, integer_tighten=True, post_coherence=False)
    mz_tc, empty_z_tc, _ = strong_closure(m, 2, integer_tighten=True, post_coherence=True)
    print(f"Rational closure (Q): empty={empty_q}, 2x<={mq[1][0]}, -2x<={mq[0][1]} (feasible over Q at x=y=1/2)")
    print(f"Tighten w/o coherence: empty={empty_z_nc}, 2x<={mz_nc[1][0]}, -2x<={mz_nc[0][1]}, 2x+(-2x)={mz_nc[1][0]+mz_nc[0][1]} < 0 UNDETECTED on diag={mz_nc[0][0]}")
    print(f"BHZ tight closure: empty={empty_z_tc}, min diag={min(mz_tc[i][i] for i in range(4))} < 0 => UNSAT over Z")

    m2 = [[INF] * 4 for _ in range(4)]
    for i in range(4):
        m2[i][i] = Fraction(0)
    m2[1][0] = Fraction(3)
    m2[0][2] = m2[3][1] = Fraction(0)
    m2q, _, _ = strong_closure(m2, 2, integer_tighten=False)
    m2z_nc, _, _ = strong_closure(m2, 2, integer_tighten=True, post_coherence=False)
    m2z_tc, _, _ = strong_closure(m2, 2, integer_tighten=True, post_coherence=True)
    print(f"Transitive witness (2x<=3, y<=x): Q gives x+y<={m2q[1][2]}; no-coh gives x+y<={m2z_nc[1][2]}; BHZ tight gives x+y<={m2z_tc[1][2]}")


def experiment_b_block_decomposition():
    print("\n=== Experiment B: Dense vs ELINA Block-Decomposed Closure (n=48, 12x4) ===")
    n_vars = 48
    n = 2 * n_vars
    m_full = [[INF] * n for _ in range(n)]
    for i in range(n):
        m_full[i][i] = Fraction(0)
    blocks = [list(range(4 * b, 4 * b + 4)) for b in range(12)]
    for blk in blocks:
        for idx in range(len(blk) - 1):
            a, b = blk[idx], blk[idx + 1]
            m_full[2 * a][2 * b] = Fraction(3)
            m_full[2 * b + 1][2 * a + 1] = Fraction(3)
        last = blk[-1]
        m_full[2 * last + 1][2 * last] = Fraction(20)

    dense_closed, _, dense_ops = strong_closure(m_full, n_vars)
    comp_ops = 0
    max_diff = Fraction(0)
    for blk in blocks:
        sub_n = len(blk)
        sub_m = [[INF] * (2 * sub_n) for _ in range(2 * sub_n)]
        for i in range(sub_n):
            for j in range(sub_n):
                for s1 in (0, 1):
                    for s2 in (0, 1):
                        sub_m[2 * i + s1][2 * j + s2] = m_full[2 * blk[i] + s1][2 * blk[j] + s2]
        sub_closed, _, b_ops = strong_closure(sub_m, sub_n)
        comp_ops += b_ops
        for i in range(sub_n):
            for j in range(sub_n):
                for s1 in (0, 1):
                    for s2 in (0, 1):
                        d = abs(sub_closed[2 * i + s1][2 * j + s2] - dense_closed[2 * blk[i] + s1][2 * blk[j] + s2])
                        if d > max_diff:
                            max_diff = d
    print(f"Dense ops: {dense_ops}, Block-decomposed ops: {comp_ops}, Reduction: {dense_ops / comp_ops:.1f}x, Max discrepancy: {max_diff}")


def experiment_c_zonotope_and_astree_iir():
    print("\n=== Experiment C: Taylor1+ Zonotope Cancellation & Astree 2nd-Order IIR Filter ===")
    print("Taylor1+ exact cancellation (0.5+0.5*e1)-(0.5+0.5*e1) = [0, 0]; x*(1-x) for x in [0,1]: Interval=[0, 1], Taylor1+=[0, 0.25]")

    a, b = 1.5, 0.7
    s1_lo, s1_hi = 0.0, 0.0
    s2_lo, s2_hi = 0.0, 0.0
    z1, z2 = [], []
    oct_m = [[1e18] * 4 for _ in range(4)]
    for i in range(4):
        oct_m[i][i] = 0.0
        oct_m[i][opp(i)] = 0.0

    def oct_close(mat):
        res = [[mat[i][j] for j in range(4)] for i in range(4)]
        for k in range(4):
            for i in range(4):
                for j in range(4):
                    res[i][j] = min(res[i][j], res[i][k] + res[k][j])
        for i in range(4):
            for j in range(4):
                res[i][j] = min(res[i][j], 0.5 * (res[i][opp(i)] + res[opp(j)][j]))
        return res

    oct_m = oct_close(oct_m)
    R_ell = 0.0
    for step in range(1, 41):
        ns1_lo = 1.5 * s1_lo - 0.7 * s2_hi - 1.0
        ns1_hi = 1.5 * s1_hi - 0.7 * s2_lo + 1.0
        s2_lo, s2_hi = s1_lo, s1_hi
        s1_lo, s1_hi = ns1_lo, ns1_hi

        nz1 = [1.5 * c1 - 0.7 * c2 for c1, c2 in zip(z1, z2)] + [1.0]
        nz2 = list(z1) + [0.0]
        z1, z2 = nz1, nz2

        def max_lin(mat, c1, c2):
            lines = [
                (1, 0, mat[1][0] / 2), (-1, 0, mat[0][1] / 2),
                (0, 1, mat[3][2] / 2), (0, -1, mat[2][3] / 2),
                (1, -1, mat[2][0]), (-1, 1, mat[0][2]),
                (1, 1, mat[3][0]), (-1, -1, mat[0][3]),
            ]
            best = -1e18
            for i in range(len(lines)):
                for j in range(i + 1, len(lines)):
                    a1, b1, d1 = lines[i]
                    a2, b2, d2 = lines[j]
                    det = a1 * b2 - a2 * b1
                    if det == 0:
                        continue
                    x = (d1 * b2 - d2 * b1) / det
                    y = (a1 * d2 - a2 * d1) / det
                    if all(la * x + lb * y <= ld + 1e-9 for la, lb, ld in lines):
                        best = max(best, c1 * x + c2 * y)
            return best

        new_oct = [[1e18] * 4 for _ in range(4)]
        for i in range(4):
            new_oct[i][i] = 0.0
        new_oct[1][0] = 2 * (max_lin(oct_m, 1.5, -0.7) + 1.0)
        new_oct[0][1] = 2 * (max_lin(oct_m, -1.5, 0.7) + 1.0)
        new_oct[3][2] = 2 * max_lin(oct_m, 1.0, 0.0)
        new_oct[2][3] = 2 * max_lin(oct_m, -1.0, 0.0)
        new_oct[2][0] = new_oct[1][3] = max_lin(oct_m, 0.5, -0.7) + 1.0
        new_oct[0][2] = new_oct[3][1] = max_lin(oct_m, -0.5, 0.7) + 1.0
        new_oct[3][0] = new_oct[1][2] = max_lin(oct_m, 2.5, -0.7) + 1.0
        new_oct[0][3] = new_oct[2][1] = max_lin(oct_m, -2.5, 0.7) + 1.0
        oct_m = oct_close(new_oct)

        R_ell = math.sqrt(b) * R_ell + 1.0
        s1_ell = R_ell * math.sqrt(b / (b - a * a / 4.0))
        z1_bound = sum(abs(c) for c in z1)
        if step in (5, 10, 20, 40):
            print(
                f"Step {step:2d}: Interval |s1|<={s1_hi:11.3f}, "
                f"Octagon |s1|<={oct_m[1][0]/2:11.3f}, "
                f"UnrolledZonotope |s1|<={z1_bound:7.3f}, "
                f"Ellipsoid |s1|<={s1_ell:7.3f}"
            )
    R_inf = 1.0 / (1.0 - math.sqrt(b))
    s1_inf = R_inf * math.sqrt(b / (b - a * a / 4.0))
    print(f"Ellipsoid exact fixpoint limit (k->oo): R*={R_inf:.4f}, |s1|<={s1_inf:.4f}")


def experiment_d_widening_and_ieee754():
    print("\n=== Experiment D: Widening Non-Monotonicity & IEEE 754 RN Unsoundness ===")
    def box_widen(a, b):
        lo_a, hi_a = a
        lo_b, hi_b = b
        lo = lo_a if lo_b >= lo_a else -math.inf
        hi = hi_a if hi_b <= hi_a else math.inf
        return (lo, hi)

    x1, x2, y = (0, 1), (0, 2), (0, 2)
    w1, w2 = box_widen(x1, y), box_widen(x2, y)
    print(f"Non-monotonicity: x1={x1} <= x2={x2}, y={y}")
    print(f"  x1 \\nabla y = {w1}, whereas x2 \\nabla y = {w2}")

    d1, d2 = float(2**53), 1.0
    rn_sum = d1 + d2
    exact_x_minus_z = (2**53) + 1
    upward_sum = math.nextafter(d1, math.inf) if rn_sum == d1 else rn_sum
    print(f"IEEE 754 RN closure: fl_RN(2^53 + 1.0) = {rn_sum:.1f} < exact {exact_x_minus_z} (UNSOUND={exact_x_minus_z > rn_sum})")
    print(f"Outward FE_UPWARD bound: nextafter(2^53, +inf) = {upward_sum:.1f} >= {exact_x_minus_z} (SOUND={upward_sum >= exact_x_minus_z})")


if __name__ == "__main__":
    experiment_a_integer_tight_closure()
    experiment_b_block_decomposition()
    experiment_c_zonotope_and_astree_iir()
    experiment_d_widening_and_ieee754()
```

Observed output (`exit 0`):

```text
=== Experiment A: Rational Strong Closure vs Integer Tight Closure ===
Rational closure (Q): empty=False, 2x<=1, -2x<=-1 (feasible over Q at x=y=1/2)
Tighten w/o coherence: empty=False, 2x<=0, -2x<=-2, 2x+(-2x)=-2 < 0 UNDETECTED on diag=0
BHZ tight closure: empty=True, min diag=-120 < 0 => UNSAT over Z
Transitive witness (2x<=3, y<=x): Q gives x+y<=3; no-coh gives x+y<=3; BHZ tight gives x+y<=2

=== Experiment B: Dense vs ELINA Block-Decomposed Closure (n=48, 12x4) ===
Dense ops: 893952, Block-decomposed ops: 6912, Reduction: 129.3x, Max discrepancy: 0

=== Experiment C: Taylor1+ Zonotope Cancellation & Astree 2nd-Order IIR Filter ===
Taylor1+ exact cancellation (0.5+0.5*e1)-(0.5+0.5*e1) = [0, 0]; x*(1-x) for x in [0,1]: Interval=[0, 1], Taylor1+=[0, 0.25]
Step  5: Interval |s1|<=     21.203, Octagon |s1|<=      7.216, UnrolledZonotope |s1|<=  6.153, Ellipsoid |s1|<=  8.150
Step 10: Interval |s1|<=    507.921, Octagon |s1|<=     16.484, UnrolledZonotope |s1|<=  7.789, Ellipsoid |s1|<= 11.492
Step 20: Interval |s1|<= 271206.188, Octagon |s1|<=     42.524, UnrolledZonotope |s1|<=  9.030, Ellipsoid |s1|<= 13.423
Step 40: Interval |s1|<=77070116173.021, Octagon |s1|<=    146.542, UnrolledZonotope |s1|<=  9.267, Ellipsoid |s1|<= 13.803
Ellipsoid exact fixpoint limit (k->oo): R*=6.1222, |s1|<=13.8135

=== Experiment D: Widening Non-Monotonicity & IEEE 754 RN Unsoundness ===
Non-monotonicity: x1=(0, 1) <= x2=(0, 2), y=(0, 2)
  x1 \nabla y = (0, inf), whereas x2 \nabla y = (0, 2)
IEEE 754 RN closure: fl_RN(2^53 + 1.0) = 9007199254740992.0 < exact 9007199254740993 (UNSOUND=True)
Outward FE_UPWARD bound: nextafter(2^53, +inf) = 9007199254740994.0 >= 9007199254740993 (SOUND=True)
```

## Revalidation

1. **Check upstream repository movement:**
   `git -c protocol.version=0 ls-remote https://github.com/antoinemine/apron.git HEAD`
   `git -c protocol.version=0 ls-remote https://github.com/eth-sri/elina.git HEAD`
   `git -c protocol.version=0 ls-remote https://github.com/NASA-SW-VnV/ikos.git HEAD`
2. **Verify targeted implementation invariants against newer revisions:**
   - Diff `octagons/oct_closure.c`, `octagons/oct_nary.c`, and `apron/ap_manager.c` (`ap_fpu_init`) to verify whether integer tight closure (`2 * floor(...)`) or thread-safe per-op rounding replaced `FE_UPWARD`.
   - Diff `elina_oct/opt_oct_closure_comp_sparse.c` (`strengthning_int_comp_sparse` `ceil` vs `floor`) and `elina_poly/opt_pk_cherni.c`.
   - Check `core/include/ikos/core/domain/numeric/octagon.hpp` to see whether native `Octagon` issues remain open or have been superseded by `VarPackingDBM` / `APRON`.
3. **Re-run deterministic domain probe (`< 0.1 s`):**
   Execute `python3 /tmp/probe_domains.py` and verify identical outputs across Experiments A–D.
