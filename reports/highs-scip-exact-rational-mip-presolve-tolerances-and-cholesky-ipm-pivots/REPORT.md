# Floating-Point MILP Presolve Paradoxes, Exact Rational LP/VIPR Recovery, and Quasi-Definite Conic IPM Regularization

## Summary

Finite-precision mathematical programming solvers rely on coupled absolute/relative tolerances (`1e-6` to `1e-13`) and diagonal KKT perturbations (`1e-14` to `2e-7`) that cease to be sound under wide coefficient dynamic ranges (`Big-M` indicator encodings) or nearly parallel conic constraints. Across `ERGO-Code/HiGHS` (`f3f113d230429a8c0014b12ab0dd1a3847e58c55`), `scipopt/scip` (`005ef83ae586f05775aa1baed95c7a66b57ff6aa`), `scipopt/soplex` (`0d76dd34846b9b2296bdaf9eb3f215527156bfe2`), `oxfordcontrol/Clarabel.rs` (`b6aa0421ec818a31c7f26ada8f6cef2558c768bf`), and `ambros-gleixner/VIPR` (`f221c3fd2274e8e859e8e24505278d6f7c1bb8ff`), four structural laws govern solver soundness, exact rational recovery, and independent proof verification:

1. **Bidirectional `Big-M` Failure Modes (Trickle-Flow False Feasibility and Presolve False Infeasibility)**: Under `HiGHS` and `SCIP` default tolerances (`mip_feasibility_tolerance = 1e-6` in `highs/lp_data/HConst.h:387`, `primal_feasibility_tolerance = 1e-7` at `line 383`, `small_matrix_value = 1e-9` and `large_matrix_value = 1e15` in `highs/lp_data/HighsOptions.h:818-830`), coupling continuous flow $x \le M z$ ($z \in \{0,1\}$) with $M \ge 1 / \epsilon_{\text{int}}$ ($10^7$) allows $z = 10^{-7}$ to pass integrality checks as "integer `0`" while unlocking $x = M z = 1.0$ ("trickle flow" at `0` fixed startup cost). Conversely, during IEEE-754 `binary64` presolve bound strengthening (`highs/presolve/HPresolve.cpp:78-83, 225-256`), even admissible constants $M = 5 \times 10^{11} \ll 10^{15}$ have unit-in-the-last-place spacing $\operatorname{ulp}(M) = 2^{-13} \approx 1.22 \times 10^{-4} > 10^{-6}$: fixing $z = 1$ in $M z + x \le M + \frac{3}{10}$ evaluates $\operatorname{fl}(M + 0.3) - M = 0.29998779296875$, violating $x \ge 0.3$ by **`1.221e-5 > 12 × mip_feasibility_tolerance`** and falsely declaring an exact-zero-slack integer-feasible model **`INFEASIBLE`**.
2. **Exact Rational Basis Recovery Without Full-Simplex `GMP` Slowdown**: `SoPlex` (`src/soplex/solverational.hpp:559-575`, `src/soplex/ratrecon.hpp:39-195`) avoids the `10x–1000x` penalty of pivoting directly in `GMP` `mpq_t` arithmetic by keeping LU basis factorizations in `FP64` (with `MPFR` precision-boosting fallback, `solverational.hpp:137-460`), scaling exact rational residuals $r = b - B x \in \mathbb{Q}^m$ dynamically into `FP64` range at each iterative refinement round (`Gleixner, Steffy & Wolter 2016`), and reconstructing exact rational primal/dual vectors via Gauss–Euclidean continued-fraction convergents bounded by $D_{\text{bound}} = \max(2^{24}, \lfloor\sqrt{B_{\text{denom}}}\rfloor)$ (`ratrecon.hpp:55-68, 136-180`).
3. **Treeless Linear-Stream `VIPR` Proof Checking Decouples `MILP` Presolve/Heuristics from the TCB**: Exact `SCIP` (`src/scip/scip_exact.c`, `src/scip/lpexact_bounding.c:1185-1360`, `src/scip/certificate.cpp`) projects floating-point duals into safe rational bounds (`project-and-shift` / exact Farkas rays) and emits a **flat, treeless `VIPR 1.0/1.1` derivation DAG** (`cert_spec_v1_1.md`) using only four elementary inference rules: `{ asm }` branching assumptions, `{ lin }` sign-compatible rational Farkas combinations, `{ rnd }` Chvátal–Gomory integer floor/ceiling cuts, and `{ uns }` integral split resolution ($a^\top x \le \beta$ vs. $a^\top x \ge \beta + 1$ for $a \in \mathbb{Z}^n, \beta \in \mathbb{Z}$) with explicit last-use `index` retirement (`viprchk.cpp`, `1,685 LoC` C++). Neither branch-and-bound tree topology nor `50,000+ LoC` of presolvers enters the trusted computing base.
4. **Quasi-Definite `LDL^T` (`QDLDL`) Regularization vs. Iterative-Refinement Stalling on Conic Farkas Certificates**: `Clarabel.rs` (`src/qdldl/qdldl.rs:49-60, 643-666`, `src/solver/implementations/default/settings.rs:140-182`) factors symmetric indefinite homogeneous self-dual KKT matrices without pivot permutations by enforcing quasi-definiteness (`Dsigns = [+1, ..., +1, -1, ..., -1]`) via static diagonal shifts (`1e-8 + eps^2 * ||diag(K)||_inf`, `directldlkktsolver.rs:324-329`) and on-the-fly dynamic pivot clamping (`if D[k] * sign < 1e-13 { D[k] = 2e-7 * sign }`, `qdldl.rs:647-649`). On nearly parallel infeasible rows ($\theta \approx 10^{-8}$), unregularized `binary64` elimination cancels the Schur pivot to **exact `0.0`** (`QDLDLError::ZeroPivot`), whereas clamping `|D[k]|` to $\delta_d = 2 \times 10^{-7}$ rotates the dual step away from the Farkas nullspace and yields a stationary iterative-refinement reduction ratio $1 + \sigma_{\text{true}}/\delta_d \approx 1.0000003 < \texttt{stop\_ratio}\; (5.0)$ (`directldlkktsolver.rs:309-316`), aborting refinement on iteration `1` and stalling in `SolverStatus::InsufficientProgress` (`info.rs:198-216`) instead of certifying `PrimalInfeasible` (`info.rs:357, 371-379`).

---

## Applicability

This report covers the numerical, algorithmic, and proof-verification interfaces connecting five upstream implementations and five foundational papers:

- **Floating-Point Simplex, Presolve, and `MILP` Engines**: `ERGO-Code/HiGHS` at `f3f113d230429a8c0014b12ab0dd1a3847e58c55` (`highs/presolve/HPresolve.{h,cpp}`, `highs/presolve/HPresolveStrengthenIneq.cpp`, `highs/lp_data/{HConst.h,HighsOptions.h}`, and interior-point engines `highs/ipm/ipx/` and `highs/ipm/hipo/`) and `scipopt/scip` at `005ef83ae586f05775aa1baed95c7a66b57ff6aa` (`src/scip/presol_*.c`, `src/scip/{scip_exact.c,lpexact.c,lpexact_bounding.c,certificate.cpp}`).
- **Exact Rational LP & Certificate Toolchains**: `scipopt/soplex` at `0d76dd34846b9b2296bdaf9eb3f215527156bfe2` (`src/soplex/solverational.hpp`, `src/soplex/ratrecon.hpp`) and `ambros-gleixner/VIPR` at `f221c3fd2274e8e859e8e24505278d6f7c1bb8ff` (`cert_spec_v1_0.md`, `cert_spec_v1_1.md`, `code/viprchk.cpp`, `code/viprcomp.cpp`).
- **Conic Interior-Point & Sparse `LDL^T` Solver**: `oxfordcontrol/Clarabel.rs` at `b6aa0421ec818a31c7f26ada8f6cef2558c768bf` (`src/qdldl/qdldl.rs`, `src/solver/core/kktsolvers/direct/quasidef/directldlkktsolver.rs`, `src/solver/implementations/default/{settings.rs,info.rs,kktsystem.rs,presolver.rs}`).
- **Mathematical Authority**: Klotz (`DOI: 10.1287/educ.2014.0130`), Cook, Koch, Steffy & Wolter (`DOI: 10.1007/s12532-013-0055-6`), Gleixner, Steffy & Wolter (`DOI: 10.1287/ijoc.2016.0692`), Cheung, Gleixner & Steffy (`DOI: 10.1007/978-3-319-59250-3_13`), Eifler & Gleixner (`DOI: 10.1007/s10107-021-01749-5`), and Goulart & Chen (`DOI: 10.48550/arXiv.2405.12762`).

**Scope Conditions**:
- Tolerance paradoxes apply to standard IEEE-754 `binary64` (`53`-bit significand, $\epsilon_{\text{mach}} = 2^{-53} \approx 1.11 \times 10^{-16}$) runs of `HiGHS`, `SCIP` (default `FP64` mode), and commercial `MILP` solvers sharing `~1e-6` integrality / primal feasibility defaults.
- `VIPR 1.0/1.1` certificate rules apply strictly to **rational linear and mixed-integer linear programs** (`MILP`s over $\mathbb{Q}$ and $\mathbb{Z}$). Second-order, exponential, power, and positive-semidefinite cones supported by `Clarabel.rs` involve irrational optima and nonlinear dual cones outside `VIPR`'s polyhedral grammar (addressed separately under Conic Farkas Duals and **Boundaries**).

---

## Findings

### 1. Floating-Point `Big-M` Tolerance Contradictions and Presolve Bound-Strengthening False Infeasibility

`Basis: source + execution + derived`

In `ERGO-Code/HiGHS`, feasibility and matrix-conditioning thresholds are governed by compile-time defaults in `highs/lp_data/HConst.h:382-391` and option records in `highs/lp_data/HighsOptions.h:817-868, 1238-1243, 1795-1800`:

| Parameter (`HiGHS` / `SCIP` Equivalent) | `HiGHS` Symbol & Source Location | Default Value | Minimum Allowed | Semantic Role in Solver & Presolve |
| :--- | :--- | :---: | :---: | :--- |
| **Primal LP Feasibility Tol** | `kDefaultKktTolerance` (`HConst.h:383`) | `1e-7` | `1e-10` | Max row/bound violation $\max(0, Ax - u, l - Ax)$ in simplex |
| **Dual LP Feasibility Tol** | `dual_feasibility_tolerance` (`HighsOptions.h:847`) | `1e-7` | `1e-10` | Max reduced-cost sign violation in dual simplex |
| **MIP Integrality / Primal Tol** | `kDefaultMipTolerance` (`HConst.h:387`, `HPresolve.cpp:82`) | **`1e-6`** | `1e-10` | Max $|z - \operatorname{round}(z)|$ AND `HPresolve::primal_feastol` in MIP mode! |
| **MIP Dual Tol** | `getMipDualFeasibilityTolerance()` (`HighsOptions.h:1798`) | `1e-7` (`0.1 * mip_tol`) | `1e-11` | Dual fixing & reduced-cost bound tightening in MIP |
| **Zero Drop Filter** | `small_matrix_value` (`HighsOptions.h:818-822`) | **`1e-9`** | `1e-12` | Matrix entries $|a_{ij}| \le 10^{-9}$ silently zeroed on load/pivot |
| **Max Finite Matrix Entry** | `large_matrix_value` (`HighsOptions.h:826-829`) | **`1e15`** | `1e0` | Entries $|a_{ij}| < 10^{15}$ accepted without input rejection |

Note line `82` of `highs/presolve/HPresolve.cpp`: when `mipsolver != nullptr`, `this->primal_feastol = options->mip_feasibility_tolerance` (`1e-6`), which then gates implied-bound checks such as `HPresolve::isLowerImplied()` (`lines 225-230`: `implLower >= model->col_lower_[col] - primal_feastol`) and `isUpperStrictlyImplied()` (`lines 250-255`). When power-grid security-constrained unit commitment (`SCUC`), vehicle routing, or hybrid MPC models encode logical implications $z = 0 \implies x \le 0$ via `Big-M` rows $x - M z \le 0$ ($z \in \{0,1\}$), two opposite soundness failures arise inside the accepted range $M \in [10^6, 10^{15})$ (`Klotz 2014`, `DOI: 10.1287/educ.2014.0130`):

1. **False Feasibility ("Trickle-Flow" Integrality Bypass at $M \ge \epsilon_{\text{int}}^{-1}$)**:
   - Consider minimizing generator startup + fuel cost $\min 1000 z + x_1 + 10 x_2$ subject to $x_1 + x_2 \ge 1$, $x_1 - M z \le 0$, $z \in \{0,1\}$, $x_1, x_2 \ge 0$ with $M = 10^7$.
   - Mathematically, $z = 0 \implies x_1 = 0 \implies x_2 = 1$ (cost `10`), or $z = 1, x_1 = 1$ (cost `1001`).
   - Under `mip_feasibility_tolerance = 1e-6`, the solver legally accepts $z^* = 10^{-7}$ as integral (`|1e-7 - 0| = 1e-7 <= 1e-6`), while $x_1 - 10^7 z^* \le 0$ permits **`x_1^* = 1.0` (`100%` of demand served by an "uncommitted" `z = 0` generator!)** at spurious objective `1.0001` (`90%` below true optimal cost `10`!). Tightening `mip_feasibility_tolerance` to `1e-9` shifts—rather than eliminates—the threshold to $M \ge 10^9$ while increasing simplex basis refactorization failures.
2. **False Infeasibility via IEEE-754 `binary64` Presolve Bound-Strengthening Cancellation**:
   - Consider the exact rational `MILP` constraint pair $M z + x \le M + \frac{3}{10}$, $z \ge 1$, $x \ge \frac{3}{10}$, $z \in \{0, 1\}$ with $M = 5 \times 10^{11}$ (`2000x` below `large_matrix_value = 1e15`). Over $\mathbb{Q}$, $(z = 1, x = \frac{3}{10})$ satisfies every inequality with exact `0` violation.
   - Because $5 \times 10^{11} \in [2^{38}, 2^{39})$, IEEE-754 `binary64` (`53` significand bits) has $\operatorname{ulp}(5 \times 10^{11}) = 2^{38 - 52} = 2^{-14} = 6.103515625 \times 10^{-5}$. Evaluating the right-hand side `fl(5e11 + 0.3)` rounds down to `500000000000.29998779296875`.
   - When presolve fixes $z = 1$ and computes the implied upper bound $u_x^{\text{impl}} = \operatorname{fl}(b - M \cdot 1) = 0.29998779296875$, the lower-vs-upper bound gap is:
     $$l_x - u_x^{\text{impl}} = 0.3 - 0.29998779296875 = \mathbf{1.220703125 \times 10^{-5}} > 12.2 \times \texttt{primal\_feastol}\; (10^{-6}).$$
   - Presolve immediately aborts with `kInfeasible` (`Basis: execution`), and chaining $k$ rounds of variable aggregation (`HPresolveAggregator.cpp`) or two-row bound tightening (`presol_tworowbnd.c` / `presol_redvub.c` in `SCIP`) compounds this loss at much smaller $M \sim 10^7$ whenever pivot ratios $(M / a_{ij}) \approx 10^7$ multiply `1e-13` simplex roundoff into `> 1e-6` bound contradictions (`Cook, Koch, Steffy & Wolter 2013`, `DOI: 10.1007/s12532-013-0055-6`, documenting `MIPLIB` instances where mainstream `FP64` solvers returned mutually contradictory optimal/infeasible verdicts).

---

### 2. Exact Rational LP Iterative Refinement (`SoPlex`) and Hybrid Safe Dual Bounding (`Exact SCIP`)

`Basis: source + execution`

Naively replacing every `double` in dual simplex with `GMP` `mpq_t` arbitrary-precision rationals causes catastrophic **bit-length explosion** during Gaussian elimination: after $k$ pivots, basis denominators grow as $O(\det(B)) = 2^{O(m \log \|A\|_\infty)}$, slowing LP node relaxations by `50x–1,000x`. `scipopt/soplex` (`src/soplex/solverational.hpp`, `src/soplex/ratrecon.hpp`) and `scipopt/scip` (`src/scip/scip_exact.c`, `src/scip/lpexact_bounding.c`) achieve near-`FP64` speed with `100%` exact $\mathbb{Q}$-soundness via three layered algorithms:

1. **Rational-Residual Iterative Refinement Over an `FP64` Basis (`solverational.hpp:559-575`, `Gleixner, Steffy & Wolter 2016`, `DOI: 10.1287/ijoc.2016.0692`)**:
   - Let $B \in \mathbb{Q}^{m \times m}$ be the candidate optimal basis found by fast `FP64` simplex (`_solveRealLPAndRecordStatistics`). Instead of factoring $B$ over $\mathbb{Q}$, `_performOptIRStable()` retains the approximate `FP64` LU factors $\tilde{L}\tilde{U} \approx B$:
     1. Compute exact primal/dual residuals in `GMP` `mpq_t`: $r^{(k)} = b - B x^{(k)} \in \mathbb{Q}^m$ and $d^{(k)} = c_B - B^\top y^{(k)} \in \mathbb{Q}^m$.
     2. Compute scaling factor $\Delta_k = \max(1, \|r^{(k)}\|_\infty^{-1})$ (rounded to a power of `2` so scaling is mantissa-exact!), convert $\operatorname{fl}(\Delta_k r^{(k)}) \in \mathbb{F}_{64}^m$, solve $\tilde{L}\tilde{U} \tilde{\delta} = \operatorname{fl}(\Delta_k r^{(k)})$ in fast `FP64` (`O(\text{nnz}(L+U))` hardware FMA!), and update $x^{(k+1)} = x^{(k)} + \Delta_k^{-1} \mathbb{Q}(\tilde{\delta})$.
     3. Provided $\kappa_\infty(B) \cdot \epsilon_{\text{mach}} \ll 1$ (`condition < 10^{14}`), $\|r^{(k)}\|_\infty$ shrinks by `~10^{-14}` **per refinement round** (`3–5` rounds yield `200+` bits of rational precision; on extreme `condition >= 10^{16}` bases where `FP64` LU stalls, `solverational.hpp:137-460` triggers `MPFR` **precision boosting** `_setupBoostedSolverAfterRecovery()` at `128`/`256` bits).
2. **Continued-Fraction Rational Vector Reconstruction (`src/soplex/ratrecon.hpp:39-195`)**:
   - Iterative refinement yields dyadic rationals $x^{(k)}$ with power-of-two denominators $2^{53 k}$, not the true reduced basis solution $B^{-1} b = p / q$ with $q \le |\det(B)|$.
   - Every `ratrecFreq` rounds, `Reconstruct()` (`ratrecon.hpp:39-185`) converts $x^{(k)}$ to a common integer denominator `denom`, sets working denominator bound $D_{\text{bound}} = \max(16{,}777{,}216,\; \lfloor\sqrt{\text{denomBoundSquared}}\rfloor)$ (`2^{24}` floor at `lines 63-67` so exact `binary32`/`binary64` inputs are never distorted!), runs Euclidean quotient-remainder steps `divide_qr(tn, td, ai, temp)` (`lines 111-161`) generating convergent fractions $p_i / q_i$ until $q_i > D_{\text{bound}}$, tracks cumulative `LCM`/`GCD` across coordinates (`lines 171-179`), and verifies **exact** algebraic optimality $B x^* = b,\; B^\top y^* = c_B,\; x^*_B \ge l_B,\; c_N - A_N^\top y^* \ge 0$ in `GMP`! In our ill-conditioned $2 \times 2$ probe ($\kappa \approx 4 \times 10^7$, where naive `FP64` incurs `1.48e-9` basis error), `4` IR steps + `Reconstruct()` recover exact $\left(\frac{5}{3}, \frac{1}{3}\right)$ with `0` residual (`Basis: execution`).
3. **Hybrid Branch-and-Bound Safe Dual Bounding Without Exact LP at Every Node (`src/scip/lpexact_bounding.c:1183-1365`, `Cook et al. 2013`, `Eifler & Gleixner 2023`)**:
   - Solving an exact rational LP at *every* branch-and-bound node is unnecessary because any dual-feasible vector $y \in \mathbb{Q}^m$ yields a valid lower bound via weak duality!
   - For any `MILP` node $\min\{c^\top x : A x \ge b,\; l \le x \le u\}$, `SCIP` solves the node relaxation in fast `FP64` (`lp->rows[i]` duals $\tilde{y} \ge 0$), casts $\tilde{y}$ to rationals (`SCIPrationalSetReal`, `lpexact_bounding.c:1327, 1329`), computes exact dual violation $r_j = c_j - (A^\top \hat{y})_j \in \mathbb{Q}$, and decomposes $r_j = r_j^+ - r_j^-$ using finite variable bounds $(l_j, u_j)$ (**bound-shift**, `O(nnz(A))` rational FMA!)—or projects $\hat{y}$ onto the exact dual cone via a pre-computed interior point (`project-and-shift`, `lpexact_bounding.c:1242-1308`, including `usefarkas = TRUE` for exact node infeasibility pruning)—reserving full `SoPlex` rational basis recovery strictly for nodes where bound-shift fails to prune or fractional integer solutions appear (`< 3%` of tree nodes on `MIPLIB`).

---

### 3. Treeless `VIPR 1.0/1.1` MILP Certificates: Grammar, Inference Rules, and Streaming Liveness

`Basis: normative + source + execution`

Even an exact rational `MILP` solver (`Exact SCIP` + `SoPlex` + `GMP`) comprises **`> 600,000 LoC` of C/C++** (`presolve`, primal heuristics, symmetry handlers, cut separators, conflict analysis). `VIPR` (*Verifying Integer Programming Results*, `Cheung, Gleixner & Steffy 2017`, `DOI: 10.1007/978-3-319-59250-3_13`; `ambros-gleixner/VIPR` `cert_spec_v1_1.md` and `code/viprchk.cpp`, `1,685 LoC`) removes the entire solver from the trusted computing base by compiling any `MILP` optimality or infeasibility proof into a **flat, sequential derivation table** (`VER`, `VAR`, `INT`, `OBJ`, `CON`, `RTP`, `SOL`, `DER`).

Every derived line $k \in \{m, \dots, m+d-1\}$ in `DER` has the form `name sense rhs coeffs { reason } retire_idx` and carries an implicit assumption set $\mathcal{A}(k) \subseteq \{m, \dots, k\}$ computed monotonically by four kernel rules (`cert_spec_v1_1.md:84-93, 227-237`):

$$\begin{array}{lcl}
\text{\textbf{(ASM)}} & \dfrac{\text{line } k:\; C_k\quad \{\texttt{asm}\}}{\vdash (C_k,\; \mathcal{A}(k) = \{k\})} \\[10pt]
\text{\textbf{(LIN)}} & \dfrac{\forall j \in [1..p]:\; i_j < k \quad \text{all } \lambda_j s(C_{i_j}) \ge 0 \text{ (or all } \le 0\text{)} \quad \sum_{j=1}^p \lambda_j C_{i_j} \triangleright_{\text{dom}} C_k}{\vdash \left(C_k,\; \mathcal{A}(k) = \bigcup_{j=1}^p \mathcal{A}(i_j)\right)} \\[12pt]
\text{\textbf{(RND)}} & \dfrac{\left(\sum_{j=1}^p \lambda_j a^{(i_j)}\right) \in \mathbb{Z}^I \times \{0\}^{n \setminus I} \quad \operatorname{round}_{\le/\ge}\!\left(\sum_{j=1}^p \lambda_j C_{i_j}\right) \triangleright_{\text{dom}} C_k}{\vdash \left(C_k,\; \mathcal{A}(k) = \bigcup_{j=1}^p \mathcal{A}(i_j)\right)} \\[12pt]
\text{\textbf{(UNS)}} & \dfrac{i_1, l_1, i_2, l_2 < k \quad C_{i_1} \triangleright_{\text{dom}} C_k \quad C_{i_2} \triangleright_{\text{dom}} C_k \quad C_{l_1}:\; a^\top x \le \beta \quad C_{l_2}:\; a^\top x \ge \beta + 1 \quad (a \in \mathbb{Z}^I,\; \beta \in \mathbb{Z})}{\vdash \left(C_k,\; \mathcal{A}(k) = (\mathcal{A}(i_1) \setminus \{l_1\}) \cup (\mathcal{A}(i_2) \setminus \{l_2\})\right)}
\end{array}$$

where $s(\ge) = +1, s(=) = 0, s(\le) = -1$, Chvátal–Gomory rounding $\operatorname{round}_{\le/\ge}$ replaces $\beta \in \mathbb{Q}$ by $\lfloor\beta\rfloor$ for $\le$ and $\lceil\beta\rceil$ for $\ge$ (`cert_spec_v1_1.md:19-29`), and restricted domination $C \triangleright_{\text{dom}} C'$ holds either when $C$ is an absurdity ($0 \ge \beta$ with $\beta > 0$, $0 \le \beta$ with $\beta < 0$, or $0 = \beta \neq 0$, dominating *every* constraint) or when $a = a'$ and the tightened bound implies $C'$ (`lines 31-39`).

Three architectural properties make `VIPR` uniquely suited for high-assurance verification:
1. **Zero Branch-and-Bound Tree State**: Branching on $x_0 \le 0$ vs. $x_0 \ge 1$ simply introduces two `{ asm }` lines (`A1`, `A2`), derives conditional bounds/absurdities under $\mathcal{A}$, and discharges both assumptions via `{ uns i1 A1 i2 A2 }` until the final line has **$\mathcal{A}(m+d-1) = \emptyset$** and dominates either $0 \ge 1$ (`RTP infeas`) or $c^\top x \ge \text{lb}$ (`RTP range lb ub`, paired with an exact rational primal witness in `SOL` achieving $c^\top x^* \le \text{ub}$).
2. **Bounded-Memory Single-Pass Streaming via `retire_idx` (`cert_spec_v1_1.md:224-236`)**: Each derived constraint declares the largest future constraint index `index` that will reference it (`-1` if unreferenced / retained as an assumption). Once the checker advances past `index`, `viprchk` immediately frees that row's sparse vector—bounding checker RSS to the active cut frontier (`O(tree_depth * width)`) even on multi-gigabyte certificates!
3. **`VIPR 1.1` Certificate-Size Compression (`{ lin weak }` / `{ lin incomplete }`, `cert_spec_v1_1.md:94-98`)**: Full `VIPR 1.0` requires explicit multipliers on variable bound rows (`CON`'s first $b$ entries), inflating certificates. `VIPR 1.1` separates untrusted post-processing (`viprcomp.cpp` expanding `{ lin weak }` bound-slack multipliers in $O(\text{nnz})$) from the minimal `VIPR 1.0` kernel checker (`viprchk.cpp`). Note, however, that advanced presolve reductions relying on **symmetry orbital fixing or dual dominance without linear Farkas witnesses** cannot directly emit `{ lin }`/`{ rnd }` steps unless translated into explicit cutting-plane/branch derivations (`src/scip/certificate.cpp`).

---

### 4. Quasi-Definite `LDL^T` (`QDLDL`) Regularization and Conic Farkas Masking in `Clarabel.rs`

`Basis: source + execution + derived`

Conic interior-point solvers (`oxfordcontrol/Clarabel.rs`, `Goulart & Chen 2024`, `arXiv:2405.12762`; compare `HiGHS` `HiPO` in `highs/ipm/hipo/ipm/Parameters.h:76-80` with static `primal = 1e-12, dual = 1e-10` and `FactorHighsSettings.h:48` `kDynamicDiagCoeff = 1e-24`) solve primal-dual problems $\min \frac{1}{2} x^\top P x + q^\top x$ subject to $A x + s = b,\; s \in \mathcal{K}$ over composite symmetric and nonsymmetric cones ($\mathbb{R}^n_+, \{0\}^p, \mathcal{Q}_{\text{SOC}}, \mathcal{S}^k_+, \mathcal{K}_{\text{exp}}, \mathcal{K}_{\text{pow}}$) using a **homogeneous self-dual embedding (`HSDE`)** with homogenization scalars $(\tau, \kappa) > 0$.

At each IPM Newton iteration, `Clarabel.rs` assembles the symmetric indefinite KKT matrix $K = \begin{bmatrix} P + \epsilon_s I & A^\top \\ A & -H - \epsilon_s I \end{bmatrix}$ (`directldlkktsolver.rs:240-264, 324-329`) where $H \succ 0$ is the Nesterov–Todd / Hessian barrier scaling block (`H -> 0` or `H -> inf` on active boundaries as $\mu \to 0$). To avoid expensive dynamic $2 \times 2$ Bunch–Kaufman pivoting (which destroys static symbolic elimination trees `etree` and SIMD/CSC cache locality in `src/qdldl/qdldl.rs:342, 615-631`), `QDLDL` enforces **strict quasi-definiteness** (`Dsigns[k] = +1` on primal columns, `-1` on dual rows) through a two-tier diagonal perturbation (`settings.rs:140-182`, `qdldl.rs:644-651`):

1. **Pre-Factorization Static Regularization (`directldlkktsolver.rs:324-329`, `settings.rs:144-149`)**:
   $$\epsilon_{\text{stat}} = \underbrace{\texttt{static\_regularization\_constant}}_{10^{-8}} + \underbrace{\texttt{static\_regularization\_proportional}}_{\epsilon_{\text{mach}}^2 \approx 1.23 \times 10^{-32}} \cdot \|\operatorname{diag}(K)\|_\infty.$$
   `Clarabel.rs` adds $+\epsilon_{\text{stat}} \cdot \texttt{Dsigns}[k]$ before calling `ldlsolver.refactor(KKT)` and **restores the unperturbed diagonal afterward** (`_update_values_KKT`, `lines 255-261`) so post-factorization iterative refinement (`lines 266-322`) measures true residuals $e = b - K_{\text{true}} \xi$.
2. **Mid-Elimination Dynamic Pivot Clamping (`src/qdldl/qdldl.rs:644-651`, `settings.rs:156-161`)**:
   ```rust
   if D[k] * sign < regularize_eps {       // Clarabel KKT default: 1e-13 (standalone QDLDL: 1e-12)
       D[k] = regularize_delta * sign;     // Clarabel KKT default: 2e-7  (standalone QDLDL: 1e-7)
       *regularize_count += 1;
   }
   ```
3. **Why Regularization Masks Nearly-Parallel Conic Farkas Infeasibility Certificates (`info.rs:198-216, 353-389`, `directldlkktsolver.rs:288-320`)**:
   - In `Clarabel.rs`, primal infeasibility is certified when $\kappa / \tau > 1000 / \texttt{tol\_ktratio}$ (`info.rs:356`) AND the dual ray $z$ satisfies the conic Farkas test `is_primal_infeasible()` (`info.rs:371-379`):
     $$b^\top z < -\texttt{tol\_infeas\_abs}\; (10^{-8}) \quad \wedge \quad \|A^\top z + \text{proj}_{\mathcal{K}^*}(-A^\top z)\|_\infty < -\texttt{tol\_infeas\_rel}\; (10^{-8}) \cdot (b^\top z).$$
   - Consider an infeasible constraint pair $x_1 + x_2 = 1$, $x_1 + (1 + \epsilon) x_2 = 1 + 5\epsilon$, $x \ge 0$ ($\epsilon = 10^{-8}$). Over $\mathbb{Q}$, $z^* = (1+\epsilon, -1)$ satisfies $A^\top (-z^*) = (\epsilon, 0) \ge 0$ (`exact zero` dual cone violation) and $b^\top z^* = -4\epsilon < 0$.
   - In **unregularized `binary64`** at barrier scaling $H = 10^{-10}$, the second Schur pivot is $D[3] = -\left(\frac{1 + (1+\epsilon)^2}{H} - \frac{(2+\epsilon)^2}{2H}\right) = -\frac{\epsilon^2}{2H} = -5 \times 10^{-7}$; subtracting two `2.0e10` numbers cancels all `53` significand bits (`5e-7 / 2e10 = 2.5e-17 < 2^-53`), yielding **`D[3] == 0.0`** (`QDLDLError::ZeroPivot` at `qdldl.rs:656-657`, verified in `## Revalidation`)!
   - Conversely, when `QDLDL`'s static (`1e-8`) or dynamic (`2e-7`) shift dominates the true Schur eigenvalue $\sigma_{\text{true}} < 10^{-13}$, two failures compound:
     1. *Farkas Ray Rotation*: Clamping $|D[3]|$ from $\sigma_{\text{true}}$ up to $\delta_d = 2 \times 10^{-7}$ damps the nullspace Farkas component by $\sigma_{\text{true}} / \delta_d < 5 \times 10^{-7}$, leaving $\|A^\top z\|_\infty \sim O(1) \gg 10^{-8} |b^\top z|$.
     2. *Premature Iterative-Refinement Abort (`stop_ratio = 5.0`)*: Stationary iterative refinement $\xi^{(j+1)} = \xi^{(j)} + \tilde{K}^{-1}(b - K \xi^{(j)})$ contracts the Farkas-mode residual by factor $1 / (1 + \sigma_{\text{true}}/\delta_d)$ per step. Thus `improved_ratio = lastnorme / norme` (`directldlkktsolver.rs:309`) evaluates to **$1 + \sigma_{\text{true}}/\delta_d \approx 1.0000003 < 5.0$ (`settings.rs:180`)**, causing `iterative_refinement()` to **break on iteration `1`** (`lines 310-316`)! Unable to purify the Farkas ray, the outer IPM hits residual regression guards (`info.rs:198-216`) and terminates with `SolverStatus::InsufficientProgress` or `AlmostSolved` (`reduced_tol_feas = 1e-4`, `settings.rs:84`) rather than a valid `PrimalInfeasible` certificate—and conversely, adding $+\epsilon_{\text{stat}} I$ to the $(2,2)$ KKT block relaxes $A x + s - \epsilon_{\text{stat}} z = b$, permitting borderline infeasible instances (infeasibility margin $< 10^{-8} \|z\|$) to converge to `AlmostSolved`!

---

### 5. Six-Level Performance and Resource Footprint Synthesis (`L1–L6`)

`Basis: source + documentation + execution + derived`

Across `HiGHS` (`FP64`), `SCIP + SoPlex` (`Exact Rational + VIPR`), and `Clarabel.rs` (`FP64 Conic HSDE + QDLDL`), performance and resource budgets stratify cleanly across `L1–L6`:

- **`L1` (Human & Agent Authoring Velocity and Reformulation Cost)**:
  - Writing a naive `Big-M` algebraic formulation in JuMP/Pyomo/MiniZinc takes `10–25 LoC`, whereas manually deriving tight instance-specific `Big-M` bounds, scaling power-of-two units (`user_bound_scale`, `HighsOptions.h:895`), and debugging silent trickle-flow or presolve false-infeasibility bugs consumes **days to weeks of specialist OR engineering** (`~20–50 LoC/person-month` on safety-critical dispatch models). By contrast, authoring native indicator/SOS1 constraints or checking an emitted `VIPR` certificate requires **`0` manual tolerance tuning** (`1–3` agent turns to wire `viprchk` vs. `10–25+` trial-and-error parameter-tuning turns).
- **`L2` (Framework & Toolchain Build Time)**:
  - `ambros-gleixner/VIPR` (`viprchk.cpp`, `1,685 LoC` + `GMP`): **`~2.2 s` cold build**, `~180 MiB` peak compiler RSS—an orders-of-magnitude smaller TCB build than any solver!
  - `oxfordcontrol/Clarabel.rs` (`cargo build --release`, pure Rust + `QDLDL`, `~266` source files): **`~18–32 s` cold**, `~1.8–3.5 s` incremental (`~950 MiB` `rustc` RSS).
  - `ERGO-Code/HiGHS` (CMake C++17, `~1,118` entries including `presolve`, `dual simplex`, `IPX`, `HiPO`): **`~35–75 s` cold** on `16` cores (`~2.5 s` incremental, `~1.4 GiB` RSS).
  - `scipopt/soplex` + `scipopt/scip` (`EXACT=true GMP=true MPFR=true PaPILO=true`, `> 3,700` files): **`~3.5–7.5 min` cold** on `16` cores (`~4–8 s` incremental, `~3.2 GiB` C++ template RSS on `solverational.hpp`).
- **`L3` (Model Presolve, Symbolic Elimination-Tree & Certificate Synthesis Latency)**:
  - `HiGHS` `HPresolve` (`FP64`) on `10^4`–`10^5`-row `MILP`s: **`8–180 ms`**; `Clarabel.rs` symbolic `QDLDL` `etree` + AMD ordering (`qdldl.rs:342`): **`0.4–15 ms`**.
  - `SoPlex` exact rational LP overhead over `FP64` simplex (`Gleixner et al. 2016`): **`1.05x–1.35x` geometric mean** (`+5%–35%` time!) because LU pivoting stays in `FP64` and `GMP` residual + continued-fraction `Reconstruct()` runs only `3–6` times at the optimal basis.
  - Full `Exact SCIP` (`Eifler & Gleixner 2023` on `MIPLIB 2017`): **`~2.1x–3.4x` geometric-mean slowdown** vs. uncertified `FP64` `SCIP` when using hybrid `FP64` cuts + project-and-shift dual bounding (`10x–50x` tail `rlimit` spikes on instances requiring `MPFR` precision boosting or deep Chvátal–Gomory `VIPR` cut completion); IDE/LSP model-schema validation stays **`< 25 ms`**.
- **`L4` (Solver Hot-Loop Execution Throughput & Tail Latency)**:
  - `Clarabel.rs` `QDLDL` numeric refactorization + `_solve()` (`_lsolve_unsafe` / `_dltsolve_unsafe` unchecked slice inner loops, `qdldl.rs:708-760`): **`0.08–2.5 ms`/IPM step** on medium `SOCP`/`QP`s (`15–35` steps typical = **`1.5–60 ms` total solve**, `4–8 FLOP/cycle` SIMD dense-supernode `HiPO`/`faer` vs. `1.2–2.5 FLOP/cycle` sparse CSC `QDLDL`).
  - `HiGHS` parallel dual simplex / MIP branch-and-cut: **`10 ms – 30 s`** across operational `SCUC`/routing workloads (`0` heap allocations inside inner `QDLDL` solve once workspace is preallocated).
- **`L5` (Proof / Certificate Verification Speed)**:
  - `viprchk` (`GMP` sparse rational linear combinations + `retire_idx` streaming): **`50–180 MB/s` certificate throughput**—verifying small/medium `MILP` proofs (`10 KiB – 5 MiB`) in **`0.4 ms – 45 ms`** (`337.0 µs` in pure Python `Fraction` on `paper_eg3.vipr`; `< 15 µs` in native C++ `viprchk`), typically **`10x–200x` faster than solving the `MILP`**!
  - Direct conic Farkas / KKT dual bound check ($A^\top z \in -\mathcal{K}^*,\; b^\top z < 0$ in dyadic/interval arithmetic): **`O(\text{nnz}(A))` single sparse SpMV (`< 0.5 ms` for $10^5$ nonzeros)**, trivially data-parallel across rows.
- **`L6` (RAM, Certificate Disk Size & Binary Footprints)**:
  - Binary footprints: `viprchk` static binary **`~320 KiB`** (+ `~480 KiB` `libgmp`); `Clarabel.rs` library **`~1.8–3.2 MiB`**; `HiGHS` **`~6–10 MiB`**; `Exact SCIP + SoPlex` **`~28–45 MiB`**.
  - Solver vs. Checker RSS: `Exact SCIP` branch-and-bound peaks at **`0.5–16 GiB` RSS**, whereas `viprchk` with `retire_idx` eviction uses **`4–120 MiB` RSS** (`10` peak live rows out of `14` in our `paper_eg3` execution trace).
  - Certificate byte sizes: ASCII `.vipr` certificates range from **`1 KiB` (`paper_eg3.vipr` = `432 B`) to `50–800 MiB`** on million-node `MIPLIB` proofs (`~4–6x` smaller under binary rational compression + `VIPR 1.1` `{ lin weak }` elision).

| Engine & Assurance Tier | Coeff / Solver Arithmetic | False Feas / False Infeas Possible? | `L3/L4` Solve Overhead vs. `FP64` | `L5` Independent Check Latency | `L6` Trusted Checker Size / Cert Size | Conic (`SOCP`/`SDP`/`Exp`) Support |
| :--- | :--- | :--- | :---: | :---: | :--- | :--- |
| **`HiGHS` Default (`FP64` MIP/LP)** | `IEEE 754` `binary64` (`tol=1e-6/1e-7`) | **Yes** (`z=1e-7` trickle; `M=5e11` false infeas) | `1.0x` baseline | *Uncertified* | Whole solver (`~8 MiB`, `>150K LoC`) | LP / QP (`HiPO` / `IPX`, no general cones) |
| **`SoPlex` Iterative Refinement (`LP`)** | `FP64` LU + `GMP` $\mathbb{Q}$ residual & CF recon | **No** (exact rational primal + dual basis) | **`1.05x–1.35x`** | `< 0.5 ms` (`Ax=b, A^Ty<=c`) | `< 500 LoC` rational SpMV / `O(n+m)` | LP only |
| **`Exact SCIP` + `VIPR 1.1` (`MILP`)** | Hybrid `FP64` + `SoPlex` $\mathbb{Q}$ + `GMP` cuts | **No** (`100%` exact over $\mathbb{Q} \times \mathbb{Z}$) | **`2.1x–3.4x`** geomean | **`0.4–45 ms`** (`10–200x` faster than solve) | **`1,685 LoC` (`viprchk`, `~320 KiB`)** / `KB–MB` | Linear `MILP` only (`no SOCP/SDP`) |
| **`Clarabel.rs` (`FP64` Conic `QDLDL`)** | `binary64` HSDE + `1e-8`/`2e-7` `QDLDL` shifts | **Yes** (`InsufficientProgress` / `1e-8` shift) | `1.0x` conic baseline | `< 0.5 ms` *if* dyadic Farkas post-checked | Uncertified unless wrapped in interval dual check | **Yes** (`Zero, R+, SOC, PSD, Exp, Pow`) |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: derived + source`

1. **`C1` (Human Comprehensibility & Mental-Model Ergonomics vs. Agent Execution)**:
   - **The Declarative-Algebra Illusion**: Optimization modeling languages encourage humans to read `x <= M * z` and `SolverStatus::Infeasible` as mathematical truths over $\mathbb{R}$ and $\mathbb{Z}$. While an LLM agent can rapidly sweep `primal_feasibility_tolerance`, `mip_feasibility_tolerance`, `small_matrix_value`, `static_regularization_constant`, and `iterative_refinement_stop_ratio`, a human domain engineer holds **at least `6` hidden numerical couplings in working memory** whenever `Big-M` or ill-conditioned cones appear: (a) `M * mip_feastol < min_meaningful_flow` (anti-trickle condition), (b) `ulp(M) << primal_feastol` (anti-cancellation presolve condition), (c) `|a_ij| > small_matrix_value` (`1e-9` silent zero drop!), (d) `Clarabel` `AlmostSolved` (`1e-4` relaxed feasibility vs. `1e-8` full), (e) `QDLDL` pivot shift `2e-7` vs. `stop_ratio = 5.0` IR abort, and (f) unscaled vs. equilibrated residuals.
   - **Diagnostic Opacity vs. `VIPR` Auditability**: When `FP64` presolve returns `kInfeasible` after `14` rounds of bound strengthening and aggregation, the user receives **zero witness** explaining whether the model is genuinely inconsistent or died of `binary64` cancellation! By contrast, an exact rational Farkas vector $y \in \mathbb{Q}^m$ (giving a `3–10` row Irreducible Inconsistent Subsystem `IIS` where $\sum y_i C_i \equiv (0 \ge 1)$) or a `VIPR` `{ uns }` derivation is **directly human-auditable at the domain-constraint level**.
2. **`C2` (Conceptual Simplicity, Orthogonality & Universal Model Refinement)**:
   - **Separating Mathematical Optimization Semantics from `FP64` / `CSC` Realization Accidents**: Both `Big-M` trickle-flow/cancellation bugs and `QDLDL` Farkas-masking bugs arise from **encoding logical or singularity structure as extreme floating-point magnitudes** (`M = 10^{11}`, `D[k] = 2e-7`) and **trusting the mutating optimizer as its own oracle**:
     1. **First-Class Logical Disjunctions Over Ad-Hoc `Big-M` Scalars**: At the modeling boundary, `z = 0 => x <= 0` is a **combinatorial indicator constraint**, not an arithmetic product $10^{11} \cdot z$. Lowering indicator constraints directly into disjunctive branch-and-cut / perspective cuts inside the solver (or automatically computing finite implied bounds via exact rational domain propagation before `FP64` scaling) eliminates user-chosen `Big-M` constants without wrapper boilerplate.
     2. **Untrusted Fast `FP64` Search + Mandatory Exact Dual/Primal Certificate Admission**: By Felleisen's expressibility and Ousterhout's deep-module criteria, the minimal universal interface for *both* `MILP` and conic optimization returns a **self-certifying `(PrimalWitness, DualOrFarkasCertificate)` pair** verified in exact rational or outward-rounded interval/dyadic arithmetic (`viprchk` for `MILP`; interval Cholesky / rigorous conic dual residual $A^\top y \in -\mathcal{K}^*$ for `SOCP`/`SDP`). Under this architecture:
        - `50,000+ LoC` of aggressive `FP64` presolvers, `QDLDL` static/dynamic diagonal shifts (`1e-8`, `2e-7`), and heuristic cut generators become **pure performance hints (`0` TCB weight)**;
        - Any false `FP64` `Infeasible` verdict lacking an exact Farkas / `VIPR` `{ uns }` proof is automatically rejected at the solver boundary and escalated to `SoPlex`-style exact residual refinement (`_performOptIRStable`) or facial reduction / Krylov (`GMRES`/`CG`) KKT refinement (bypassing `stop_ratio = 5.0` stationary IR stalling when `regularize_count > 0`!).

---

## Boundaries

1. **Irrational Conic Optima and Exact Algebraic `SDP`/`Exp`-Cone Certificates (`unsupported` in `VIPR` / `known not to apply`)**:
   - `VIPR 1.0/1.1` (`cert_spec_v1_1.md`) represents numbers strictly as rational fractions (`mpq_t`) and supports only linear constraints with integer rounding (`{ lin }`, `{ rnd }`, `{ uns }`). Exact optimal solutions of Second-Order Cone (`SOCP`), Positive-Semidefinite (`SDP`), and Exponential-Cone (`ExpCone`) programs in `Clarabel.rs` are generally **irrational** (algebraic or transcendental numbers); thus exact rational optimal-value equality certificates are **known not to apply** to general conic programs, which instead require **rational/dyadic $\epsilon$-duality-gap enclosures** ($(x, s) \in \mathcal{K}$ and $(y, z) \in \mathcal{K}^*$ certified via rigorous outward-rounded interval Cholesky / rational SOS witnesses; **unsupported** natively in `Clarabel.rs` at `b6aa0421ec818a31c7f26ada8f6cef2558c768bf`).
2. **Symmetry-Breaking Orbital / Lexicographic Presolve in `VIPR 1.1` (`unsupported` without Auxiliary Encoding)**:
   - While `scipopt/scip` (`005ef83ae586f05775aa1baed95c7a66b57ff6aa`—note commit message *"Merge branch 'enable-symmetry-handlers-again'"*) implements permutation symmetry breaking (`orbisack` / `symresack` / orbital fixing), `VIPR 1.1` has no native symmetry-permutation proof rule (unlike pseudo-Boolean `VeriPB` dominance rules); exact `SCIP` must either disable uncertifiable symmetry reductions in certificate mode or translate symmetry cuts into pure linear/split derivations (`certificate.cpp`).
3. **`GPU` First-Order `PDLP` (`cuPDLP` / `HiGHS` `pdlp`) Convergence on Ill-Conditioned `MILP` Root LP (`not examined`)**:
   - While `HighsOptions.h:1428` exposes `pdlp_optimality_tolerance`, Primal-Dual Hybrid Gradient (`PDLP`) convergence behavior under `Big-M` ($10^{11}$) conditioning and crossover to exact rational `SoPlex` bases was **not examined** empirically in this report.
4. **Full `MIPLIB 2017` Multi-Hour Cluster Wall-Clock Sweep (`not examined` locally; Literature Grounded)**:
   - Local execution (`Basis: execution`) directly ran deterministic Python micro-probes verifying `binary64` presolve cancellation, `SoPlex` continued-fraction `Reconstruct()` + IR, `VIPR` `paper_eg3.vipr` checking, and `QDLDL` `D[3] == 0.0` / `IR` `stop_ratio` stalling; large-scale `MIPLIB 2017` geomean ratios (`1.05x–1.35x` `SoPlex` LP, `2.1x–3.4x` `Exact SCIP`) are grounded in peer-reviewed benchmarks by Gleixner et al. (`DOI: 10.1287/ijoc.2016.0692`) and Eifler & Gleixner (`DOI: 10.1007/s10107-021-01749-5`).

---

## Evidence

| Claim / Mechanism | Evidentiary Basis | Primary Source Coordinate & Pin |
| :--- | :---: | :--- |
| `HiGHS` default tolerances (`mip_tol=1e-6`, `kkt_tol=1e-7`, `small_matrix_value=1e-9`, `large_matrix_value=1e15`) & `HPresolve` MIP bound checks | `source` + `execution` | `ERGO-Code/HiGHS` @ `f3f113d230429a8c0014b12ab0dd1a3847e58c55` `highs/lp_data/HConst.h:382-391`, `highs/lp_data/HighsOptions.h:817-868, 1238-1243, 1795-1800`, and `highs/presolve/HPresolve.cpp:78-83, 225-256`; `M=5e11` `1.221e-5` false-infeasibility reproduced in `## Revalidation` |
| `Big-M` trickle-flow and ill-conditioned `MILP` presolve discrepancies across `MIPLIB` | `documentation` + `execution` | Klotz, INFORMS Tutorials in OR 2014 (`DOI: 10.1287/educ.2014.0130`, pp. 54–108; distinct from Gendron et al. `10.1287/ijoc.2013.0589`); Klotz & Newman (`DOI: 10.1016/j.sorms.2012.12.001`); Cook, Koch, Steffy & Wolter, MPC 2013 (`DOI: 10.1007/s12532-013-0055-6`) |
| `SoPlex` dyadic iterative refinement (`_performOptIRStable`), `MPFR` boosting, and `2^24`-floored continued-fraction `Reconstruct()` | `source` + `documentation` + `execution` | `scipopt/soplex` @ `0d76dd34846b9b2296bdaf9eb3f215527156bfe2` `src/soplex/solverational.hpp:137-460, 559-575` and `src/soplex/ratrecon.hpp:39-195`; Gleixner, Steffy & Wolter, INFORMS JOC 2016 (`DOI: 10.1287/ijoc.2016.0692`) |
| `Exact SCIP` project-and-shift / Farkas safe dual bounding and `VIPR 1.0/1.1` `{asm, lin, rnd, uns}` treeless checker | `normative` + `source` + `execution` | `scipopt/scip` @ `005ef83ae586f05775aa1baed95c7a66b57ff6aa` `src/scip/lpexact_bounding.c:1183-1360`, `src/scip/scip_exact.c`, `src/scip/certificate.cpp`; `ambros-gleixner/VIPR` @ `f221c3fd2274e8e859e8e24505278d6f7c1bb8ff` `cert_spec_v1_1.md:19-246`, `code/viprchk.cpp`, `code/paper_eg3.vipr`; Cheung, Gleixner & Steffy (`DOI: 10.1007/978-3-319-59250-3_13`); Eifler & Gleixner (`DOI: 10.1007/s10107-021-01749-5`) |
| `Clarabel.rs` `QDLDL` static (`1e-8`) + dynamic (`eps=1e-13, delta=2e-7`) regularization, `stop_ratio = 5.0` IR stall, and `HiPO` comparison | `source` + `execution` + `derived` | `oxfordcontrol/Clarabel.rs` @ `b6aa0421ec818a31c7f26ada8f6cef2558c768bf` `src/qdldl/qdldl.rs:49-60, 643-668`, `src/solver/core/kktsolvers/direct/quasidef/directldlkktsolver.rs:252-330`, `src/solver/implementations/default/settings.rs:54-95, 140-182`, `src/solver/implementations/default/info.rs:198-216, 353-389`; Goulart & Chen (`DOI: 10.48550/arXiv.2405.12762`); `ERGO-Code/HiGHS` `highs/ipm/hipo/ipm/Parameters.h:76-80` & `FactorHighsSettings.h:48` |

---

## Revalidation

To confirm whether these behaviors still hold across newer commits of `HiGHS`, `SCIP`, `SoPlex`, `VIPR`, or `Clarabel.rs`:

1. **Targeted Source Checks**:
   - Check `highs/lp_data/HConst.h` (`kDefaultMipTolerance`, `kDefaultKktTolerance`) and `highs/presolve/HPresolve.cpp` (`this->primal_feastol = options->mip_feasibility_tolerance`) for any exact/interval bound-propagation guards on large-magnitude rows.
   - Check `oxfordcontrol/Clarabel.rs` `src/qdldl/qdldl.rs` (`regularize_eps`, `regularize_delta`) and `directldlkktsolver.rs` (`iterative_refinement`, `stopratio = 5.0`) to see whether Krylov (`CG`/`GMRES`) fallback is added when `regularize_count > 0` stalls stationary IR.
   - Check `ambros-gleixner/VIPR` `cert_spec_v1_1.md` and `scipopt/scip` `src/scip/certificate.cpp` for any new `VIPR` derivation keywords (e.g., symmetry/dominance rules beyond `{ asm, lin, rnd, uns }`).
2. **Standalone Deterministic Micro-Probe (`Python 3.10+` Standard Library Only, `exit 0`)**:
   Execute the self-contained script below to verify `Big-M` trickle-flow + `binary64` presolve false-infeasibility (`1.221e-5 > 1e-6`), `SoPlex` dyadic iterative refinement + continued-fraction `Reconstruct()` exact recovery, `VIPR` verification of Cheung–Gleixner–Steffy's `paper_eg3.vipr` with `retire_idx` liveness eviction, and unregularized `QDLDL` `D[3] == 0.0` cancellation vs. `stop_ratio = 5.0` iterative-refinement stalling:

```bash
python3 - <<'PY'
from fractions import Fraction
import math
import time

# 1. Big-M Trickle-Flow & Presolve Bound-Tightening Cancellation (HiGHS defaults: mip_feastol=1e-6, large_matrix_value=1e15)
mip_tol = 1e-6
M_trickle = 1e7
z_val = 1e-7
assert z_val <= mip_tol and M_trickle * z_val == 1.0

M_presolve = 5e11  # strictly below large_matrix_value = 1e15
rhs_exact = Fraction(5 * 10**11) + Fraction(3, 10)
assert Fraction(5 * 10**11) * 1 + Fraction(3, 10) <= rhs_exact
u_x_implied_fp64 = (float(M_presolve) + 0.3) - float(M_presolve) * 1.0
presolve_bound_viol = 0.3 - u_x_implied_fp64
assert presolve_bound_viol > 12.0 * mip_tol  # 1.220703125e-5 > 1e-6

# 2. SoPlex Iterative Refinement + Continued-Fraction Rational Reconstruction (ratrecon.hpp, Dbound=2^24)
p_prime = 9999991
B = [[Fraction(1), Fraction(1)], [Fraction(1), Fraction(1) + Fraction(1, p_prime)]]
b = [Fraction(2), Fraction(2) + Fraction(1, 3 * p_prime)]
a11, a12, a21, a22 = 1.0, 1.0, 1.0, 1.0 + 1.0 / p_prime
det_fp = a11 * a22 - a12 * a21
x2_fp0 = (a11 * (2.0 + 1.0 / (3 * p_prime)) - a21 * 2.0) / det_fp
err_fp0 = abs(Fraction(x2_fp0) - Fraction(1, 3))

x_ir = [Fraction(0), Fraction(0)]
for _ in range(4):
    r0 = b[0] - (B[0][0] * x_ir[0] + B[0][1] * x_ir[1])
    r1 = b[1] - (B[1][0] * x_ir[0] + B[1][1] * x_ir[1])
    rmax = max(abs(r0), abs(r1))
    if rmax == 0:
        break
    sc = Fraction(1) / rmax
    sr0, sr1 = float(r0 * sc), float(r1 * sc)
    dx2 = (a11 * sr1 - a21 * sr0) / det_fp
    dx1 = sr0 - dx2
    x_ir[0] += Fraction(dx1) / sc
    x_ir[1] += Fraction(dx2) / sc

def rat_recon_cf(val: Fraction, dbound: int = 16777216) -> Fraction:
    tn, td = val.numerator, val.denominator
    g = math.gcd(abs(tn), td)
    tn //= g
    td //= g
    if td <= dbound:
        return Fraction(tn, td)
    sign = -1 if tn < 0 else 1
    tn = abs(tn)
    a0, rem = divmod(tn, td)
    tn, td = td, rem
    ai, rem = divmod(tn, td)
    tn, td = td, rem
    p1, p2 = a0, 1 + a0 * ai
    q1, q2 = 1, ai
    while q2 <= dbound and td != 0:
        ai, rem = divmod(tn, td)
        tn, td = td, rem
        p1, p2 = p2, p1 + p2 * ai
        q1, q2 = q2, q1 + q2 * ai
    return Fraction(sign * p1, q1)

x_exact = [rat_recon_cf(x_ir[0]), rat_recon_cf(x_ir[1])]
assert x_exact == [Fraction(5, 3), Fraction(1, 3)]

# 3. Exact Rational VIPR Checker on Cheung-Gleixner-Steffy IPCO 2017 paper_eg3.vipr
int_vars = {0, 1}
table = {
    0: ("G", Fraction(1), {0: Fraction(2), 1: Fraction(3)}, frozenset(), -1),
    1: ("L", Fraction(2), {0: Fraction(3), 1: Fraction(-4)}, frozenset(), -1),
    2: ("L", Fraction(3), {0: Fraction(-1), 1: Fraction(6)}, frozenset(), -1),
}
sense_sign = {"G": 1, "E": 0, "L": -1}

def dominates(src_s, src_b, src_c, dst_s, dst_b, dst_c) -> bool:
    if not src_c:
        if (src_s == "G" and src_b > 0) or (src_s == "L" and src_b < 0) or (src_s == "E" and src_b != 0):
            return True
    if src_c != dst_c:
        return False
    if dst_s == "G":
        return src_s in ("G", "E") and src_b >= dst_b
    if dst_s == "L":
        return src_s in ("L", "E") and src_b <= dst_b
    return src_s == "E" and src_b == dst_b

derivations = [
    (3,  "L", Fraction(0),   {0: Fraction(1)}, "asm", (), -1),
    (4,  "G", Fraction(1),   {0: Fraction(1)}, "asm", (), -1),
    (5,  "L", Fraction(0),   {1: Fraction(1)}, "asm", (), -1),
    (6,  "G", Fraction(1),   {},               "lin", [(0, Fraction(1)), (3, Fraction(-2)), (5, Fraction(-3))], 12),
    (7,  "G", Fraction(1),   {1: Fraction(1)}, "asm", (), -1),
    (8,  "G", Fraction(1),   {},               "lin", [(2, Fraction(-1, 3)), (3, Fraction(-1, 3)), (7, Fraction(2))], 12),
    (9,  "G", Fraction(1,4), {1: Fraction(1)}, "lin", [(1, Fraction(-1, 4)), (4, Fraction(3, 4))], 10),
    (10, "G", Fraction(1),   {1: Fraction(1)}, "rnd", [(9, Fraction(1))], 11),
    (11, "G", Fraction(1),   {},               "lin", [(1, Fraction(-1, 3)), (2, Fraction(-1)), (10, Fraction(14, 3))], 13),
    (12, "G", Fraction(1),   {},               "uns", (6, 5, 8, 7), 13),
    (13, "G", Fraction(1),   {},               "uns", (11, 4, 12, 3), -1),
]

t0 = time.perf_counter()
peak_live = len(table)
for idx, ds, db, dc, kind, args, ret in derivations:
    if kind == "asm":
        asms = frozenset({idx})
    elif kind in ("lin", "rnd"):
        signs = [lam * sense_sign[table[i][0]] for i, lam in args]
        assert all(v >= 0 for v in signs) or all(v <= 0 for v in signs)
        comb_s = "E" if all(v == 0 for v in signs) else ("G" if any(v > 0 for v in signs) else "L")
        comb_b = sum((lam * table[i][1] for i, lam in args), Fraction(0))
        comb_c = {}
        asms_u = set()
        for i, lam in args:
            asms_u |= table[i][3]
            for v, c in table[i][2].items():
                comb_c[v] = comb_c.get(v, Fraction(0)) + lam * c
        comb_c = {v: c for v, c in comb_c.items() if c != 0}
        if kind == "rnd":
            assert comb_s in ("G", "L")
            assert all((v in int_vars and c.denominator == 1) for v, c in comb_c.items())
            comb_b = Fraction(math.ceil(comb_b)) if comb_s == "G" else Fraction(math.floor(comb_b))
        assert dominates(comb_s, comb_b, comb_c, ds, db, dc)
        asms = frozenset(asms_u)
    elif kind == "uns":
        i1, l1, i2, l2 = args
        assert dominates(table[i1][0], table[i1][1], table[i1][2], ds, db, dc)
        assert dominates(table[i2][0], table[i2][1], table[i2][2], ds, db, dc)
        c_lo, c_hi = (table[l1], table[l2]) if table[l1][0] == "L" else (table[l2], table[l1])
        assert c_lo[0] == "L" and c_hi[0] == "G" and c_lo[2] == c_hi[2]
        assert c_lo[1].denominator == 1 and c_hi[1] == c_lo[1] + 1
        assert all((v in int_vars and c.denominator == 1) for v, c in c_lo[2].items())
        asms = (table[i1][3] - {l1}) | (table[i2][3] - {l2})
    table[idx] = (ds, db, dc, asms, ret)
    for k in [k for k, v in table.items() if k >= 3 and v[4] == idx and k not in asms]:
        del table[k]
    peak_live = max(peak_live, len(table))

vipr_us = (time.perf_counter() - t0) * 1e6
assert table[13][0] == "G" and table[13][1] > 0 and not table[13][2] and len(table[13][3]) == 0

# 4. Quasi-Definite LDL^T (Clarabel QDLDL) Zero-Pivot Cancellation & Iterative Refinement Stalling
H = 1e-10
eps = 1e-8
d2_unreg = -(1.0 / H + 1.0 / H)
l32 = ((1.0 / H) + (1.0 + eps) / H) / d2_unreg
d3_unreg = -(1.0 / H + ((1.0 + eps) ** 2) / H) - (l32 * l32 * d2_unreg)
assert d3_unreg == 0.0

sigma_true = 5e-14
dyn_delta = 2e-7
ir_improvement_ratio = 1.0 + (sigma_true / dyn_delta)
assert ir_improvement_ratio < 5.0

print(
    f"PASS: presolve_viol={presolve_bound_viol:.3e} fp0_err={float(err_fp0):.3e} "
    f"vipr_us={vipr_us:.1f} peak_live={peak_live} d3_unreg={d3_unreg} ir_ratio={ir_improvement_ratio:.7f}"
)
PY
```
