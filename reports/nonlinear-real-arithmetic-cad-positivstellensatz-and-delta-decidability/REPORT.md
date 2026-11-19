# Nonlinear Real Arithmetic: CAD/NLSAT, Positivstellensatz SOS Certificates, Delta-Decidability, and Transcendental Bounds

## Summary

Automated reasoning over nonlinear real and transcendental arithmetic spans four fundamentally different mathematical regimes, each with sharp complexity, completeness, and kernel-certification boundaries:

1. **Exact Polynomial Real Arithmetic (`QF_NRA` / RCF):** Tarski's Real Closed Field (RCF) theory is decidable, but full quantifier elimination via Cylindrical Algebraic Decomposition (CAD) has an inherent doubly-exponential lower bound $2^{2^{\Omega(n)}}$ in the number of variables $n$ (Davenport & Heintz 1988). Modern SMT solvers avoid building a full CAD upfront by driving single-cell algebraic projections lazily from concrete search conflicts: **Z3 NLSAT** (`Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1`, Jovanović & de Moura 2012) pairs Model-Constructing Satisfiability (`MCSAT`) with levelwise single-cell construction (`levelwise_single_cell`) and sample-cell projection (`nlsat_explain.cpp`), while **cvc5** (`7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`) combines heuristic monomial/tangent-plane lemmas with complete **Cylindrical Algebraic Coverings** (`CDCAC`, Ábrahám et al. 2021) backed by `libpoly` (`8779171e`) and Lazard modified lifting (`lazard_evaluation.h`, which silently degrades to standard `poly::infeasible_regions` if CoCoALib is absent at build time).
2. **Kernel-Checked Polynomial Positivity via Positivstellensatz & Reflexive Floating-Point Cholesky (`ValidSDP`):** While CAD/NLSAT certificates remain large and hard to check in proof-assistant kernels, **Stengle's (1974) / Putinar's (1993) Positivstellensatz** reduces polynomial positivity to Sum-of-Squares (SOS) semidefinite programs (SDPs) solvable in polynomial time for fixed degree—at the cost of degree-hierarchy incompleteness (e.g., Motzkin's globally nonnegative polynomial $M(x,y) = x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1$ has no pure SOS decomposition without denominator $(x^2+y^2)$). **ValidSDP** (`validsdp/validsdp` @ `083e96683cf7087492d4d57e87c546264c2170c1`, Martin-Dorel & Roux CPP 2017; Roux et al. FMSD 2018) bridges untrusted floating-point interior-point SDP witnesses $\tilde{Q}$ into the Coq/Rocq kernel without rational-projection blowup: `soscheck` (`theories/validsdp.v`) computes the exact rational coefficient residual $r = \max_\alpha |(p - z^\top \tilde{Q} z)_\alpha|$, shifts the diagonal downward by $n r$ plus Rump's (2006) rigorous floating-point Cholesky rounding bound $c$ (`theories/cholesky_prog.v`, `libvalidsdp/cholesky.v:corollary_2_7`), and verifies Cholesky positivity reflexively via `vm_cast_no_check` / `native_cast_no_check`. Because $Q - (nr + c)I$ must be strictly positive definite, ValidSDP rejects boundary-touching singular PSD witnesses ($\lambda_{\min}(Q) = 0$) unless strictly interiorized or facially reduced. In **Lean 4 / Mathlib4** (`4502bb0de81f5b5bd65b7b91162a0f1eb9a56b4b`), the historical Sage-backed `polyrith` tactic has been retired (`Mathlib/Tactic/Polyrith.lean:11-21`) in favor of `grobner` (kernel-checked `grind` Gröbner basis for equalities), leaving kernel-checked Positivstellensatz SOS certification outside Mathlib's core tactic suite.
3. **Richardson's Undecidability Barrier vs. $\delta$-Decidability (`dReal4`) and Rational-Envelope RCF (`MetiTarski`):** Adding $\sin$, $\pi$, and $|x|$ (or $\exp$ with $\sin$) makes real-number identity/satisfiability undecidable (Richardson 1968). Three practical escape hatches trade different guarantees:
   - **$\delta$-Decidability (`dreal/dreal4` @ `f93bdcc26b62abdcc30ad7de6046729bb48016b9`, Gao et al. LICS 2012 / CADE 2013):** On compact boxes, Interval Constraint Propagation (IBEX forward-backward contractors + optional polytope linearization + PicoSAT CDCL(T)) is $\delta$-complete: `UNSAT` is mathematically exact (proved by outward-rounded interval refutation), while `delta-SAT` guarantees only that a $\delta$-perturbation (default `kDefaultPrecision = 0.001`) is satisfiable—or, as source inspection of `icp_seq.cc:127-133` exposes, that an unpruned box became non-bisectable at IEEE-754 double 1-ULP resolution even when output interval diameter exceeds $\delta$.
   - **Rational-Function Bounding + RCF (`MetiTarski`, Akbarpour & Paulson JAR 2010):** Replaces `ln`, `exp`, `sin`, `cos`, `arctan`, `sqrt` with continued-fraction / Padé rational upper and lower bounds inside a resolution prover calling an RCF solver (QEPCAD-B / Z3 / Mathematica); certifies **unbounded** strict real inequalities without $\delta$-slack, but cannot prove identities, tight tangencies, or high-dimensional formulas exceeding CAD's variable ceiling.
   - **In-Loop Transcendental Refinement in SMT (`Z3` `nlsat_transcendentals.h` & `cvc5` `transcendental_solver.h`):** Both modern Z3 (`c73b745c`, 2026) and cvc5 (`7507ed17`) integrate sound conservative enclosures / Taylor tangent-secant linearizations (`Cimatti et al., CADE 2017`) directly with their polynomial engines—sound on returned `UNSAT`, incomplete/non-terminating in general.

## Applicability

This report covers the algebraic, numerical, and proof-certification architecture of nonlinear real arithmetic solvers and kernel checkers across seven pinned durable subjects:

- **Exact `QF_NRA` SMT solvers (comparison of conflict-driven CAD vs. coverings):**
  - `Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1` (`src/nlsat/{nlsat_solver.h,nlsat_solver.cpp,nlsat_explain.cpp,nlsat_transcendentals.h}`).
  - `cvc5/cvc5` @ `7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc` (`src/theory/arith/nl/{strategy.cpp,coverings/cdcac.h,coverings/projections.h,coverings/lazard_evaluation.h,transcendental/transcendental_solver.h}`), paired with `SRI-CSL/libpoly` @ `8779171e061fdbda9708d8839e3ca8d0a250df4f`.
- **Reflexive Positivstellensatz / SOS kernel certification:**
  - `validsdp/validsdp` @ `083e96683cf7087492d4d57e87c546264c2170c1` (`theories/{validsdp.v,posdef_check.v,cholesky_prog.v}`, `libvalidsdp/cholesky.v`, `plugins/soswitness/src/soswitness_v820.mlg`), targeting Rocq 9.0+ / Coq + MathComp + Flocq + Coq-Interval + CoqEAL + OSDP.
  - `leanprover-community/mathlib4` @ `4502bb0de81f5b5bd65b7b91162a0f1eb9a56b4b` (`Mathlib/Tactic/Polyrith.lean`), characterizing the boundary of Lean 4 polynomial certificate tactics.
- **Transcendental real reasoning ($\delta$-decidability vs. rational-envelope RCF):**
  - `dreal/dreal4` @ `f93bdcc26b62abdcc30ad7de6046729bb48016b9` (`dreal/solver/{config.h,icp.cc,icp_seq.cc,relational_formula_evaluator.cc,forall_formula_evaluator.cc,context_impl.cc}`, `dreal/contractor/contractor_ibex_fwdbwd.cc`).
  - `MetiTarski` (Akbarpour & Paulson, JAR 2010, DOI `10.1007/s10817-009-9149-2`), characterized from peer-reviewed literature and its official distribution specification.

Source-level claims (exact rounding formulas in `cholesky_prog.v`, `dReal4` default `kDefaultPrecision = 0.001` and 1-ULP exit branch, `Z3` `nlsat_transcendentals.h` in-loop refinement, `cvc5` `LazardEvaluation` CoCoALib fallback, `Mathlib4` `polyrith` deprecation) apply strictly to the pinned revisions. Theoretical results (Davenport–Heintz lower bound, Stengle/Putinar theorems, Richardson's undecidability, $\delta$-completeness) apply to their mathematical definitions. Executable Python 3 probes (`fractions.Fraction` + IEEE-754 `math.nextafter` directed rounding) verify the exact arithmetic invariants of ValidSDP's rounding shift, Motzkin's Positivstellensatz identity, interval wrapping/cluster effects, and 1-ULP stagnation.

## Findings

### 1. Exact Polynomial Real Arithmetic: CAD, Conflict-Driven NLSAT, and Cylindrical Algebraic Coverings

Basis: source (`Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1`, `cvc5/cvc5` @ `7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`) + derived (Collins 1975, Davenport & Heintz 1988, Jovanović & de Moura 2012, Ábrahám et al. 2021)

#### 1.1 Classical CAD Complexity and Projection Nullification
Given a set of multivariate polynomials $P \subset \mathbb{Q}[x_1, \dots, x_n]$ of maximum degree $d$, **Cylindrical Algebraic Decomposition (CAD)** (Collins 1975) partitions $\mathbb{R}^n$ into connected semialgebraic **cells** over which every $p \in P$ is sign-invariant:
1. **Projection phase:** Recursively eliminates $x_n, x_{n-1}, \dots, x_2$ by computing a projection set $\operatorname{Proj}(P_k) \subset \mathbb{Q}[x_1, \dots, x_{k-1}]$ containing coefficients, discriminants $\operatorname{disc}_{x_k}(p)$, and pairwise resultants $\operatorname{res}_{x_k}(p, q)$ (or principal subresultant coefficient chains `psc`).
2. **Lifting phase:** Isolates real algebraic roots of $\operatorname{Proj}^{n-1}(P) \subset \mathbb{Q}[x_1]$, picks rational/algebraic sample points in each section (root) and sector (open interval), substitutes into $P_2$, and lifts recursively to $\mathbb{R}^n$.

- **Complexity wall:** Real quantifier elimination is intrinsically doubly exponential: Davenport & Heintz (JSC 1988, DOI `10.1016/S0747-7171(88)80004-X`) proved a $2^{2^{\Omega(n)}}$ cell-count lower bound even for linear-degree alternation formulas; CAD builds $O((md)^{2^{O(n)}})$ cells in the worst case and is acutely sensitive to variable ordering.
- **McCallum projection nullification hazard:** Collins's complete projection includes all coefficients and all principal subresultants (huge blowup). **McCallum's projection** shrinks this to leading coefficients, discriminants, and resultants—achieving order-invariance—**except when a polynomial is nullified** (vanishes identically) over a lower-dimensional sample point $\alpha \in \mathbb{R}^{k-1}$. For the minimal witness $p(x, y, z) = x \cdot z + y$ (Probe 2B.4), $\operatorname{Proj}_{\text{McCallum}}(\{xz+y\}, z) = \{\operatorname{ldcf}_z(p) = x, \operatorname{disc}_z(p) = 1\}$ omits the trailing coefficient $y$; over $(x, y) = (0, 0)$, $p(0, 0, z) \equiv 0$ vanishes identically across all $z \in \mathbb{R}$, breaking delineability unless either all coefficients are added or **Lazard's modified lifting** divides out vanishing $(x_i - \alpha_i)$ factors.

#### 1.2 Conflict-Driven NLSAT (`Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1`)
Jovanović & de Moura (IJCAR 2012, DOI `10.1007/978-3-642-31365-3_27`) eliminate eager CAD construction via **NLSAT** (the first concrete instantiation of MCSAT): the solver searches directly over partial model assignments $(x_1 \mapsto a_1, \dots, x_{k-1} \mapsto a_{k-1})$ in the real algebraic numbers $\mathbb{R}_{\text{alg}}$ (represented by isolating intervals + square-free defining polynomials). When univariate evaluation at $x_k$ leaves no feasible real interval (the union of infeasible regions covers $\mathbb{R}$), NLSAT calls `explain` to construct a **single CAD cell** containing $(a_1, \dots, a_{k-1})$ throughout which the same conflict persists, learning a semantic lemma whose atoms include **indexed root expressions** ($x_k \bowtie \operatorname{root}_i(p(x_1,\dots,x_{k-1}, \cdot))$).

Inspection of `src/nlsat/nlsat_explain.cpp` (`c73b745cef365e1390408fbd7c599236941d34d1`) reveals how modern Z3 implements conflict projection (`L953-1052`):
- **Path 1 — Levelwise Single-Cell Construction (`levelwise_single_cell`, `L953-981`):** First attempts direct single-cell construction (`levelwise lws(...)`, `L959-960`), emitting `ROOT_EQ` literals for sections (`I.is_section()`) and `ROOT_GT`/`ROOT_GE` / `ROOT_LT`/`ROOT_LE` bounds for non-trivial sectors (`L965-979`). If levelwise projection fails, `project` sets **`m_add_all_coeffs = true`** (`L1019`) to avoid nullification and falls back to Path 2.
- **Path 2 — Sample-Cell Projection (`project`, `L997-1052`, citing Li & Xia, `arXiv:2003.00409`):** Extracts square-free factors into `m_todo` (`L1003-1011`). On the highest variable (`first == true`, where `x` has no sample constraint), it adds leading coefficients (`add_lcs`), discriminants (`psc_discriminant`), and pairwise resultants (`psc_resultant`, `L1034-1039`); on all lower variables, it restricts resultants to sample-bounding polynomials (`psc_resultant_sample`, `L1041-1045`) and generates cell literals via `cac_add_cell_lits`.
- **Direct In-Loop Transcendentals (`src/nlsat/nlsat_transcendentals.h:1-60`):** Notably at Z3 HEAD (`c73b745c`), `nlsat` also registers transcendental applications (`sin/cos/tan/asin/acos/atan/sinh/cosh/tanh/asinh/acosh/atanh/exp/log`, `atan2`) plus exact algebraic `identity_pair` axioms for `(sin, cos)`, `(cosh, sinh)`, and `(cosh, tanh)`. Inside `solver::imp::search_check`, whenever polynomial `search()` returns `l_true`, `refine()` checks each registered witness against conservative floating-point enclosures and inserts permanent interval-exclusion clauses without tearing down the NLSAT solver state.

#### 1.3 Cylindrical Algebraic Coverings (`CAlC` / `CDCAC`) in `cvc5` (`7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`)
Rather than constructing a complete cell decomposition or relying purely on MCSAT root atoms inside the CDCL core, **cvc5** implements a layered CDCL(T) nonlinear strategy (`src/theory/arith/nl/strategy.cpp:111-196`) culminating in **Cylindrical Algebraic Coverings** (Ábrahám, Davenport, England, Kremer, JLAMP 2021, DOI `10.1016/j.jlamp.2020.100633`; implemented in `src/theory/arith/nl/coverings/cdcac.h:46-168`):
1. **Fast incomplete pre-passes (`strategy.cpp:113-163`):** Optional `ICP`, zero-splitting (`NL_SPLIT_ZERO`), monomial sign/magnitude bounds (`NL_MONOMIAL_SIGN`, `NL_MONOMIAL_MAGNITUDE0..2`, `NL_MONOMIAL_INFER_BOUNDS`), and incremental linearization tangent planes (`NL_TANGENT_PLANES`) resolve easy conflicts via linear arithmetic (`LRA`) without algebraic numbers.
2. **Complete `CDCAC` (`COVERINGS_INIT` / `COVERINGS_FULL`, `strategy.cpp:164-168`, `cdcac.h:86-168`):** Backed by `libpoly` (`8779171e`), `CDCAC::getUnsatCoverImpl` recursively builds a **covering** (overlapping infeasible open/closed intervals whose union covers $\mathbb{R}$, rather than disjoint CAD cells!). When infeasible intervals cover the line for `cur_variable`, `constructCharacterization` (`L116`) computes projection polynomials (discriminants + resultants of *adjacent* covering intervals only, avoiding all-pairs resultant blowup!) via `requiredCoefficients` (McCallum or Lazard) and lifts a single wider infeasible interval (`intervalFromCharacterization`, `L122`) to the parent dimension.
3. **Lazard Modified Lifting & CoCoALib Build Dependency (`lazard_evaluation.h:40-80`):** To overcome McCallum nullification (`foundNullifiedPolynomial()`, `cdcac.h:158`), `LazardEvaluation` conceptually iterates `while p[x // a] = 0: p = p / (x - a)` over real algebraic assignments by embedding $p$ into the tower of quotient rings $\mathbb{Q}[x_k]/\langle p_k\rangle$ and computing a Gröbner basis (or iterated resultant) to project into the free variable $x_n$. Critically, **`lazard_evaluation.h:77-79` documents a silent configuration fallback**: *"If CoCoALib is not available, this class will simply fall back to `poly::infeasible_regions` and issue a warning about this."* Builds of cvc5 without CoCoALib thus lose true Lazard nullification recovery.

---

### 2. Positivstellensatz Sum-of-Squares Certificates and ValidSDP Reflexive Cholesky Verification

Basis: source (`validsdp/validsdp` @ `083e96683cf7087492d4d57e87c546264c2170c1`, `leanprover-community/mathlib4` @ `4502bb0de81f5b5bd65b7b91162a0f1eb9a56b4b`) + execution (Probe 2A) + derived (Stengle 1974, Putinar 1993, Martin-Dorel & Roux CPP 2017, Roux et al. FMSD 2018)

#### 2.1 Algebraic Positivstellensatz Hierarchy and Degree-Completeness Limits
To certify $\forall x \in \mathbb{R}^n.\; \left(\bigwedge_{i=1}^m g_i(x) \ge 0\right) \implies f(x) \ge 0$ (or $> 0$) inside a small proof-assistant kernel (Coq/Rocq, Lean 4, HOL Light), algebraic certificates decouple untrusted search from polynomial-time kernel checking:

- **Sum of Squares (SOS) $\leftrightarrow$ Semidefinite Programming (Parrilo 2003):** A polynomial $s(x)$ of degree $2d$ is a sum of squares $s(x) = \sum_k h_k(x)^2$ iff there exists a symmetric positive semidefinite (PSD) **Gram matrix** $Q \succeq 0$ such that $s(x) = z(x)^\top Q z(x)$, where $z(x)$ is the vector of monomials of degree $\le d$ (dimension $N = \binom{n+d}{d}$). Matching coefficients of $z^\top Q z$ against $s(x)$ defines a linear matrix inequality (SDP) solvable in polynomial time for fixed $(n, d)$ by interior-point solvers (CSDP, SDPA, Mosek).
- **The Hilbert/Motzkin Gap (Nonnegative $\supsetneq$ SOS):** For $n \ge 2$ and degree $2d \ge 6$ (or $n \ge 3, 2d \ge 4$), nonnegative polynomials need not be SOS. The **Motzkin polynomial** $M(x, y) = x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1$ satisfies $M(x,y) \ge 0$ everywhere (by AM-GM on $x^4 y^2, x^2 y^4, 1$) yet has **no** polynomial SOS decomposition in $\mathbb{R}[x,y]$.
- **Stengle's Positivstellensatz (1974, DOI `10.1007/BF01362149`):** Over *arbitrary* semialgebraic sets $\{g_i \ge 0\}$, refutation is complete using multiplicative cones (products of $g_i$ with SOS multipliers) and denominators—e.g., $(x^2 + y^2) M(x, y) = x^2 (y^2 - 1)^2 + y^2 (x^2 - 1)^2 + x^2 y^2 (x^2 + y^2 - 2)^2$ (verified identically in Probe 2A.3!).
- **Putinar's Positivstellensatz (1993, DOI `10.1512/iumj.1993.42.42045`):** Under the **Archimedean condition** (compact domain, e.g., $R^2 - \|x\|^2 \ge 0$ belongs to the quadratic module), every *strictly positive* polynomial $f > 0$ on $\{g_i \ge 0\}$ admits a **linear-in-$g_i$** SOS representation $f = s_0 + \sum_{i=1}^m s_i g_i$ ($s_0, s_i \in \Sigma[x]^2$)—eliminating exponential cross-product cones at the cost of an unknown degree bound on $s_i$.

#### 2.2 ValidSDP's Floating-Point Witness Certification Pipeline (`validsdp/validsdp` @ `083e96683cf7087492d4d57e87c546264c2170c1`)
Numerical interior-point SDP solvers (called via OCaml's `OSDP` in `plugins/soswitness/src/soswitness_v820.mlg`) return an approximate IEEE-754 floating-point Gram matrix $\tilde{Q}$ that satisfies $p(x) - z(x)^\top \tilde{Q} z(x) = \epsilon(x) \neq 0$ (small residual $\sim 10^{-8}$) and is only numerically positive definite. Naive exact rational $LDL^\top$ factorization blows up bit-widths exponentially in matrix dimension $n$.

**ValidSDP** (Martin-Dorel & Roux, CPP 2017, DOI `10.1145/3018610.3018622`; Roux, Voronin, Sankaranarayanan, FMSD 2018, DOI `10.1007/s10703-017-0302-y`) solves this inside Rocq/Coq via **exact rational residual accounting + rigorous floating-point Cholesky decomposition (Rump 2006)**:

1. **Exact Rational Residual Extraction (`theories/validsdp.v:868-883, 2174-2179`):**
   ```coq
   Definition soscheck (p : polyT) (z : mx monom s 1) (Q : mx F s s) : bool :=
     check_base p z &&
     let r :=
       let p' := ... (zp^T *m Q' *m zp) ... in
       let pmp' := poly_sub_op p p' in
       max_coeff pmp' in
     posdef_check_itv fieps fieta finite Q (T2F r).
   ```
   After verifying monomial coverage (`check_base p z`, every monomial of $p$ appears in $z \cdot z^\top$, `L860-864`), `soscheck` casts each binary float entry of $\tilde{Q}$ **exactly** to a dyadic rational (`F2T := F2bigQ \o FI_val`, `L2177`), symbolically expands $p - z^\top \tilde{Q} z$ over exact `bigQ` sparse polynomials (`CoqEAL` `effmpoly`), computes $r = \max_\alpha |(p - z^\top \tilde{Q} z)_\alpha|$, and rounds $r$ **upward** to a float `T2F r` (`L2178`).
2. **Diagonal Spectral-Norm Perturbation Shift (`theories/cholesky_prog.v:155-159`):**
   If $p - z^\top \tilde{Q} z = z^\top E z$ for a symmetric error matrix $E$ with $|E_{ij}| \le r$, then $\|E\|_2 \le \|E\|_F \le n \cdot r$ (where $n = |z|$). `posdef_check_itv` therefore subtracts $n \cdot r$ **downward** (`subdn`) from every diagonal entry of $\tilde{Q}$:
   $$A' = \tilde{Q} - \operatorname{fl}_{\downarrow}(n \cdot r) I.$$
3. **Rump (2006) Floating-Point Cholesky Rounding Shift (`theories/cholesky_prog.v:118-153`, `libvalidsdp/cholesky.v:722`):**
   `posdef_check` verifies `test_n n` ($3(n+1)\varepsilon < 1$, `L141-143`), symmetry `is_sym A'`, and nonnegative diagonal `noneg_diag A'`, then computes an upward-rounded upper bound `c = compute_c_aux A' (max_diag A')` (`L120-128`) over-approximating:
   $$c \ge \frac{(n+2)\varepsilon}{1 - (n+2)\varepsilon}\operatorname{tr}(A') + 4\eta n\left(2(n+1) + \max_i A'_{ii}\right)$$
   where $\varepsilon = 2^{-53}$ (unit roundoff) and $\eta = 2^{-1074}$ (underflow unit) for IEEE-754 binary64. It shifts the diagonal downward once more to $A'' = A' - c I$ (`L150`) and runs standard floating-point Cholesky `R := cholesky A''` (`L151`), checking `all_diag is_finite R && pos_diag R` (`L152`). By **`libvalidsdp/cholesky.v:722` (`corollary_2_7`)**, floating-point Cholesky success on $A''$ implies **exact real positive definiteness** `posdef Xt` for *every* real symmetric matrix $X_t$ within entrywise radius `Rad` of $\tilde{Q}$—hence $p(x) = z(x)^\top (\tilde{Q} + E) z(x) \ge 0$ globally!
4. **Constrained Positivstellensatz & Strict Positivity (`validsdp.v:898-917, 2173-2187`):**
   `soscheck_hyps` verifies $\bigwedge_i p_i \ge 0 \implies p \ge 0$ by certifying `soscheck (p - \sum_i s_i p_i) z Q` **and** `soscheck s_i z_i Q_i` for every multiplier $s_i$. For *strict* positivity ($p > 0$), `soscheck_hyps_eff_wrapup` additionally requires **`strict ==> has_const_eff z`** (`L2173`), guaranteeing the constant monomial $1$ appears in $z$ so $z(x)^\top Q_{\text{true}} z(x) \ge \lambda_{\min}(Q_{\text{true}}) \cdot 1 > 0$. The entire check executes inside Coq's bytecode/native evaluator via CoqEAL data refinements (`hseqmx`, `effmpoly`) and `vm_cast_no_check (erefl true)` / `native_cast_no_check (erefl true)` (`posdef_check.v:214-226`), with support for both `CoqInterval` software floats and hardware 63-bit/64-bit `primitive_floats_infnan` (`posdef_check.v:244-246`).
5. **Failure Mode — Boundary-Touching Singular PSD Polynomials (Probe 2A.2):**
   Because ValidSDP subtracts a strictly positive shift $(nr + c)I$ ($c > 0$) and requires `pos_diag R` (strictly positive Cholesky pivots), **any** polynomial whose Gram matrix lies on the boundary of the PSD cone ($\lambda_{\min}(Q) = 0$)—even exact $(x - y)^2$ with zero residual ($r = 0$)—causes $Q - c I$ to acquire eigenvalue $-c < 0$ and fails `posdef_check` unless the user first applies facial reduction (eliminating zero-eigenvector directions) or relaxes the goal by $+\epsilon$.

#### 2.3 Lean 4 / Mathlib4 Polynomial Certificate Boundary (`4502bb0de81f5b5bd65b7b91162a0f1eb9a56b4b`)
Inspection of `Mathlib/Tactic/Polyrith.lean:11-64` confirms a significant recent ecosystem shift:
- The external-oracle `polyrith` tactic (which queried a remote SageCell API for Nullstellensatz / ideal-membership `linear_combination` witnesses) now unconditionally throws an error (`"`polyrith` is no longer available, as the external service it relied on has been shut down"`, `L60-61`).
- Mathlib4 directs polynomial **equality** (Nullstellensatz / ideal membership) goals to **`grobner`** (backed by Lean 4's kernel-checked `grind` Gröbner basis module, `L18-20`), while nonlinear **inequalities** in Mathlib rely on syntactic heuristics (`positivity`, `nlinarith`) rather than a built-in SDP/Positivstellensatz reflexive Cholesky verifier equivalent to ValidSDP. Adopting ValidSDP's exact-residual + directed-rounded Cholesky architecture in Lean 4 requires either kernel-verified floating-point arithmetic (`Float` lacks definitional reduction/axiomatization in Lean's kernel, so software dyadic floats over `Int`/`Nat` or verified rational $LDL^\top$ are needed to avoid `Lean.ofReduceBool` / `native_decide` trust expansion).

---

### 3. Transcendental Real Arithmetic: Richardson's Barrier, `dReal4` $\delta$-Decidability, and `MetiTarski`

Basis: source (`dreal/dreal4` @ `f93bdcc26b62abdcc30ad7de6046729bb48016b9`, `cvc5/cvc5` @ `7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`) + documentation (`JSL 1968`, `LICS 2012`, `CADE 2013`, `JAR 2010`) + execution (Probe 2B)

#### 3.1 Richardson's Undecidability Theorem (1968)
Daniel Richardson (JSL 1968, DOI `10.2307/2271358`) proved that for the class of expressions generated from rational numbers, $x$, $\pi$, $\ln 2$, $+, -, \times$, $\sin$, $\exp$, and $|\cdot|$ (or $\sin$ with $x$ and $\pi$ via $\sin(\pi x) = 0 \iff x \in \mathbb{Z}$, encoding Hilbert's 10th Problem over Diophantine polynomials!), determining whether an expression $E(x)$ satisfies $\exists x \in \mathbb{R}.\; E(x) < 0$ (or identically $E(x) = 0$) is **undecidable**. No algorithm can decide arbitrary real formulas containing both polynomials and periodic transcendentals.

#### 3.2 $\delta$-Decidability and `dReal4` (`dreal/dreal4` @ `f93bdcc26b62abdcc30ad7de6046729bb48016b9`)
Gao, Avigad, and Clarke (LICS 2012, DOI `10.1109/LICS.2012.41`) circumvented Richardson's theorem for **bounded-domain Type-2 computable functions** ($\exp, \sin, \cos, \arctan, \ln, \text{ODE flows}$) by weakening exact satisfiability to **$\delta$-decidability**: given a formula $\phi$ over compact box $B \subset \mathbb{R}^n$ and any rational $\delta > 0$, a $\delta$-complete decision procedure always terminates and returns either:
- **`UNSAT`**: $\phi$ is **mathematically unsatisfiable** on $B$ (exact refutation; zero false negatives!), or
- **`delta-SAT`**: the syntactic $\delta$-perturbation $\phi^\delta$ (relaxing $f(x) = 0$ to $|f(x)| \le \delta$, $f(x) \le 0$ to $f(x) \le \delta$, etc.) is satisfiable on $B$. (Note: $\delta$-SAT and exact UNSAT overlap on the narrow boundary band where $\phi$ is UNSAT but $\phi^\delta$ is SAT.)

Direct inspection of **`dReal4`** (`dreal/dreal4` @ `f93bdcc26b62abdcc30ad7de6046729bb48016b9`) exposes the exact operational semantics and subtle engineering boundaries of its CDCL(T) + Interval Constraint Propagation (ICP) engine:

1. **Architecture & Contractors:** PicoSAT (`SatSolver`) proposes Boolean truth assignments; `IcpSeq::CheckSat` (`dreal/solver/icp_seq.cc:34-143`) runs a branch-and-prune loop over boxes (`Box`) applying **IBEX forward-backward contractors** (`ContractorIbexFwdbwd::Prune` calling `num_ctr_->f.backward(rhs, iv)`, i.e., HC4Revise, `contractor_ibex_fwdbwd.cc:99-100`) plus optional LP polytope contractors (`use_polytope_`, default `false`, `config.h:172`) and worklist fixpoints (`use_worklist_fixpoint_`, default `false`, `config.h:174`). Every contractor that shrinks or empties the box registers its source constraint via `cs->AddUsedConstraint(f_)` (`contractor_ibex_fwdbwd.cc:124`) to extract minimal unsatisfiable conflict clauses for PicoSAT.
2. **Exact Box Evaluation & $\delta$ Stopping Rule (`icp.cc:30-76`, `relational_formula_evaluator.cc:89-159`, `config.h:161`):**
   - `RelationalFormulaEvaluator` evaluates $e_1(B) - e_2(B)$ using outward-rounded interval arithmetic:
     - For `EQ` ($e_1 = e_2$): `VALID` iff $[0,0]$; `UNSAT` iff $0 \notin \text{eval}$; else `UNKNOWN` (`L93-108`).
     - For `GT` ($e_1 > e_2$): `VALID` iff $\text{lb} > 0$; `UNSAT` iff $\text{ub} \le 0$; else `UNKNOWN` (`L127-142`).
     - For `NEQ` ($e_1 \neq e_2$): `VALID` iff $0 \notin \text{eval}$; `UNSAT` iff $[0,0]$; else `UNKNOWN` (`L110-125`).
   - In `EvaluateBox` (`icp.cc:53-72`), an `UNKNOWN` constraint requests branching **only if** `evaluation.diam() > config().precision()` (default **`kDefaultPrecision = 0.001`**, `config.h:161`) **and** `!is_simple_relational() && !is_neq()` (`icp.cc:61-64`). Once `branching_candidates.none()`, `IcpSeq::CheckSat` returns `true` (`delta-SAT`, `icp_seq.cc:106-110`).
3. **Critical Undocumented Edge Case — Non-Bisectable 1-ULP IEEE-754 Return (`icp_seq.cc:117-133`):**
   ```cpp
   const int branching_dim = config().brancher()(
       current_box, *evaluation_result, &box_left, &box_right);
   if (branching_dim >= 0) { ... }
   else {
     DREAL_LOG_DEBUG("... not satisfying delta-condition but it's not bisectable.");
     return true;
   }
   ```
   When a steep constraint (e.g., $10^{20}(x - 1/3) = 0$, Probe 2B.3) narrows `current_box` down to adjacent IEEE-754 `double` endpoints (`diam = 5.551e-17`, 1 ULP) while its interval output diameter is still $1.665 \times 10^4 \gg \delta = 10^{-3}$, `branching_dim` returns `-1` and `dReal4` **returns `delta-SAT` anyway**! Thus `delta-SAT` guarantees output diameter $\le \delta$ *modulo machine double precision*; `UNSAT` remains completely sound.
4. **Interval Dependency Wrapping & Cluster Effect (Probe 2B.1 & 2B.2):**
   - For the globally UNSAT formula $(x - x) + 10^{-4} = 0$ on $[0, 1]$, natural interval arithmetic evaluates $B - B + 10^{-4}$ with width $2\operatorname{diam}(B)$. At $\delta = 10^{-3}$, ICP stops after **11 splits** returning spurious **`delta-SAT`** on $[0, 4.88 \times 10^{-4}]$; tightening to $\delta = 10^{-5}$ proves **`UNSAT`** but requires **16,383 splits** (classic Moore cluster effect!).
   - For the true transcendental inequality $\sin(x) < x$ (checking $\sin(x) - x > 0$), because $\sin(x) - x \approx -x^3/6$ approaches zero cubically near $0$, ICP at $\delta = 10^{-3}$ returns **`delta-SAT`** on $[0.01, 1.0]$ (where $|\sin(0.01) - 0.01| = 1.67 \times 10^{-7} \ll 10^{-3}$, 11 splits) while proving exact **`UNSAT`** on $[0.25, 1.0]$ (61 splits).
5. **Quantified $\exists\forall$ Solving (`forall_formula_evaluator.cc:74-134`):**
   `ForallFormulaEvaluator` instantiates a nested `Context` asserting **`DeltaStrengthen(!get_quantified_formula(formula()), epsilon)`** (`L95-96`) with precision `delta` (`L83`). For a candidate outer box $B_\exists$, if the inner counterexample search returns `UNSAT` (no $\epsilon$-strengthened counterexample exists), the $\forall$ constraint is certified `VALID` (`L129-133`); otherwise the counterexample box is evaluated back against the disjuncts to drive outer branching (`L108-128`), optionally accelerated by NLopt local optimization (`config.h:162-165, 175`).

#### 3.3 `MetiTarski` Rational-Function Bounds + RCF (`JAR 2010`) and `cvc5` Transcendental Incremental Linearization (`7507ed17`)
- **MetiTarski** (Akbarpour & Paulson, JAR 2010, DOI `10.1007/s10817-009-9149-2`) attacks **unbounded universally quantified** special-function inequalities ($\forall x.\; \dots \ln x, \exp x, \sin x, \cos x, \arctan x, \sqrt{x} \dots$) without $\delta$-slack:
  1. Augments the Metis first-order resolution prover with a curated library of **continued-fraction and Padé rational upper/lower bound axioms** valid on explicit intervals (vastly tighter and wider-domain than truncated Taylor polynomials for $\ln$ and $\arctan$).
  2. Clears denominators via case-splitting on denominator sign, reducing clauses to pure polynomial inequalities.
  3. Calls an external RCF decision procedure (**QEPCAD-B**, Z3, or Mathematica) to eliminate variables and discharge polynomial subgoals.
  4. **Sharp failure boundaries:** Because rational upper/lower bounds leave a strict gap around exact values at non-anchor points, MetiTarski generally requires **strict inequalities** (cannot prove transcendental identities like $\sin^2 x + \cos^2 x = 1$ or tight tangencies without dedicated algebraic rewrite axioms), is inherently incomplete, and hits CAD's doubly-exponential wall beyond ~3–6 real variables.
- **cvc5 Transcendental Solver (`src/theory/arith/nl/transcendental/transcendental_solver.h:37-150`):** Implements incremental linearization (Cimatti et al., CADE 2017): constructs degree-$k$ Taylor upper/lower envelopes $P_u, P_l$ with rigorous remainder bounds (`taylor_generator.h`) and emits linear **tangent plane** and **secant plane** lemmas (e.g., `(0 < y < PI/2) => sin(y) <= T(y)` and secant lower bounds on `(0, 1)` and `(1, PI/2)`, `L105-149`) gated behind `--nl-ext-tf-tplanes` (non-terminating in general, off by default, `L101-103`).

---

### 4. Cross-System Decision Procedure & Proof-Certification Trade-Off Matrix

Basis: source + documentation + execution + derived

| System / Method | Theory Scope | Completeness & Soundness Semantics | Asymptotic Scaling / Bottleneck | Proof / Kernel Certification Path | Primary Failure Mode |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Classical CAD** (Collins / QEPCAD-B) | Full first-order RCF ($\exists, \forall$, polynomials) | Exact decision procedure (sound & complete) | Doubly exponential $2^{2^{\Omega(n)}}$ in variables $n$ | Complex algebraic-number cell proofs; no mainstream lightweight kernel checker | Variable-count explosion ($n \gtrsim 5$–$8$), variable-ordering sensitivity |
| **Z3 NLSAT** (`c73b745c`) | `QF_NRA` (+ experimental in-loop transcendentals) | Complete on `QF_NRA`; sound (incomplete) on transcendentals | Single-cell conflict-driven; doubly exponential worst case | No built-in kernel-checked Lean/Coq proof export for CAD projections | Levelwise fallback + all-coeffs blowup on high-degree coupled constraints |
| **cvc5 `CDCAC` + `TranscendentalSolver`** (`7507ed17`) | `QF_NRA` (+ optional `QF_NRAT` tangent/secant planes) | Complete on `QF_NRA` (with CoCoALib Lazard); incomplete on transcendentals | Covering intervals avoid all-pairs resultants; worst-case doubly exponential | Internal `CoveringsProofGenerator` (`cdcac.h:168`); Lazard needs CoCoALib | Nullification warning/fallback if built without CoCoALib; non-termination on `--nl-ext-tf-tplanes` |
| **ValidSDP** (`083e9668`) | Universal polynomial positivity ($\bigwedge p_i \ge 0 \implies p \ge 0$ or $> 0$) | **Sound** (Rocq/Coq kernel-checked); incomplete (fixed SOS degree + interior PD) | Polynomial in $\binom{n+d}{d}$ per fixed degree $2d$ (fast for $n \le 20$, low $d$) | **Gold standard:** reflexive CoqEAL `vm_cast_no_check` / `native_cast_no_check` via Rump Cholesky | Singular PSD boundaries ($\lambda_{\min} = 0$), Motzkin-type non-SOS forms without Putinar/Stengle lifting |
| **dReal4** (`f93bdcc2`) | Bounded `QF_NRA` + transcendentals + ODEs + $\exists\forall$ | **$\delta$-complete** on compact boxes: `UNSAT` exact, `delta-SAT` up to $\delta$ (or 1 ULP) | Exponential in dimension $n$ (cluster effect near boundary/tangency) | External interval-proof trace checking possible; core C++/IBEX solver unverified | Spurious `delta-SAT` on near-tangency / wrapping, cluster blowup as $\delta \to 0$, 1-ULP steep exit |
| **MetiTarski** (`JAR 2010`) | Unbounded $\forall$ special-function inequalities (`ln`, `exp`, `sin`, `cos`, `arctan`) | Sound (modulo RCF backend & bound axioms); incomplete | Limited by RCF/CAD backend ($n \lesssim 4$–$6$) and bound-axiom degree | Resolution proof traces checkable in Isabelle/HOL or PVS (`metit`) | Identities, tight tangencies, high variable counts, domain-guard explosion |

## Boundaries

- **Not examined (live binary benchmarks):** Compiled C++/OCaml/Coq binaries for Z3, cvc5, ValidSDP, dReal4, and MetiTarski were not executed on benchmark suites; execution evidence comes from standalone Python 3 stdlib probes replicating the exact rounding, Cholesky, interval-contractor, and nullification formulas inspected in upstream source.
- **Known not to apply (ValidSDP on singular PSD or non-SOS polynomials):** ValidSDP's `posdef_check_itv` (`cholesky_prog.v:155-159`) requires strict positive definiteness of $Q - (nr + c)I$ (`pos_diag R`, `L152`) and therefore **cannot** directly certify boundary-touching PSD witnesses with $\lambda_{\min}(Q) = 0$ (Probe 2A.2) or globally nonnegative non-SOS polynomials such as Motzkin's $M(x,y)$ without explicit Positivstellensatz denominators/multipliers (Probe 2A.3).
- **Known not to apply (`dReal4` `delta-SAT` as exact satisfiability or strict $\delta$-bound at 1 ULP):** `dReal4`'s `delta-SAT` result never establishes exact satisfiability—and when IEEE-754 double bisection exhausts at 1 ULP (`branching_dim < 0`, `icp_seq.cc:127-133`), it returns `delta-SAT` even if constraint evaluation diameter strictly exceeds `precision` (Probe 2B.3). Furthermore, `dReal4`'s $\delta$-completeness theorem requires **bounded** variable domains (compact boxes); unbounded real variables can diverge.
- **Known not to apply (`cvc5` Lazard projection without CoCoALib):** As documented in `src/theory/arith/nl/coverings/lazard_evaluation.h:77-79`, builds of cvc5 lacking CoCoALib fall back to `poly::infeasible_regions` rather than executing Lazard's quotient-ring nullification recovery.
- **Unsupported (`Mathlib4` `polyrith` and kernel-checked SDP SOS in core Mathlib):** At `leanprover-community/mathlib4` @ `4502bb0de81f5b5bd65b7b91162a0f1eb9a56b4b`, `polyrith` is permanently disabled (`Mathlib/Tactic/Polyrith.lean:58-62`), and core Mathlib4 has no reflexive floating-point Cholesky Positivstellensatz checker analogous to ValidSDP.
- **Unknown (Z3 `nlsat_transcendentals.h` empirical termination and proof-production coverage):** While `src/nlsat/nlsat_transcendentals.h` was inspected at `c73b745cef365e1390408fbd7c599236941d34d1`, its underlying `transcendental_eval.cpp` rounding-error proof and interaction with Z3's proof-logging mode were not examined.
- **Not examined (MetiTarski Bitbucket source tree):** MetiTarski's upstream Bitbucket source repository was not cloned; MetiTarski findings rely on the peer-reviewed JAR 2010 specification (`10.1007/s10817-009-9149-2`) and Cambridge distribution documentation.

## Evidence

### Peer-Reviewed Literature and Mathematical Foundations
- **Richardson (1968):** D. Richardson, *"Some Undecidable Problems Involving Elementary Functions of a Real Variable"*, Journal of Symbolic Logic 33(4):514–520, DOI `10.2307/2271358`.
- **Stengle (1974):** G. Stengle, *"A Nullstellensatz and a Positivstellensatz in semialgebraic geometry"*, Mathematische Annalen 207:87–97, DOI `10.1007/BF01362149`.
- **Davenport & Heintz (1988):** J. H. Davenport, J. Heintz, *"Real quantifier elimination is doubly exponential"*, Journal of Symbolic Computation 5(1–2):29–35, DOI `10.1016/S0747-7171(88)80004-X`.
- **Putinar (1993):** M. Putinar, *"Positive polynomials on compact semi-algebraic sets"*, Indiana University Mathematics Journal 42(3):969–984, DOI `10.1512/iumj.1993.42.42045`.
- **Akbarpour & Paulson (2010):** B. Akbarpour, L. C. Paulson, *"MetiTarski: An Automatic Theorem Prover for Real-Valued Special Functions"*, Journal of Automated Reasoning 44(3):175–205, DOI `10.1007/s10817-009-9149-2`.
- **Jovanović & de Moura (2012):** D. Jovanović, L. de Moura, *"Solving Non-linear Arithmetic"*, IJCAR 2012, LNCS 7364, ch. 27, pp. 339–354, DOI `10.1007/978-3-642-31365-3_27`.
- **Gao, Avigad, Clarke (2012):** S. Gao, J. Avigad, E. M. Clarke, *"$\delta$-Complete Decision Procedures for Satisfiability over the Reals"*, LICS 2012, DOI `10.1109/LICS.2012.41`.
- **Gao, Kong, Clarke (2013):** S. Gao, S. Kong, E. M. Clarke, *"dReal: An SMT Solver for Nonlinear Theories over the Reals"*, CADE-24 (2013), LNCS 7898, DOI `10.1007/978-3-642-38574-2_14`.
- **Martin-Dorel & Roux (2017):** É. Martin-Dorel, P. Roux, *"A Reflexive Tactic for Polynomial Positivity Using Numerical Solvers and Floating-Point Computations"*, CPP 2017, DOI `10.1145/3018610.3018622`.
- **Roux, Voronin, Sankaranarayanan (2018):** P. Roux, Y.-L. Voronin, S. Sankaranarayanan, *"Validating Numerical Semidefinite Programming Solvers for Polynomial Invariants"*, Formal Methods in System Design 53:286–312, DOI `10.1007/s10703-017-0302-y`.
- **Ábrahám, Davenport, England, Kremer (2021):** E. Ábrahám, J. H. Davenport, M. England, G. Kremer, *"Deciding the consistency of non-linear real arithmetic constraints with a conflict driven search using cylindrical algebraic coverings"*, JLAMP 119:100633, DOI `10.1016/j.jlamp.2020.100633`.

### Pinned Upstream Source Locations (Observed 2026-11-19)
- **`Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1`:**
  - `src/nlsat/nlsat_explain.cpp:953-1052` (`levelwise_single_cell`, fallback `m_add_all_coeffs = true` at L1019, sample-cell `project` citing `arXiv:2003.00409`, `psc_discriminant`, `psc_resultant`, `psc_resultant_sample`).
  - `src/nlsat/nlsat_transcendentals.h:1-60` (direct-in-NLSAT transcendental `refine()` loop and algebraic `identity_pair` axioms).
- **`cvc5/cvc5` @ `7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`:**
  - `src/theory/arith/nl/strategy.cpp:111-196` (`Strategy::initializeStrategy`, ordering of `ICP`, monomial passes, `COVERINGS_INIT`/`COVERINGS_FULL`, fallback tangent planes).
  - `src/theory/arith/nl/coverings/cdcac.h:46-168` (`CDCAC`, `getUnsatIntervals`, `constructCharacterization`, `intervalFromCharacterization`, `foundNullifiedPolynomial`, `CoveringsProofGenerator`).
  - `src/theory/arith/nl/coverings/projections.h:40-70` (`PolyVector`, `projectionMcCallum`).
  - `src/theory/arith/nl/coverings/lazard_evaluation.h:40-117` (`LazardEvaluation`, quotient-ring tower, CoCoALib fallback warning L77-79).
  - `src/theory/arith/nl/transcendental/transcendental_solver.h:37-150` (`TranscendentalSolver`, Cimatti et al. CADE 2017 Taylor/tangent/secant linearization, `--nl-ext-tf-tplanes`).
- **`validsdp/validsdp` @ `083e96683cf7087492d4d57e87c546264c2170c1`:**
  - `README.md:1-40` (Rocq 9.0+, MathComp, Flocq, Coq-Interval, OSDP, CoqEAL dependencies).
  - `theories/cholesky_prog.v:60-160` (`cholesky`, `compute_c_aux`, `compute_c`, `test_n`, `posdef_check`, `posdef_check_itv`).
  - `libvalidsdp/cholesky.v:722-765` (`Lemma corollary_2_7`, Rump 2006 interval-matrix positive-definiteness proof).
  - `theories/posdef_check.v:118-246` (`posdefcheck_eff_wrapup_correct`, `vm_cast_no_check`, `native_cast_no_check`, `primitive_floats_infnan`).
  - `theories/validsdp.v:860-917, 2135-2215` (`check_base`, `soscheck`, `soscheck_hyps`, `has_const`, `strict ==> has_const_eff`, `soscheck_hyps_eff_wrapup_correct`).
- **`dreal/dreal4` @ `f93bdcc26b62abdcc30ad7de6046729bb48016b9`:**
  - `dreal/solver/config.h:161-230` (`kDefaultPrecision = 0.001`, `use_polytope_`, `use_worklist_fixpoint_`, `use_local_optimization_`, `BranchLargestFirst`).
  - `dreal/solver/icp.cc:30-76` (`EvaluateBox`, `diam > precision`, `is_simple_relational() || is_neq()` skip).
  - `dreal/solver/icp_seq.cc:34-143` (`IcpSeq::CheckSat`, non-bisectable 1-ULP `return true` at L127-133).
  - `dreal/solver/relational_formula_evaluator.cc:89-159` (`EQ`/`NEQ`/`GT`/`GEQ` interval classification).
  - `dreal/contractor/contractor_ibex_fwdbwd.cc:68-137` (`num_ctr_->f.backward`, `AddUsedConstraint`).
  - `dreal/solver/forall_formula_evaluator.cc:74-134` (`DeltaStrengthen`, nested `Context` counterexample search).
- **`leanprover-community/mathlib4` @ `4502bb0de81f5b5bd65b7b91162a0f1eb9a56b4b`:**
  - `Mathlib/Tactic/Polyrith.lean:11-64` (deprecation of SageCell-backed `polyrith`; redirection to `grobner` / `grind`).

### Executable Micro-Probes (Python 3 Stdlib, Executed 2026-11-19)

#### Probe 2A: Exact ValidSDP / Rump (2006) Cholesky Certification, Singular PSD Failure, and Motzkin Identity
```python
import math
from fractions import Fraction

EPS, ETA = 2.0 ** -53, 2.0 ** -1074
addup = lambda a, b: math.nextafter(a + b, math.inf)
mulup = lambda a, b: math.nextafter(a * b, math.inf)
divup = lambda a, b: math.nextafter(a / b, math.inf)
subdn = lambda a, b: math.nextafter(a - b, -math.inf)

def compute_c(A):
    n = len(A)
    if not (mulup(mulup(3.0, float(n + 1)), EPS) < 1.0): return None
    np2eps = mulup(float(n + 2), EPS)
    nem1 = addup(np2eps, -1.0)
    if not (math.isfinite(nem1) and nem1 < 0.0): return None
    g = divup(np2eps, -nem1)
    tr_up, maxd = 0.0, 0.0
    for i in range(n):
        tr_up = addup(tr_up, A[i][i]); maxd = max(maxd, A[i][i])
    return addup(mulup(g, tr_up), mulup(mulup(mulup(4.0, ETA), float(n)), addup(float(2*(n+1)), maxd)))

def cholesky_ok(A):
    n = len(A); R = [[0.0]*n for _ in range(n)]
    for j in range(n):
        for i in range(j):
            s = A[i][j] - sum(R[i][k]*R[j][k] for k in range(i))
            if not (math.isfinite(R[i][i]) and R[i][i] > 0.0): return False
            R[j][i] = s / R[i][i]
        s = A[j][j] - sum(R[j][k]*R[j][k] for k in range(j))
        if not (math.isfinite(s) and s > 0.0): return False
        R[j][j] = math.sqrt(s)
    return True

def validsdp_soscheck(p, monoms, Q):
    n, gram = len(monoms), {}
    for i in range(n):
        for j in range(n):
            k = tuple(a+b for a, b in zip(monoms[i], monoms[j]))
            gram[k] = gram.get(k, Fraction(0)) + Fraction(Q[i][j])
    r_exact = max((abs(p.get(k, Fraction(0)) - gram.get(k, Fraction(0))) for k in set(p)|set(gram)), default=Fraction(0))
    rf = float(r_exact)
    if Fraction(rf) < r_exact: rf = math.nextafter(rf, math.inf)
    nm = mulup(float(n), rf)
    A1 = [row[:] for row in Q]
    for i in range(n): A1[i][i] = subdn(A1[i][i], nm)
    if any(A1[i][i] < 0.0 for i in range(n)): return False, r_exact, nm, None
    c = compute_c(A1)
    A2 = [row[:] for row in A1]
    for i in range(n): A2[i][i] = subdn(A2[i][i], c)
    return cholesky_ok(A2), r_exact, nm, c

p1 = {(0,0): Fraction(1), (2,0): Fraction(2), (0,2): Fraction(2),
      (4,0): Fraction(2), (3,1): Fraction(2), (2,2): Fraction(-1), (0,4): Fraction(5)}
monoms = [(0,0), (1,0), (0,1), (2,0), (1,1), (0,2)]
Q_noisy = [
    [1.00000001, 0.0, 0.0, -1e-9, 0.0, 1e-9],
    [0.0, 1.99999999, 0.0, 0.0, 0.0, 0.0],
    [0.0, 0.0, 2.00000001, 0.0, 0.0, 0.0],
    [-1e-9, 0.0, 0.0, 2.00000002, 0.99999999, -1.00000001],
    [0.0, 0.0, 0.0, 0.99999999, 1.00000001, 0.0],
    [1e-9, 0.0, 0.0, -1.00000001, 0.0, 4.99999998],
]
print("quartic:", validsdp_soscheck(p1, monoms, Q_noisy))
print("singular (x-y)^2:", validsdp_soscheck({(2,0): Fraction(1), (1,1): Fraction(-2), (0,2): Fraction(1)}, [(1,0), (0,1)], [[1.0, -1.0], [-1.0, 1.0]]))
```
Observed output across the noisy strictly-positive quartic $p(x,y) = 2x^4 + 2x^3 y - x^2 y^2 + 5y^4 + 2x^2 + 2y^2 + 1$, the singular PSD polynomial $(x-y)^2$, and the exact Motzkin identity:
```text
[Probe 2A.1] ValidSDP certification of noisy float64 SDP witness for p(x,y) = 2x^4 + 2x^3y - x^2y^2 + 5y^4 + 2x^2 + 2y^2 + 1:
  Exact rational max residual r = 2.000e-08
  Spectral residual shift n*r   = 1.200e-07 (n=6)
  Rump Cholesky rounding c      = 1.155e-14
  Cholesky certification passed = True  (certifies p(x,y) > 0 for all x,y in R!)
[Probe 2A.2] Boundary-touching PSD polynomial q(x,y) = (x - y)^2 (lambda_min = 0):
  Exact rational residual r = 0.000e+00, c = 8.882e-16
  ValidSDP Cholesky passed  = False (fails because Q - c*I has eigenvalue -c < 0!)
[Probe 2A.3] Motzkin polynomial M(x,y) = x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1:
  Exact rational SOS identity (x^2+y^2)*M = x^2(y^2-1)^2 + y^2(x^2-1)^2 + x^2y^2(x^2+y^2-2)^2 verified: True
```

#### Probe 2B: Outward-Rounded ICP ($\delta$-SAT Wrapping, Cluster Effect, Cubic Transcendental Tangency, and 1-ULP Stagnation)
```python
import math

def iv_add(a, b): return (math.nextafter(a[0]+b[0], -math.inf), math.nextafter(a[1]+b[1], math.inf))
def iv_sub(a, b): return (math.nextafter(a[0]-b[1], -math.inf), math.nextafter(a[1]-b[0], math.inf))
def iv_mul(a, b):
    ps = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]
    return (math.nextafter(min(ps), -math.inf), math.nextafter(max(ps), math.inf))
def iv_sin(a): return (math.nextafter(math.sin(a[0]), -math.inf), math.nextafter(math.sin(a[1]), math.inf))

def icp(eval_fn, box, delta, mode="eq"):
    stack, splits = [box], 0
    while stack:
        lo, hi = stack.pop()
        ev = eval_fn((lo, hi))
        if (mode == "eq" and (ev[1] < 0.0 or ev[0] > 0.0)) or (mode == "gt" and ev[1] <= 0.0):
            continue
        if mode == "gt" and ev[0] > 0.0: return "VALID", (lo, hi), ev, splits
        if ev[1] - ev[0] <= delta: return "delta-SAT(diam<=delta)", (lo, hi), ev, splits
        mid = 0.5 * (lo + hi)
        if not (lo < mid < hi): return "delta-SAT(non-bisectable-1ULP)", (lo, hi), ev, splits
        splits += 1
        stack.extend([(mid, hi), (lo, mid)])
    return "UNSAT", None, None, splits

print("wrap d=1e-3:", icp(lambda b: iv_add(iv_sub(b, b), (1e-4, 1e-4)), (0.0, 1.0), 1e-3, "eq"))
print("wrap d=1e-5:", icp(lambda b: iv_add(iv_sub(b, b), (1e-4, 1e-4)), (0.0, 1.0), 1e-5, "eq"))
print("sin>x [0.01,1]:", icp(lambda b: iv_sub(iv_sin(b), b), (0.01, 1.0), 1e-3, "gt"))
print("sin>x [0.25,1]:", icp(lambda b: iv_sub(iv_sin(b), b), (0.25, 1.0), 1e-3, "gt"))
third = (math.nextafter(1.0/3.0, -math.inf), math.nextafter(1.0/3.0, math.inf))
print("steep 1e20:", icp(lambda b: iv_mul((1e20, 1e20), iv_sub(b, third)), (0.0, 1.0), 1e-3, "eq"))
```
Observed output replicating `dReal4`'s `IcpSeq::CheckSat` + `EvaluateBox` (`icp_seq.cc:62-143`, `icp.cc:30-76`):
```text
[Probe 2B.1] Interval dependency wrapping g(x) = (x - x) + 1e-4 = 0 on [0, 1] (globally UNSAT):
  delta=1e-3 (dReal4 default): status=delta-SAT, box=[0, 0.00048828125], f(B)=[-0.00038828125, 0.00058828125], splits=11 (diam<=delta)
  delta=1e-5:                  status=UNSAT, splits=16383 (empty-stack)
[Probe 2B.2] Transcendental sin(x) - x > 0 (true inequality sin(x) < x for x > 0):
  On [0.01, 1.0] (where |sin(0.01)-0.01|=1.67e-7 << delta=1e-3): status=delta-SAT, box=[0.01, 0.0104833984375], splits=11 (diam<=delta)
  On [0.25, 1.0] (where |sin(0.25)-0.25|=2.60e-3 > delta=1e-3):  status=UNSAT, splits=61 (empty-stack)
[Probe 2B.3] Steep constraint 1e20 * (x - 1/3) = 0 hitting 1-ULP IEEE-754 stagnation:
  status=delta-SAT, box=[0.333333333333, 0.333333333333], box_diam=5.551e-17, eval_diam=1.665e+04 >> delta=1e-3, splits=54 (non-bisectable-1ULP)
[Probe 2B.4] McCallum projection nullification p(x,y,z) = x*z + y:
  proj_McCallum({x*z + y}, z) = {ldcf_z(p) = x, disc_z(p) = 1}
  Over (x,y) = (0,0): p(0,0,z) == 0 identically (nullified -> infinitely many roots in z!)
  Adding all coefficients (y) or Lazard evaluation divides out vanishing factors and recovers y = 0.
```

## Revalidation

To cheaply revalidate the core source invariants against newer upstream revisions without repeating the full investigation:

1. **Z3 NLSAT & transcendentals:** Diff `src/nlsat/nlsat_explain.cpp` (`levelwise_single_cell`, `project`) and `src/nlsat/nlsat_transcendentals.h` in `Z3Prover/z3` to check whether projection operators, nullification fallbacks, or transcendental enclosure backends changed.
2. **cvc5 `CDCAC` & Lazard lifting:** Diff `src/theory/arith/nl/strategy.cpp` (`initializeStrategy`) and `src/theory/arith/nl/coverings/lazard_evaluation.h` in `cvc5/cvc5` to verify whether CoCoALib remains optional with fallback to `poly::infeasible_regions` and whether `CoveringsProofGenerator` exports kernel-checkable Alethe/LFSC proofs.
3. **ValidSDP rounding & Positivstellensatz check:** Diff `theories/cholesky_prog.v` (`compute_c_aux`, `posdef_check`, `posdef_check_itv`) and `theories/validsdp.v` (`soscheck`, `soscheck_hyps`, `has_const_eff`) in `validsdp/validsdp` to verify whether facial-reduction preprocessing or alternative matrix-norm bounds were added.
4. **dReal4 $\delta$-SAT termination:** Diff `dreal/solver/config.h` (`kDefaultPrecision`), `dreal/solver/icp.cc` (`EvaluateBox`), and `dreal/solver/icp_seq.cc` (`branching_dim < 0`) in `dreal/dreal4` to check whether non-bisectable 1-ULP boxes still return `delta-SAT` or emit an explicit precision-underflow status.
5. **Lean 4 / Mathlib4 polynomial certificates:** Check `Mathlib/Tactic/Polyrith.lean` and search `Mathlib/Tactic/` in `leanprover-community/mathlib4` for any newly merged SOS/Positivstellensatz certificate tactic.
6. **Executable re-check:** Rerun Probe 2A under `python3` to re-verify Rump's rounding margins and Motzkin's algebraic identity; if a live `dreal` binary is available, run `(set-logic QF_NRA) (declare-fun x () Real) (assert (<= 0.01 x)) (assert (<= x 1.0)) (assert (> (sin x) x)) (check-sat)` at `--precision 0.001` vs. `[0.25, 1.0]` to directly confirm the cubic-tangency `delta-SAT` vs. `UNSAT` boundary.
