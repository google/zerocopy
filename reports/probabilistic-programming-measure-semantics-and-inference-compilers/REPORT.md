# Probabilistic Programming: Measure-Theoretic Semantics, Conditioning Paradoxes, and Inference Compiler Verification

## Summary

Probabilistic Programming Languages (PPLs) denote measures and transition kernels rather than deterministic functions, creating four coupled semantic and compiler verification challenges:

1. **Higher-order denotational semantics (`Meas` vs. `Qbs` and s-finite kernels).** By Aumann's theorem (1961), the category `Meas` of measurable spaces is not Cartesian closed: no $\sigma$-algebra on $\mathrm{Meas}(\mathbb{R}, \mathbb{R})$ makes evaluation measurable. **Quasi-Borel spaces (`Qbs`)** (Heunen, Kammar, Staton & Yang, LICS 2017) replace $\sigma$-algebras with admissible random elements $M_X \subseteq X^{\mathbb{R}}$ to yield a Cartesian closed, well-pointed category that embeds standard Borel spaces fully and faithfully while supporting higher-order continuous distributions. Orthogonally, **s-finite kernels** (Staton, ESOP 2017) restore Fubini-Tonelli commutativity for unnormalized `score` kernels, validating statement reordering (though not dead-code discardability).
2. **Measure-zero conditioning ambiguity (Borel-Kolmogorov paradox).** Conditioning a continuous distribution on an equality $X = Y$ is ill-defined until a base measure (Radon-Nikodym disintegration) or limiting positive-measure family is fixed. For $X, Y \stackrel{\text{i.i.d.}}{\sim} \mathrm{Uniform}(0,1)$, $|X - Y| \le \epsilon$ converges to $\mathrm{Uniform}(0,1)$ ($\mathbb{E}[X] = 0.5$, Jacobian $1$), whereas $|X / Y - 1| \le \epsilon$ converges to $\mathrm{Beta}(2,1)$ ($\mathbb{E}[X] = 2/3$, Jacobian $x$). **Hakaru** (Shan & Ramsey, POPL 2017; `hakaru-dev/hakaru`) resolves this via symbolic disintegration relative to a base measure, emitting inverse-Jacobian weights and failing closed (`bot`) on point masses without Lebesgue density; **Jacobs** (POPL 2021) models null-set observations through explicit infinitesimal limits.
3. **Continuous HMC and SVI compiler invariants (`Stan`, `Pyro`, `pyppai`).** HMC/NUTS requires smooth, fixed-dimension, unconstrained $\mathbb{R}^K$ densities. `stan-dev/stanc3` (`v2.40.0`) statically bans integer parameters and automatically lowers 18 built-in parameter constraints with `if constexpr (jacobian__)` adjustments, while relegating nonlinear `~` LHS and parameter-dependent control flow to opt-in `--warn-pedantic` heuristics and leaving manual `jacobian +=` values unverified. In SVI, minimizing $\mathrm{KL}(q_\phi \| p(\cdot \mid y))$ requires $q_\phi \ll p$ ($\mathrm{supp}(q_\phi) \subseteq \mathrm{supp}(p)$). `pyro-ppl/pyro`'s runtime `check_model_guide_match` validates site names and tensor shapes but omits support containment; static abstract interpretation (`pyppai`, Lee, Yu, Rival & Yang, POPL 2020) caught a live Pyro Bayesian Regression bug (`Uniform(0, 10)` model vs. `Normal(1.0, 0.05)` guide) where $\mathrm{KL}(q \| p) = +\infty$ is silently masked across $10^5$ Monte Carlo ELBO draws ($P_{\text{escape}} \approx 2.75 \times 10^{-89}$).
4. **Exact discrete WMC compilation (`Dice`) vs. programmable inference (`Gen` GFI and Trace Types).** **Dice** (Holtzen, Van den Broeck & Millstein, OOPSLA 2020; `SHoltzen/dice`) compiles discrete programs into dual BDDs—value tree $\dot{\varphi}$ and branch-guarded accepting formula $\gamma$—for linear-time Weighted Model Counting (WMC). Exact Dice inference is **PSPACE-hard** (beyond **PP-complete** / **#P-hard** Bayesian networks), scaling as $O(k)$ on factored Markov chains but hitting exact $2^k$ cut-width blowup on separated or dense parity couplings. **Gen** (Cusumano-Towner et al., PLDI 2019; `probcomp/Gen.jl` `v0.4.9`) exposes the **Generative Function Interface (GFI)** (`simulate`, `generate`, `project`, `propose`, `assess`, `update`, `regenerate`) and automates transdimensional **involutive MCMC** via `ForwardDiff.jacobian` plus opt-in dynamic round-trip checks (`check=true`), while **Trace Types** (Lew et al., POPL 2020) statically enforce absolute continuity and Radon-Nikodym weight exactness over `Qbs`.

## Applicability

This report characterizes PPL measure semantics, conditioning soundness, and inference-compiler guarantees across 17 durable primary subjects (11 foundational papers and 6 pinned upstream repositories):

- **Higher-order denotational foundations:** Aumann (1961), Heunen et al. (LICS 2017), Staton (ESOP 2017).
- **Measure-zero conditioning & symbolic disintegration:** Shan & Ramsey (POPL 2017), `hakaru-dev/hakaru` (`e8bebac6d344e81a429c25f2b4c29b76172ea47f`), Jacobs (POPL 2021).
- **Continuous gradient & variational inference compilers/verifiers:** Carpenter et al. (2017), `stan-dev/stanc3` `v2.40.0` (`456130a900c56ddb0505c4540460977106bd9938`), Lee et al. (POPL 2020), `wonyeol/static-analysis-for-support-match` (`pyppai`, `850fb58ec5ce2f5e82262c2a9bfc067b799297c1`), `pyro-ppl/pyro` (`a31bc1784707268cd79df77ead4c7a47062f0193`).
- **Exact discrete WMC & programmable trace-based inference:** Holtzen et al. (OOPSLA 2020), `SHoltzen/dice` (`1d8a277636a428eb46164ba4639fab12a310f30c`), Cusumano-Towner et al. (PLDI 2019), `probcomp/Gen.jl` `v0.4.9` (`9953ceb296b56ad5cd225d811a9fdfc8470b17e5`), Lew et al. (POPL 2020), Cusumano-Towner, Lew & Mansinghka (2020).

**Cross-version distinctions:**
- `SHoltzen/dice`: The OOPSLA 2020 paper targets CUDD; pinned revision `1d8a277636a428eb46164ba4639fab12a310f30c` binds Rust `rsdd` via `ocaml-ctypes` (`lib/Bdd.ml`) while leaving a legacy `Cudd` call in `lib/Passes.ml:198`. Core dual-BDD compilation rules are shared.
- `stan-dev/stanc3`: `v2.40.0` adds explicit `jacobian +=` statements and `_jacobian` UDF suffixes beyond the 2017 JSS paper while preserving the integer-parameter ban and `log_prob_impl<propto__, jacobian__, ...>` lowering.
- `probcomp/Gen.jl`: `v0.4.9` implements the PLDI 2019 GFI and 2020 `@transform` involutive MCMC DSL, but does **not** enforce POPL 2020 Trace Types statically; checks remain opt-in dynamic assertions (`check=true`).
- `support/verify_ppl_conditioning_and_wmc.py` is a self-contained Python 3.10+ semantic probe verifying exact ROBDD/WMC agreement and $2^k$ parity blowup, Borel-Kolmogorov discrepancies, and SVI support-check vs. Monte Carlo masking; it validates the mathematical models directly rather than invoking OCaml/Julia/C++ binaries.

**Adjacent corpus packages (cross-referenced without duplicating domain inventories):**
- `anneal-synbio-crns-pde-physics-math-and-rail-survey` covers `WebPPL`/RSA pragmatics, `OpenDP` differential privacy, causal do-calculus, and `Enzyme` autodiff pipelines.
- `semantic-models-lenses-hyperproperties-and-putnam-tcb-boundary` treats general denotational models, behavioral codecs, relational framing, and trust boundaries; this report supplies the measure-theoretic specialization when boundary semantics are measures or Markov kernels.

## Findings

### 1. Higher-Order Measure Semantics: Aumann's Obstruction, Quasi-Borel Spaces, and s-Finite Kernels

Basis: normative (Aumann 1961, Heunen et al. LICS 2017, Staton ESOP 2017) + derived

#### 1.1 Why `Meas` Fails Cartesian Closure (Aumann 1961)

Classical probability models spaces as pairs $(X, \Sigma_X)$ with measurable maps forming the category `Meas` and distributions forming the Giry monad $\mathcal{G}(X)$. Higher-order PPLs, however, define distributions over functions (Gaussian processes, Dirichlet processes, stochastic memoization, and inference combinators taking model functions as arguments).

**Aumann's theorem (1961)** proves that `Meas` is **not Cartesian closed**: for uncountable standard Borel spaces such as $\mathbb{R}$, no $\sigma$-algebra $\Sigma$ on $\mathrm{Meas}(\mathbb{R}, \mathbb{R})$ (or even $\{0,1\}^{\mathbb{R}}$) makes the canonical evaluation map

$$\mathrm{eval} : (\mathrm{Meas}(\mathbb{R}, \mathbb{R}), \Sigma) \times (\mathbb{R}, \mathcal{B}(\mathbb{R})) \longrightarrow (\mathbb{R}, \mathcal{B}(\mathbb{R})), \qquad \mathrm{eval}(f, x) = f(x)$$

jointly measurable. Currying therefore fails semantically: a measurable kernel $X \times Y \to \mathcal{G}(Z)$ cannot in general be internalized as a measurable map $X \to (\mathcal{G}(Z))^Y$, blocking compositional denotational semantics for a higher-order probabilistic $\lambda$-calculus with continuous distributions.

#### 1.2 Quasi-Borel Spaces (`Qbs`, Heunen, Kammar, Staton & Yang, LICS 2017)

Heunen et al. bypass Aumann's negative result by axiomatizing admissible *random elements* $\mathbb{R} \to X$ instead of measurable subsets of $X$. A **quasi-Borel space (QBS)** is a pair $(X, M_X)$ with $M_X \subseteq X^{\mathbb{R}}$ satisfying three closure axioms:

1. **Constants:** Every constant map $\lambda r.\, x$ is in $M_X$.
2. **Borel precomposition:** If $\alpha \in M_X$ and $f : \mathbb{R} \to \mathbb{R}$ is Borel-measurable, then $\alpha \circ f \in M_X$.
3. **Countable disjoint gluing:** If $\mathbb{R} = \biguplus_{n \in \mathbb{N}} S_n$ is a countable Borel partition and $\alpha_n \in M_X$, then $\alpha(r) = \alpha_n(r)$ on $S_n$ belongs to $M_X$.

A `Qbs` **morphism** $f : (X, M_X) \to (Y, M_Y)$ satisfies $\forall \alpha \in M_X.\, f \circ \alpha \in M_Y$. Key consequences:

- **Cartesian closure & well-pointedness:** Finite products take $M_{X \times Y} = \{ (\alpha, \beta) \mid \alpha \in M_X, \beta \in M_Y \}$ (using a Borel isomorphism $\mathbb{R} \cong \mathbb{R} \times \mathbb{R}$). Exponentials $(Y^X, M_{Y^X})$ set $Y^X = \mathrm{Qbs}(X, Y)$ with $M_{Y^X} = \{ \gamma : \mathbb{R} \to \mathrm{Qbs}(X, Y) \mid \mathrm{uncurry}(\gamma) \in \mathrm{Qbs}(\mathbb{R} \times X, Y) \}$. Evaluation is a `Qbs` morphism by construction, restoring $\beta\eta$-equational reasoning.
- **Full-and-faithful standard Borel embedding:** An adjunction $L \dashv R : \mathbf{Qbs} \rightleftarrows \mathbf{Meas}$ sends $(X, \Sigma_X) \mapsto (X, \mathrm{Meas}(\mathbb{R}, X))$. Restricted to **standard Borel spaces** (`StdBorel`—Polish spaces with Borel $\sigma$-algebras, covering $\mathbb{R}^n$, countable discrete spaces, and countable products/coproducts), the embedding is **full and faithful**, so `Qbs` agrees identically with classical measure theory on first-order spaces while adding function spaces.
- **Commutative probability monad $P$:** Distributions on $(X, M_X)$ are equivalence classes $[\alpha, \mu]$ of $\alpha \in M_X$ and a Borel probability measure $\mu$ on $\mathbb{R}$ modulo pushforward equality ($\int f(\alpha(r))\,\mu(dr)$ agreeing for all morphisms $f : X \to [0, \infty]$). $P$ forms a strong commutative monad on `Qbs` (satisfying Fubini) and supports a categorical generalization of de Finetti's theorem.
- **General recursion (`ωQbs`):** Equipping `Qbs` with $\omega$-cpos yields $\omega$-quasi-Borel spaces (Vákár, Kammar & Staton, POPL 2019, DOI `10.1145/3290349`), modeling general recursion, recursive trace types, and soft conditioning.

#### 1.3 Commutativity of Unnormalized Scoring via s-Finite Kernels (Staton, ESOP 2017)

PPLs with soft conditioning (`score(w)` / `target += lp`) denote unnormalized measures. Compiler optimizations (reordering independent draws, CSE, partial evaluation) require **commutativity** (Fubini-Tonelli):

$$\text{let } x = e_1 \text{ in let } y = e_2 \text{ in } e_3 \;\equiv\; \text{let } y = e_2 \text{ in let } x = e_1 \text{ in } e_3 \qquad (x \notin \mathrm{FV}(e_2),\, y \notin \mathrm{FV}(e_1)).$$

General $\sigma$-finite kernels are **not** closed under marginalization/pushforward (integrating out a uniform draw on $\mathbb{R}$ with constant score yields an everywhere-infinite measure), breaking Fubini composition. Staton (ESOP 2017) uses **s-finite kernels**—countable sums of finite kernels $\kappa = \sum_{n=0}^{\infty} \kappa_n$—which:
1. Close under Kleisli composition and marginalization;
2. Satisfy exact Fubini-Tonelli interchange even with arbitrary `score` and improper priors (`lebesgue`);
3. Remain **non-affine** (not discardable): dead-code elimination of `let _ = e1 in e2` is unsound whenever `e1` can execute `score(w)` ($w \neq 1$), `observe(false)`, or diverge with positive probability, requiring a purity/normalizing effect check before DCE.

---

### 2. Measure-Zero Conditioning, Borel-Kolmogorov Paradox, and Symbolic Disintegration

Basis: normative (Shan & Ramsey POPL 2017, Jacobs POPL 2021) + source (`hakaru-dev/hakaru`) + execution (`support/verify_ppl_conditioning_and_wmc.py`)

#### 2.1 Borel-Kolmogorov Coordinate-Change Discrepancy

Conditioning a continuous pair $(X, Y)$ on $g(X, Y) = 0$ conditions on a null set $E$ ($P(E) = 0$). Shrinking a naive $\epsilon$-ball $|g(X, Y)| \le \epsilon$ makes the limiting posterior depend on the algebraic parameterization $g$, even when two predicates define the identical set $E$.

For $X, Y \stackrel{\text{i.i.d.}}{\sim} \mathrm{Uniform}(0, 1)$ conditioned on the diagonal $E = \{x = y\}$ (and the classical $S^2$ great circle):

| Conditioning Parameterization | $\epsilon$-Neighborhood | Local Slice Width $L(x)$ | Jacobian $\left|\frac{\partial y}{\partial u}\right|_{y=x}$ | Limiting Density | $\mathbb{E}[X \mid E]$ | $P(X \le \frac{1}{2} \mid E)$ |
| --- | --- | --- | --- | --- | --- | --- |
| Additive: $U = X - Y = 0$ | $\|X - Y\| \le \epsilon$ | $2\epsilon$ (uniform band) | $1$ | $1$ — $\mathrm{Uniform}(0,1)$ | $0.500000$ | $0.500000$ |
| Ratio: $V = X / Y = 1$ | $\|X / Y - 1\| \le \epsilon$ | $\frac{2\epsilon x}{1 - \epsilon^2} \sim 2\epsilon x$ (wedge) | $x$ | $2x$ — $\mathrm{Beta}(2,1)$ | $2/3 \approx 0.666667$ | $0.250000$ |
| Spherical meridian ($\phi = 0$) | $\|\phi\| \le \epsilon$ | $2\epsilon \cos\theta$ (pinched at poles) | $\cos\theta$ | $\frac{1}{2}\cos\theta$ on $[-\frac{\pi}{2},\frac{\pi}{2}]$ | $\mathbb{E}[\|\sin\theta\|] = 0.500000$ | — |
| Spherical equator ($\theta = 0$) | $\|\theta\| \le \epsilon$ | $2\epsilon$ (uniform band) | $1$ | $\frac{1}{\pi}$ on $[-\frac{\pi}{2},\frac{\pi}{2}]$ | $\mathbb{E}[\|\sin\psi\|] = \frac{2}{\pi} \approx 0.636620$ | — |

In `support/verify_ppl_conditioning_and_wmc.py` (Probe 2), closed-form finite-$\epsilon$ integrals ($\epsilon \in \{0.1, 0.05, 0.01, 0.002, 0.0005\}$) and deterministic $550 \times 550$ midpoint quadrature at $\epsilon = 0.01$ confirm:
- $|X - Y| \le 0.01$: $\mathbb{E}[X] = 0.500000$, $P(X \le 0.5) = 0.500000$.
- $|X / Y - 1| \le 0.01$: analytical $\mathbb{E}[X] = 0.664992$, quadrature $\mathbb{E}[X] = 0.662257$ (converging to $0.666583 \to 2/3$ at $\epsilon = 0.0005$), quadrature $P(X \le 0.5) = 0.255354$ (converging to $0.250063 \to 0.25$).
- Spherical great circle: $\mathbb{E}[|\sin\theta|] = 0.500000$ (meridian) vs. $0.636620$ (equator).

**Why naive density scoring fails:** Lowering `observe(f(z) == c)` to prior density evaluation drops the inverse-Jacobian / coarea factor $|\det J_f|^{-1}$ dictated by the disintegrated variable $U = f(X, Y)$. Worse, mixing discrete `observe` (dimensionless probability mass under counting measure) and continuous `observe` (density with units $\text{length}^{-1}$ under Lebesgue measure) across `if` branches makes posterior branch odds change arbitrarily under unit rescaling (e.g., meters vs. centimeters; Jacobs, POPL 2021).

#### 2.2 Symbolic Disintegration in `Hakaru` (Shan & Ramsey, POPL 2017)

Shan & Ramsey (POPL 2017) replace ambiguous null-set `observe` with **symbolic disintegration** of a joint measure $\xi \in \mathcal{M}(A \times B)$ relative to an explicit base measure $\nu$ on $A$, computing a measurable kernel $\kappa : A \to \mathcal{M}(B)$ satisfying

$$\xi = \int_A (\delta_a \otimes \kappa(a))\, d\nu(a), \qquad \text{i.e., } \texttt{m == bindx lebesgue n}.$$

Disintegrating `(x - y, x)` against Lebesgue and evaluating at `0` yields $\mathrm{Uniform}(0,1)$, whereas disintegrating `(x / y, x)` and evaluating at `1` automatically emits the Jacobian factor `x` and yields $\mathrm{Beta}(2,1)$.

Direct inspection of `hakaru-dev/hakaru` (`e8bebac6d344e81a429c25f2b4c29b76172ea47f`, `haskell/Language/Hakaru/Disintegrate.hs`) shows the exact compiler mechanics:
- **API & measurable kernel typing (`L151-227`):** `disintegrateWithVar` binds a fresh observation variable $x$, runs lazy partial evaluation (`perform m`), splits the pair (`emitUnpair`), propagates constraints backward (`constrainValue (var x) a`), and returns candidate kernels `[abt '[] (a ':-> 'HMeasure b)]` typed with Hakaru's measurable arrow `':->`.
- **Fail-closed rejection of singular point masses (`L533-549, 963`):** Constraining `Literal_ v` or `Pi` against ambient Lebesgue returns `bot` because `dirac v` lacks a Lebesgue density; uninvertible `Dirac`, `MBind`, `Superpose_`, and `Reject_` terms also return `bot`.
- **Inverse-Jacobian emission (`L870-1060`):**
  - `Sum` (`L878-882`): picks one summand `e` via `lubSeq`, atomizes cofactor sum `u`, recurses `constrainValue (v0 - u) e`.
  - `Prod` (`L883-889`): atomizes cofactor product `u`, emits weight `emitWeight (P.recip (toProb_abs theSemi u'))` ($1/|u|$), recurses `constrainValue (v0 / u') e`.
  - `Max` (`L890-894`): branches via `chooseSeq`, emits guard `u < v0`, constrains `e` to `v0`.
  - Nonlinear primitives (`L965-1060`): `Sin`/`Cos` emit countable branch superpositions via `counting`, guard `-1 < x0 < 1`, and weight `1 / sqrt(1 - x0^2)`; `Tan` emits `1 / (1 + x0^2)`; `Atan` emits `1 / cos(x0)^2`; `RealPow` emits log/power derivative reciprocals.
- **Primitive base cases (`L1236-1296`):** `constrainOutcomeMeasureOp` replaces `Lebesgue`, `Uniform`, `Normal`, `Gamma`, `Beta`, `Poisson`, and `Categorical` with exact support guards and densities.
- **Documented limitations (`L30-42, 525-530, 554-565`):** To avoid going forward and backward on the same heap-bound variable, `Disintegrate.hs` requires one argument of binary ops like `x * y` to have zero Jacobian—preventing automatic disintegration of coupled multi-path nonlinearities—does not yet emit range guards for `CoerceTo_`, and errors on `Lam_`, `App_`, `Integrate`, and `Summate`.

#### 2.3 Infinitesimal Conditioning (Jacobs, POPL 2021)

Jacobs (POPL 2021) resolves density/unit conditioning paradoxes by treating every continuous observation as an explicit limit of positive-measure sets carrying **infinitesimal probabilities** ($dx$). Dimensionally mismatched branches ($O(1)$ discrete mass vs. $O(dx)$ continuous density) separate by infinitesimal order rather than summing incompatible units, and reparameterizations automatically multiply by $df = f'(x)\,dx$.

---

### 3. Continuous HMC/NUTS Compilers: `Stan` (`stanc3`) Constraints, Jacobians, and Discontinuity Hazards

Basis: normative (Carpenter et al. 2017, Hoffman & Gelman 2014) + source (`stan-dev/stanc3` `v2.40.0` at `456130a900c56ddb0505c4540460977106bd9938`) + derived

#### 3.1 Mathematical Preconditions and the HMC vs. Pathwise-AD Distinction

HMC and NUTS (Hoffman & Gelman 2014) simulate Hamiltonian dynamics $H(q, p) = -\log \pi(q) + \frac{1}{2} p^\top M^{-1} p$ over unconstrained $q \in \mathbb{R}^K$ using reversible, volume-preserving leapfrog steps driven by reverse-mode AD of $\nabla_q \log \pi(q)$. Soundness and efficient exploration require: (1) fixed continuous dimension $K$ (no discrete latents or varying-dimension traces), (2) smooth bijections $T : \mathbb{R}^M \to \mathcal{C}$ adding $\log |\det J_T(\eta)|$ during MCMC (`jacobian__ = true`) while omitting it for constrained-space MAP (`jacobian__ = false`), and (3) $C^1$ smoothness of $\log \pi(q)$.

**Discontinuity failure modes (HMC vs. pathwise VI gradients):** In Metropolis-adjusted fixed-step HMC, a symmetric leapfrog map over a piecewise-smooth density can remain reversible almost everywhere, so asymptotic detailed balance is not automatically violated by a jump—**yet** energy conservation breaks instantaneously at the jump (zero piecewise gradient impulse across a finite potential jump $\Delta U$), causing massive rejections, mode trapping, and **NUTS divergent transitions** (`divergent__ = 1`, creating severe finite-sample bias). Crossing discontinuities smoothly requires boundary-detecting Reflective/Refractive HMC (Afshar & Domke 2015) or Discontinuous HMC (Nishimura, Dunson & Lu 2020), which fixed-step AD engines do not implement. Conversely, in **pathwise VI gradient estimators** differentiating $\nabla_\phi \mathbb{E}_{z \sim q_\phi}[f(z)]$ through an `if` branch, dropping the boundary Dirac-delta term yields a **strictly biased** gradient even asymptotically (addressed by boundary-aware AD such as `ADEV`, Lew, Huot, Staton & Mansinghka, POPL 2023, DOI `10.1145/3571198`).

#### 3.2 Concrete Compiler Enforcement and Gaps in `stan-dev/stanc3` (`v2.40.0`)

| HMC / Measure Precondition | `stanc3` Mechanism | Source Location (`stan-dev/stanc3`) | Enforcement Level & Soundness Gap |
| --- | --- | --- | --- |
| **No discrete latent parameters** | `verify_transformed_param_ty` rejects `int` anywhere inside `parameters` or `transformed parameters` (`"Parameters cannot be integers."` / `"Transformed parameters cannot be integers."`). | `src/frontend/Typechecker.ml:1894-1899`, `src/frontend/Semantic_error.ml:825, 986-988, 1305-1306` | **Hard compile error.** Forces manual marginalization ($O(D^k)$ for $k$ coupled discrete latents). |
| **Built-in constrained bijections + Jacobians** | 18 `Transformation.t` constructors (`Lower`, `Upper`, `LowerUpper`, `Offset`, `Multiplier`, `OffsetMultiplier`, `Ordered`, `PositiveOrdered`, `Simplex`, `UnitVector`, `SumToZero`, `CholeskyCorr`, `CholeskyCov`, `Correlation`, `Covariance`, `StochasticRow`, `StochasticColumn`, `TupleTransformation`) lower to `read_constrain_<c><..., jacobian__>(..., lp__)` inside `log_prob_impl<propto__, jacobian__, VecR, VecI>`. | `src/middle/Transformation.ml:9-34`, `src/stan_math_backend/Lower_expr.ml:420-435`, `Lower_program.ml:226-244, 276-278` | **Automatic & toggleable.** `write_array_impl` fixes `constexpr bool jacobian__ = false`. |
| **User-defined `jacobian +=` & `_jacobian` UDFs** | `verify_jacobian_pe_usage` / `verify_fn_jacobian_plus_equals` restrict usage to `transformed parameters` or `FnJacobian`; backend emits `if constexpr (jacobian__) { lp_accum__.add(e); }`. | `src/frontend/Typechecker.ml:62-65, 457-469, 1241-1249`, `Semantic_error.ml:917-920`, `Lower_stmt.ml:290-294` | **Placement-checked only.** Compiler never verifies that `e` equals the true $\log |\det J|$ of the transform. |
| **Missing Jacobian on nonlinear LHS of `~`** | `maybe_jacobian_adjustment_warnings` checks syntactic `is_linear true e` on `TargetPE (FunApp (FnDist _, e :: _))`. | `src/analysis_and_optimization/Pedantic_analysis.ml:74-135, 389-400` | **Opt-in (`--warn-pedantic`).** Local-only: `Var _` returns `allow_var = true` (`L88`), so `y = exp(theta); y ~ normal(0, 1);` silently bypasses the warning! |
| **Parameter-dependent control flow** | `list_param_dependant_cf` and `list_param_dependant_fundefs_cf` trace backward dataflow dependencies from control flow to `parameters` (including UDF calls). | `src/analysis_and_optimization/Pedantic_analysis.ml:158-269, 415-442` | **Opt-in (`--warn-pedantic`).** Warns only; cannot separate smooth piecewise splices from jump discontinuities. |
| **Hard lower+upper parameter bounds** | `hard_constrained_warnings` warns that logit/hard constraints induce exploding boundary curvature/gradients. | `src/analysis_and_optimization/Pedantic_analysis.ml:367-387` | **Opt-in (`--warn-pedantic`).** |

---

### 4. Stochastic Variational Inference Verification: Support Violations and Silent Monte Carlo Masking (`Pyro` and `pyppai`)

Basis: normative (Lee, Yu, Rival & Yang POPL 2020) + source (`pyro-ppl/pyro`, `wonyeol/static-analysis-for-support-match`) + execution (`support/verify_ppl_conditioning_and_wmc.py`)

#### 4.1 Measure-Theoretic Conditions for Valid SVI

SVI maximizes the Evidence Lower Bound $\mathcal{L}(\phi) = \mathbb{E}_{z \sim q_\phi}[\log p(x, z) - \log q_\phi(z)] = \log p(x) - \mathrm{KL}(q_\phi(z) \| p(z \mid x))$. Soundness requires three trace-level invariants:

1. **Address correspondence:** Every unenumerated latent site in `model` appears in `guide`, and every non-auxiliary site in `guide` appears in `model`.
2. **Absolute continuity ($q_\phi \ll p$) and support containment ($\mathrm{supp}(q_\phi) \subseteq \mathrm{supp}(p)$):** If $q_\phi$ assigns positive mass outside $\mathrm{supp}(p)$, then $\mathrm{KL}(q_\phi \| p(\cdot \mid x)) = +\infty$ and $\mathcal{L}(\phi) = -\infty$. (Conversely, importance sampling and MH proposals require reverse dominance $p \ll q$, i.e. $\mathrm{supp}(p) \subseteq \mathrm{supp}(q)$; exact match $\mathrm{supp}(q) = \mathrm{supp}(p)$ satisfies both.)
3. **Reference-measure compatibility:** Both $q_\phi$ and $p$ at a site must share a common reference measure (Lebesgue on $\mathbb{R}$, simplex $\Delta^{K-1}$, or counting measure). Pairing a continuous `Dirichlet` prior with a point-mass `Delta` guide creates mutual singularity ($\delta_c \perp \lambda_{\Delta^{K-1}}$).

#### 4.2 Pyro Runtime Checks vs. Static Abstract Interpretation (`pyppai`)

In `pyro-ppl/pyro` (`a31bc1784707268cd79df77ead4c7a47062f0193`), `check_model_guide_match` (`pyro/util.py:314-425`) checks **only** site-name inclusion (modulo `is_auxiliary` / `_enumerate_dim`), `event_dim`, and tensor `shape`, while `Trace_ELBO` (`pyro/infer/trace_elbo.py:71-159`) averages empirical particle log-ratios and calls `warn_if_nan`. **Pyro performs no distributional support-containment or singularity checks.**

Lee, Yu, Rival & Yang (POPL 2020) build the OCaml abstract interpreter `pyppai` (`wonyeol/static-analysis-for-support-match`, `850fb58ec5ce2f5e82262c2a9bfc067b799297c1`). In `pyppai/main.ml:89-103`, `pyppai` stacks APRON numerical domains (`PA_box` / `PA_oct` / `PA_pol`), a tensor Zone domain (`Adom_zone`), a distribution-type domain (`Adom_distty`), and a fibered product (`Adom_fib`). Its relational check `Adom_fib.is_related` (`adom_fib.ml:1621-1661`) verifies exact must/may random-variable sets, numerical bounds, tensor zones, and `Adom_distty.is_related_dist_lat` (`adom_distty.ml:187-190`), which invokes `Ir_util.dist_kind_support_subseteq dk2 dk1` (`ir_util.ml:64-99`) to prove $\mathrm{supp}(\text{guide}) \subseteq \mathrm{supp}(\text{model})$ (`Normal` dominates `Normal`/`Exponential`/`Gamma`/`Beta`/`Uniform`; `Uniform(l2, u2)` dominates `Uniform(l1, u1)` iff $l_2 \le l_1 \land u_1 \le u_2$; `Dirichlet(k)` matches only `Dirichlet(k)`).

Across 12 official Pyro example pairs (9 valid, 3 invalid) and 39 Pyro test-suite pairs (20 valid, 3 invalid, 8 error, 8 crash; `README.txt:158-206`), `pyppai` exposed two mislabeled suite tests (`nested_plate_plate_dim_error_1` and `_3`, actually valid) and two real semantic flaws in official Pyro examples:

1. **Bayesian Regression support violation (`tests/pyro_examples/br_original_modelguide.py:7, 10, 25`):**
   ```python
   # model:
   sigma = pyro.sample("sigma", dist.Uniform(0., 10.))
   pyro.sample("obs", dist.Normal(mean, sigma), obs=log_gdp)
   # guide:
   sigma_loc = pyro.param('sigma_loc', torch.tensor(1.), constraint=constraints.positive)
   sigma = pyro.sample("sigma", dist.Normal(sigma_loc, torch.tensor(0.05)))
   ```
   Here $\mathrm{supp}(q_\sigma) = \mathbb{R} \not\subseteq [0, 10] = \mathrm{supp}(p_\sigma)$, so exact $\mathrm{KL}(q \| p) = +\infty$. At initialization (`loc=1.0, scale=0.05`), `0.0` is $20\sigma$ away ($P_{\text{escape}} = \Phi(-20) + \Phi(-180) \approx 2.75 \times 10^{-89}$).
   - **Probe 3 verification (`support/verify_ppl_conditioning_and_wmc.py`):** Over $100{,}000$ deterministic Monte Carlo draws (`seed=20261119`), `0` samples exit $[0, 10]$, silently producing a plausible finite empirical ELBO `-3.881020` (matching $-\log 10 + H(\mathcal{N}(1, 0.05^2)) \approx -3.8794$). Once SGD shifts `loc` to `0.15` ($3\sigma$ from `0`), `106 / 100,000` draws escape ($P_{\text{escape}} = 0.001350$), abruptly collapsing the ELBO to `-inf`. Static analysis rejects the pair deterministically and accepts the corrected `Uniform(0.1, 10.)` pair (`br_model1.py:25`, `br_guide1.py:41`).
2. **LDA singular Dirac-Delta guide (`tests/pyro_examples/lda_original_modelguide.py:18, 75`):**
   `model` samples `doc_topics ~ dist.Dirichlet(topic_weights)` while `guide` uses `dist.Delta(doc_topics, event_dim=1)` (point-mass MAP/amortized inference), flagged by both `pyppai` and Probe 3 as `MEASURE_SINGULARITY`.

---

### 5. Exact Discrete Inference via Knowledge Compilation and Weighted Model Counting (`Dice`)

Basis: normative (Holtzen, Van den Broeck & Millstein OOPSLA 2020) + source (`SHoltzen/dice` at `1d8a277636a428eb46164ba4639fab12a310f30c`) + execution (`support/verify_ppl_conditioning_and_wmc.py`)

#### 5.1 Dual-BDD Compilation and Correctness Theorem

**Dice** compiles discrete probabilistic programs compositionally into Reduced Ordered Binary Decision Diagrams (ROBDDs) separating logical structure from numeric flip parameters:
- `state : bddptr btree` ($\dot{\varphi}$, `lib/Compiler.ml:10-13`): BDD tree encoding the unnormalized return value (leaves for Booleans, binary trees for tuples and bitvector integers).
- `z : bddptr` ($\gamma$, `lib/Compiler.ml:12`): **accepting formula**, true on flip assignments satisfying all dynamically executed `observe` statements.
- `weights` ($w$, `lib/Wmc.ml:5`): `(1 - theta, theta)` pairs per `Flip(theta)` (`lib/Compiler.ml:124-131`).

**Theorem 4.6 (Compilation Correctness, Holtzen et al. OOPSLA 2020):** If $\emptyset, \emptyset \vdash p : \tau \leadsto (\dot{\varphi}, \gamma, w)$, then $\llbracket p \rrbracket_A = \mathrm{WMC}(\gamma, w)$ and $\llbracket p \rrbracket_D(v) = \mathrm{WMC}((\dot{\varphi} \Leftrightarrow_\tau v) \wedge \gamma, w) / \mathrm{WMC}(\gamma, w)$. Once compiled, memoized bottom-up WMC runs in **$O(|\text{BDD}|)$ linear time** (`lib/Wmc.ml:18-35`).

#### 5.2 Compiler Rules and Subtle Implementation Caveats (`SHoltzen/dice`)

1. **Branch-guarded observations (`lib/Compiler.ml:93-108`):** `Ite(g, thn, els)` computes
   ```ocaml
   let z' = Bdd.bdd_and ctx.man cg.z (Bdd.bdd_ite ctx.man gbdd cthn.z cels.z)
   ```
   preventing observations in untaken branches from constraining taken branches (verified in Probe 1: exact rational posterior $1/4$, $Z = 1/2$).
2. **Modular function compilation (`lib/Compiler.ml:180-246`):** Functions are compiled once in topological order with symbolic placeholder arguments (`gen_sym_type`); each `FuncCall` allocates fresh `new_flips`, rewrites BDDs via `bdd_vector_compose`, and substitutes arguments via `subst_state`.
3. **Semiring modes (`lib/Wmc.ml:36-41`, `lib/Compiler.ml:249-254`):** Supports `wmc_type=0` (log-probability floats, default in `get_prob` to avoid underflow at the cost of float rounding), `1` (exact rational `Bignum`), and `2` (IEEE-754 float).
4. **Backend evolution & unimplemented ops (`lib/Bdd.ml:8-48`, `lib/Compiler.ml:161`, `lib/Passes.ml:198`):** The pinned 2025 codebase binds Rust `rsdd` via `ocaml-ctypes` (replacing the OOPSLA 2020 CUDD backend, though `Passes.ml:198` still references `Cudd.Bdd`); `Sample(e)` raises `failwith "not implemented"`.
5. **Silent recursion tail truncation (`lib/Passes.ml:9, 67-106`):** `expand_recursion` unrolls self-recursion up to `default_recursion_limit = 10` and terminates the base copy with `Observe(False)` (`unreachable`), silently conditioning away deeper execution paths and biasing the posterior whenever tail probability exceeds zero.

#### 5.3 Complexity Bounds and Empirical Linear vs. $2^k$ Regimes

- **Theorem 6.1 (OOPSLA 2020):** Exact inference in Dice with procedures is **PSPACE-hard** (strictly harder than **PP-complete** / **#P-hard** Bayesian network inference).
- **Proposition 6.2 (OOPSLA 2020):** While general BDD conjunction takes $O(|B_1| \times |B_2|)$, two BDDs conditionally independent given a single separator variable $z$ compose in **$O(|B_1| + |B_2|)$** under a compatible variable order. Dice also exploits context-specific independence and local logical structure regardless of numeric flip values—unlike Algebraic Decision Diagrams (ADDs), which explode to the full path count when flip weights are generic (OOPSLA 2020 §6.3).

**Probe 1 execution results (`support/verify_ppl_conditioning_and_wmc.py`):** Exact `Fraction` ROBDD WMC agrees identically with $2^n$ enumeration (`ObsProg` = `5/6`, $Z = 18/25$; Burglary-Alarm BN = `592242590/2084100239` $\approx 0.284172$ in 12 nodes) and isolates linear vs. exponential scaling:

| Benchmark Family | Size $k$ | Paths | Good-Order Nodes (Max Width) | Coupled / Separated Nodes | Cut Width at Level $k$ | Enum Check |
| --- | --- | --- | --- | --- | --- | --- |
| Factored Markov Chain | 2 / 4 / 8 / 16 | $2^5$..$2^{33}$ | 12 / 22 / 42 / 82 (width 2) | — | — | Exact ($k \le 4$) |
| Parity $\bigwedge_{i<k}(x_i \oplus y_i)$ | 2 / 4 / 6 / 8 / 10 | $2^4$..$2^{20}$ | 7 / 13 / 19 / 25 / 31 (width 2) | 10 / 46 / 190 / 766 / 3,070 | $2^2, 2^4, 2^6, 2^8, 1024$ | Exact ($k \le 4$) |
| Dense Cross-Cut Parity | 2 / 4 / 6 / 8 | $2^4$..$2^{16}$ | — | 10 / 46 / 190 / 766 | $2^2, 2^4, 2^6, 256$ | Exact ($k \le 4$) |

---

### 6. Programmable Inference: `Gen` GFI Contracts, Trace Types, and Automated Involutive MCMC

Basis: normative (Cusumano-Towner et al. PLDI 2019, Lew et al. POPL 2020, Cusumano-Towner et al. 2020) + source (`probcomp/Gen.jl` `v0.4.9` at `9953ceb296b56ad5cd225d811a9fdfc8470b17e5`)

#### 6.1 Generative Function Interface (GFI) Weight Contracts (`probcomp/Gen.jl`)

**Gen** (PLDI 2019) separates models from programmable inference engines (IS, SMC, MH, HMC, VI, involutive MCMC) via the **Generative Function Interface (GFI)**. Any custom generative function is valid iff its methods satisfy the exact Radon-Nikodym weight laws recorded in `src/gen_fn_interface.jl` (for args $x$, addressed choices $t$, unaddressed randomness $r$, density $p$, and internal proposal $q$):

| GFI Operation | Semantics | Exact Log-Weight Contract | `src/gen_fn_interface.jl` |
| --- | --- | --- | --- |
| `get_score` | Trace log-score | $\log \dfrac{p(r, t; x)}{q(r; x, t)}$ ($\log p(t; x)$ if no $r$) | `L53-62` |
| `simulate` | Prior draw $(r, t) \sim p(\cdot; x)$ | None | `L138-150` |
| `generate` | Constrained draw $t \sim q(\cdot; u, x)$, $r \sim q(\cdot; x, t)$ | $\log \dfrac{p(r, t; x)}{q(t; u, x)\,q(r; x, t)}$ | `L153-190` |
| `project` | Weight for $u = t|_A$ on selection $A$ | $\log \dfrac{p(r, t; x)}{q(t; u, x)\,q(r; x, t)}$ | `L193-207` |
| `propose` / `assess` | Forward sample / full-choice evaluation (errors if $p(t; x)=0$) | $\log \dfrac{p(r, t; x)}{q(r; x, t)}$ | `L210-243` |
| `update` | New args $x'$, constraints $u$; returns `discard` $v$ | $\log \dfrac{p(r', t'; x')}{q(r'; x', t')\,q(t'; x', t + u)} - \log \dfrac{p(r, t; x)}{q(r; x, t)}$ | `L246-290` |
| `regenerate` | Resample selection $A$ given $u = t|_{A^c}$, $u' = t'|_{A^c}$ | $\log \dfrac{p(r', t'; x')}{q(t'; u, x')\,q(r'; x', t')} - \log \dfrac{p(r, t; x)}{q(t; u', x)\,q(r; x, t)}$ | `L293-335` |

In `src/dynamic/update.jl:19-68, 122-160` and `src/dynamic/regenerate.jl:17-57, 104-142`, the dynamic DSL enforces address uniqueness (`visit!`), tracks incremental weight deltas, and subtracts deleted-branch scores (`update_delete_recurse`) or unaddressed noise (`regenerate_delete_recurse`). Meanwhile, `src/inference/hmc.jl:81-128` executes leapfrog steps calling `update` with zero static check that `selection` excludes discrete choices or branching control flow, and custom-proposal `metropolis_hastings` carries an unimplemented `# TODO add a round trip check` (`src/inference/mh.jl:42`).

#### 6.2 Trace Types for Sound Programmable Inference (Lew et al., POPL 2020)

Lew, Cusumano-Towner, Sherman, Carbin & Mansinghka (POPL 2020, Article 19) give programmable inference a static type system over **Quasi-Borel Spaces (`Qbs`)**:
- **Trace types $\sigma$:** Built from primitive choice distributions, labeled records (choice maps), and disjoint unions/coproducts (stochastic branching), each trace type $\sigma$ denotes both the measurable space of traces and its canonical reference measure $\mu_\sigma$ (products/coproducts of Lebesgue and counting measures).
- **Static soundness:** Typechecking IS, SMC, MH, VI, and trace translators checks structural subtyping/compatibility between model trace type $\sigma_p$ and proposal/guide trace type $\sigma_q$, statically guaranteeing **absolute continuity** ($\mu_p \ll \mu_q$ or $\mu_q \ll \mu_p$) and exact **Radon-Nikodym derivatives** for all importance weights and acceptance ratios, eliminating singular measure-zero mismatches by construction.

#### 6.3 Automated Involutive MCMC and Dynamic Checks (Cusumano-Towner et al., 2020; `Gen.jl`)

For transdimensional updates (e.g., split-merge RJMCMC on infinite Gaussian mixtures), Cusumano-Towner, Lew & Mansinghka (`arXiv:2007.09871`, Algorithm 1 & Theorem 3.1) prove stationarity for any involution $f : Z \to Z$ ($f \circ f = \mathrm{id}$) on $Z = \{(x, y) : p(x) q_x(y) > 0\}$ with $\mu \circ f^{-1} \ll \mu$ ($\mu = \mu_P \times \mu_Q$) under acceptance probability

$$\alpha = \min\!\left(1,\; \frac{p(x')\, q_{x'}(y')}{p(x)\, q_x(y)} \cdot \frac{d(\mu \circ f^{-1})}{d\mu}(x, y)\right).$$

In `probcomp/Gen.jl` (`src/inference/trace_translators.jl`), traces are finite dictionaries split into discrete keys $I$ and continuous keys $J$ (`arXiv:2007.09871` §3.2):
1. The `@transform` DSL (`L114-222`) annotates `@read`/`@write` as `:discrete` or `:continuous` and `@copy` for unmodified addresses (exploiting sparsity to shrink the Jacobian).
2. `jacobian_correction` (`L582-619`) runs `ForwardDiff.jacobian`, errors if the reduced Jacobian is non-square (`L608-610`), computes `LinearAlgebra.logabsdet(J)[1]` (`L613`), and logs an error if `isinf(correction)` (singular map, `L614-616`).
3. `SymmetricTraceTranslator` (`L910-938`) assembles `new_model_score - prev_model_score + backward_proposal_score - forward_proposal_score + log_abs_determinant`.
4. **Opt-in 3-stage dynamic check (`arXiv:2007.09871` Algorithm 4; `trace_translators.jl:621-638, 929-963`):** Passing `check=true` verifies observation invariance (`check_observations`), continuous dimension/support validity, and round-trip involutivity $f(f(x, y)) \approx (x, y)$ (`check_round_trip`). Because `check=false` is the default (`mh.jl:86`, `trace_translators.jl:911`), validation is opt-in and probabilistic rather than a static proof.

---

### 7. Comparative Architecture Matrix and Finite-Machine / Host-Effect Boundaries

Basis: normative (Mironov CCS 2012, Bagnall et al. PLDI 2023) + source (`hakaru`, `stanc3`, `pyro`, `pyppai`, `dice`, `Gen.jl`) + derived

#### 7.1 Comparative Matrix of Examined PPL Semantics and Compiler Guarantees

| System | Semantic Model | Discrete Latents | Measure-Zero Conditioning | Gradients & Jacobians | Varying Dimension | Soundness Guarantee | Primary Failure Mode |
| --- | --- | --- | --- | --- | --- | --- | --- |
| **QBS + s-Finite** (`Heunen 2017`; `Staton 2017`) | Cartesian closed `Qbs` + commutative s-finite kernels (`ωQbs` for recursion) | Full | Explicit disintegration or soft `score` | Orthogonal (`ADEV`/diffeologies) | Full | Mathematical foundation | Discarding non-affine `score`/diverging code breaks equivalence |
| **Hakaru** (`Shan & Ramsey 2017`) | Standard Borel symbolic measures | Full | **Exact symbolic disintegration** w.r.t. base measure | Automatic symbolic inverse Jacobians (`Prod`, trig, `RealPow`) | Disjoint sums | Sound when succeeding; `bot` on `Dirac` vs. Lebesgue | Fails (`bot`) on coupled multi-path nonlinearities or `Lam_`/`Integrate` |
| **Stan (`stanc3` v2.40.0)** | Fixed-dim smooth density on $\mathbb{R}^K$ | **Compile-time banned** in params | Soft `target +=` only | Auto for 18 `Transformation.t`; manual `jacobian +=` | Unsupported | Hard int-param error; opt-in `--warn-pedantic` | NUTS divergences on param `if`; silent bias on wrong manual Jacobians |
| **Pyro + `pyppai`** (`Lee et al. 2020`) | Dynamic Python traces + ELBO | Enumeration or REINFORCE | Soft `obs=` only | PyTorch autograd | Runtime dynamic | Runtime checks names/shapes; **`pyppai`** proves $\mathrm{supp}(q) \subseteq \mathrm{supp}(p)$ | Silent $\mathrm{KL}(q\|p)=+\infty$ masked by finite MC ELBO; singular `Delta` guides |
| **Dice** (`Holtzen et al. 2020`) | Dual discrete BDDs (`state`, `z`) | **Exact** ROBDD (`rsdd`/CUDD) + WMC | Discrete Boolean `observe` | N/A | Bounded unrolling (`Observe(False)`) | Theorem 4.6 exact compilation (finite programs) | **PSPACE-hard** $2^k$ BDD blowup on unfactored parity; silent depth-10 truncation |
| **Gen.jl + Trace Types** (`2019`/`2020`) | Dictionary traces over `Qbs` + GFI | Full mixed choice maps | `ChoiceMap` constraints | `ForwardDiff.jacobian` (`@transform`); AD for HMC | **Full** via involutive MCMC | Trace Types statically prove $q \ll p$; `Gen.jl` opt-in `check=true` | Default `check=false` masks non-involutions, dropped addresses, or discrete HMC |

#### 7.2 Finite-Machine Sampling Gap and Host-Effect Replay Obligations

1. **Idealized $\mathbb{R}$-samplers vs. IEEE-754 porosity:** Real-valued semantics ignore finite-precision mantissa spacing. **Mironov (CCS 2012, DOI `10.1145/2382196.2382264`)** showed that textbook floating-point Laplace noise left zero-probability "holes" enabling privacy breaches across `PINQ`, `Airavat`, `Fuzz`, and `GUPT`. For discrete distributions, **Zar** (Bagnall, Stewart & Banerjee, PLDI 2023, DOI `10.1145/3591220`) compiles looping/conditioned programs into formally verified exact discrete samplers from fair bits; verified IEEE-754 continuous samplers remain largely open.
2. **Host-FFI replay safety:** Inference engines re-execute models across mutated and rejected traces (`Gen.jl` `update`/`regenerate`/`hmc.jl`, `Pyro` `Trace_ELBO`). Host mutation, I/O, or non-splittable global PRNG state inside models breaks commutativity (`Staton 2017`) and reproducibility. At a verified language/FFI boundary (cf. `semantic-models-lenses-hyperproperties-and-putnam-tcb-boundary`), foreign probabilistic models require three explicit contracts: (i) **replay-safe effect isolation**, (ii) **reference-measure & support dominance**, and (iii) **regularity / GFI weight exactness** matched to the inference engine.

## Boundaries

- **known not to apply:**
  - `stan-dev/stanc3`'s integer-parameter ban and automatic `Transformation.t` Jacobians do not guarantee smoothness or Jacobian correctness for arbitrary Stan models: parameter-dependent `if` branches still compile, `list_possible_nonlinear` misses transforms bound to local variables (`Var _`), and manual `target +=`/`jacobian +=` terms are never algebraically checked.
  - `pyro-ppl/pyro`'s `check_model_guide_match` does not verify distributional support containment or reference-measure equivalence; passing runtime validation does not rule out $\mathrm{KL}(q \| p) = +\infty$.
  - `probcomp/Gen.jl`'s `check=true` involution test is opt-in (`check=false` by default) and dynamic/probabilistic rather than a static proof of universal involutivity.
  - `SHoltzen/dice`'s exact compilation theorem (Theorem 4.6) holds for finite/non-recursive programs; recursive programs truncated via `Observe(False)` at depth 10 (`Passes.expand_recursion`) lose exactness whenever deeper paths carry positive mass.
- **unsupported:**
  - Discrete latent parameters in `stan-dev/stanc3` (`parameters` and `transformed parameters`).
  - Continuous distributions and `Sample(e)` (`Compiler.ml:161`) in `SHoltzen/dice`.
  - Disintegrating lambdas (`Lam_`/`App_`), `Integrate`/`Summate`, and coupled multi-path nonlinearities in `hakaru-dev/hakaru` (`Disintegrate.hs`).
  - Static POPL 2020 Trace Type checking in `probcomp/Gen.jl` `v0.4.9`.
- **not examined:**
  - Mechanized theorem-prover libraries (Lean 4, Rocq, Isabelle) for `Qbs`, `ωQbs`, or s-finite kernels.
  - End-to-end runtime benchmarks of compiled `stanc3`, `Gen.jl`, `Hakaru`, or `Dice` `rsdd` binaries on large empirical workloads.
  - Supermartingale probabilistic termination provers, exact hybrid discrete-continuous languages (`SPPL`), simulation-based calibration (`SBC`), and `pyro-ppl/numpyro` internals.
- **unknown:**
  - Whether any production PPL compiler unifies static measure-zero disintegration, static model-guide support dominance, static HMC smoothness checking, and verified finite-precision continuous sampling in a single end-to-end checked toolchain.
  - Tight complexity completeness (between **PSPACE-hard** and **EXPTIME**) for exact inference in full Dice with procedures (open in Holtzen et al. OOPSLA 2020 §6.1).

## Evidence

All primary sources and probes were verified on `2026-11-19`.

### Primary Literature

1. Aumann (1961), *Illinois J. Math.* 5(4):614–630, DOI `10.1215/ijm/1255631584`.
2. Heunen, Kammar, Staton & Yang (2017), LICS 2017, DOI `10.1109/LICS.2017.8005137`, `arXiv:1701.02547`.
3. Staton (2017), ESOP 2017, LNCS 10201:855–879, DOI `10.1007/978-3-662-54434-1_32`.
4. Shan & Ramsey (2017), POPL 2017, DOI `10.1145/3009837.3009852`.
5. Jacobs (2021), PACMPL 5(POPL), DOI `10.1145/3434339`, `arXiv:2101.03391`.
6. Carpenter et al. (2017), *JSS* 76(1), DOI `10.18637/jss.v076.i01`; Hoffman & Gelman (2014), *JMLR* 15:1593–1623.
7. Lee, Yu, Rival & Yang (2020), PACMPL 4(POPL), DOI `10.1145/3371084`, `arXiv:1907.08827`.
8. Cusumano-Towner, Saad, Lew & Mansinghka (2019), PLDI 2019, DOI `10.1145/3314221.3314642`.
9. Lew, Cusumano-Towner, Sherman, Carbin & Mansinghka (2020), PACMPL 4(POPL) Art. 19, DOI `10.1145/3371087`.
10. Cusumano-Towner, Lew & Mansinghka (2020), `arXiv:2007.09871` (Algorithm 1, Theorem 3.1, §3.2, §6 Algorithm 4).
11. Holtzen, Van den Broeck & Millstein (2020), PACMPL 4(OOPSLA) Art. 140, DOI `10.1145/3428208`, `arXiv:2005.09089` (Theorems 4.6 & 6.1, Proposition 6.2, §6.3).
12. Cross-cutting verified DOIs: Vákár, Kammar & Staton (POPL 2019, `10.1145/3290349`); Lew et al. (`ADEV`, POPL 2023, `10.1145/3571198`); Mironov (CCS 2012, `10.1145/2382196.2382264`); Bagnall, Stewart & Banerjee (`Zar`, PLDI 2023, `10.1145/3591220`).

### Pinned Repository Source Evidence

- **`hakaru-dev/hakaru` @ `e8bebac6d344e81a429c25f2b4c29b76172ea47f`:** `haskell/Language/Hakaru/Disintegrate.hs` (`L30-42`, `L151-227`, `L499-600`, `L870-895`, `L945-1060`, `L1236-1296`).
- **`stan-dev/stanc3` @ `456130a900c56ddb0505c4540460977106bd9938` (`v2.40.0`):** `src/frontend/Typechecker.ml` (`L62-65, 457-469, 1241-1249, 1894-1899`), `Semantic_error.ml` (`L816, 825, 917-920, 986-988, 1279-1280, 1305-1306`), `src/middle/Transformation.ml` (`L9-34`), `src/stan_math_backend/Lower_{expr,program,stmt}.ml` (`Lower_expr.ml:420-435`, `Lower_program.ml:226-244, 276-278`, `Lower_stmt.ml:290-294`), `src/analysis_and_optimization/Pedantic_analysis.ml` (`L74-135, 158-269, 367-442`).
- **`wonyeol/static-analysis-for-support-match` @ `850fb58ec5ce2f5e82262c2a9bfc067b799297c1`:** `pyppai/main.ml:89-103`, `adom_distty.ml:31-36, 187-212`, `adom_fib.ml:1621-1661`, `ir_util.ml:64-99`, `README.txt:158-206`, `tests/pyro_examples/{br_original_modelguide,br_model1,br_guide1,lda_original_modelguide}.py`.
- **`pyro-ppl/pyro` @ `a31bc1784707268cd79df77ead4c7a47062f0193`:** `pyro/util.py:314-425` (`check_model_guide_match`), `pyro/infer/trace_elbo.py:23-159`.
- **`SHoltzen/dice` @ `1d8a277636a428eb46164ba4639fab12a310f30c`:** `lib/Compiler.ml:10-13, 93-108, 124-135, 161, 180-254`, `lib/Wmc.ml:5, 18-41`, `lib/Bdd.ml:8-48`, `lib/Passes.ml:9, 67-106, 198`.
- **`probcomp/Gen.jl` @ `9953ceb296b56ad5cd225d811a9fdfc8470b17e5` (`v0.4.9`):** `src/gen_fn_interface.jl:53-350`, `src/dynamic/{update,regenerate}.jl`, `src/inference/{mh,hmc,trace_translators}.jl` (`mh.jl:14-116`, `hmc.jl:81-128`, `trace_translators.jl:114-222, 582-638, 885-965`).

### Runnable Execution Evidence

- **`support/verify_ppl_conditioning_and_wmc.py`** (Python 3.10+, stdlib-only, ~0.5s):
  - **Probe 1 (`dice_wmc`):** Exact `Fraction` equality between ROBDD WMC and exhaustive enumeration (`ObsProg` = `5/6`, branch-guarded `Ite` = `1/4`, Burglary-Alarm BN = `592242590/2084100239`), linear $5k+2$ Markov-chain scaling (82 nodes, width 2 at $k=16$), and exact $2^k$ cut-width blowup on separated parity ($k=10$: 31 nodes paired vs. 3,070 nodes / width 1,024 separated) and dense parity ($k=8$: 766 nodes / width 256).
  - **Probe 2 (`borel_kolmogorov`):** Analytical $\epsilon \to 0$ convergence and $550 \times 550$ midpoint quadrature at $\epsilon = 0.01$ separating $|X - Y| \le \epsilon$ ($\mathbb{E}[X]=0.500000$, $P(X \le 0.5)=0.500000$) from $|X/Y - 1| \le \epsilon$ ($\mathbb{E}[X]=0.662257 \to 2/3$, $P(X \le 0.5)=0.255354 \to 0.25$), plus spherical meridian (`0.500000`) vs. equator (`0.636620`).
  - **Probe 3 (`svi_support`):** Static rejection of `pyro_bayesian_regression_original` (`SUPPORT_VIOLATION`), `pyro_lda_dirac_guide` (`MEASURE_SINGULARITY`), and `missing_latent_site`; acceptance of `pyro_bayesian_regression_fixed`; silent MC ELBO masking at `loc=1.0` (`0/100,000` escapes, `-3.881020`, $P_{\text{escape}}=2.75 \times 10^{-89}$) vs. `-inf` crash (`106/100,000` escapes) at `loc=0.15`.

## Revalidation

1. **Rerun the standalone semantic probe (<1s):**
   ```console
   python3 -B reports/probabilistic-programming-measure-semantics-and-inference-compilers/support/verify_ppl_conditioning_and_wmc.py
   python3 -B reports/probabilistic-programming-measure-semantics-and-inference-compilers/support/verify_ppl_conditioning_and_wmc.py --json
   ```
   A pass confirms the mathematical ROBDD/WMC, Borel-Kolmogorov, and SVI masking properties; it does not inspect newer upstream compiler revisions.
2. **Diff narrow upstream decision sites:**
   - `stan-dev/stanc3`: `Typechecker.ml` (`verify_transformed_param_ty`, `verify_jacobian_pe_usage`), `Lower_stmt.ml` (`JacobianPE`), `Pedantic_analysis.ml` (`list_possible_nonlinear`, `list_param_dependant_cf`).
   - `pyro-ppl/pyro`: `pyro/util.py` (`check_model_guide_match`) for distributional support-containment checks.
   - `SHoltzen/dice`: `lib/Compiler.ml` (`Ite`, `Sample`, `FuncCall`), `lib/Bdd.ml`, `lib/Wmc.ml`, `lib/Passes.ml` (`expand_recursion`).
   - `probcomp/Gen.jl`: `src/gen_fn_interface.jl`, `src/inference/mh.jl` (`check` default and round-trip TODO), `src/inference/trace_translators.jl` (`jacobian_correction`, `SymmetricTraceTranslator`).
   - `hakaru-dev/hakaru`: `haskell/Language/Hakaru/Disintegrate.hs` (`constrainValue`, `constrainNaryOp`, `constrainPrimOp`).
3. **Full re-investigation triggers:** Re-evaluate §7.1 and `## Boundaries` if a production PPL ships static Trace Types, native Discontinuous HMC, or verified IEEE-754 continuous sampling end-to-end.
