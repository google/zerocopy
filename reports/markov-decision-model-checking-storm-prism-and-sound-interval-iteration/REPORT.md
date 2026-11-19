# Quantitative Model Checking of Markov Decision Processes, Unsound Value Iteration, and Exact Bellman Certificates in Storm and PRISM

## Summary

Quantitative verification of Discrete-Time Markov Chains (`DTMC`), Continuous-Time Markov Chains (`CTMC`), and Markov Decision Processes (`MDP`) in **Storm** (`v2.0.0.3`) and **PRISM** (`v4.12.1-dev`) reduces `PCTL*`, `CSL`, and expected-reward queries to extremal fixed points of monotone Bellman operators (plus Fox–Glynn uniformized Poisson series for continuous-time bounds). Four foundational soundness and architectural invariants govern engineering reliance on these tools:

1. **Catastrophic Premature-Convergence Unsoundness of Standard IEEE 754 Value Iteration (`VI`):** Halting Bellman iteration from below when consecutive iterates satisfy $\|x^{(k)} - x^{(k-1)}\|_\infty \le \varepsilon$ (or relative difference $\le \varepsilon$) provides **zero bound on true error** $\|x^* - x^{(k)}\|_\infty$. On cyclic or slowly mixing chains with exit probability $\delta \ll \varepsilon$ (e.g., $\delta = 10^{-7}, \varepsilon = 10^{-6}$), standard `VI` halts after **1 iteration** reporting `1e-7` when the true reachability probability is `0.500000025`—an absolute error of `0.5` ($500{,}000\times$ larger than $\varepsilon$). Default floating-point `VI` must never be treated as a sound safety or dependability verifier without explicit `--sound` or `--exact` modes.
2. **Mandatory Maximal End Component (`MEC`) Quotienting for Sound Upper Brackets:** For maximizing reachability ($P_{\max}$) and minimizing expected reachability rewards ($R_{\min}$), zero-reward Maximal End Components inside the "maybe" state space $S_?$ induce **non-unique Bellman fixed points**: $l^* = \mathrm{lfp}(T_{\max})$ is the true reachability vector, whereas $u^* = \mathrm{gfp}(T_{\max}) = \mathbf{1}$ traps upper iterates at $1.0$ forever. Consequently, Interval Iteration (`II`), Sound Value Iteration (`SVI`), and Optimistic Value Iteration (`OVI`) **deadlock or fail to contract** unless zero-reward `MEC`s are first collapsed into quotient states with internal cycle choices removed (`EndComponentEliminator` in Storm; `MDPModelChecker.maxQuotient` in PRISM). Conversely, $P_{\min}$ and $R_{\max}$ (after qualitative `Prob0`/`Prob1` filtering) have no maybe-state `MEC`s and unique fixed points without quotienting.
3. **Convergence-Guarantee Trade-Offs Across `II`, `SVI`, and `OVI`:** Interval Iteration (`II`) maintains two monotone vectors $l^{(k)} \le x^* \le u^{(k)}$ (requiring an explicit `Baier` / `DSMPI` / `Variant-2` upper-bound precomputation for expected rewards and IEEE 754 monotonicity clamping). Sound Value Iteration (`SVI`) iterates $(x^{(k)}, y^{(k)})$ tracking target-absorption mass $x^{(k)}$ and maybe-retention mass $y^{(k)}$ to derive tight analytic brackets without apriori upper bounds. Optimistic Value Iteration (`OVI`—Storm's default under `--sound`) runs fast single-vector Gauss-Seidel `VI` from below, heuristically shifts $u = v + \varepsilon$, and certifies $T(u) \le u$ via Park's induction principle, typically halving total Bellman sweeps relative to `II` while preserving sound post-convergence bounds.
4. **Exact Rational Synthesis and Standalone Bellman / Farkas Certificates:** Exact verification (`--exact` in Storm; `-exact` in PRISM) bypasses IEEE 754 drift entirely via GMP/CLN `mpq_class` Policy Iteration, LP, or Kwek–Mehlhorn continued-fraction **Rational Search** (sharpening `double` `VI` iterates into candidate rationals and checking exact $T(x) = x$). Crucially, any quantitative dependability claim ($P_{\max}(s_0 \models \Diamond T) \le \lambda$ or $P_{\min} \ge \lambda$) can be **decoupled completely from numerical model-checker TCBs** by exporting an exact rational inductive vector $u \in \mathbb{Q}^{|S|}$ ($T_{\max}(u) \le u \land u(s_0) \le \lambda$) or dual Farkas occupancy-measure witness $\mu \in \mathbb{Q}_{\ge 0}^{M}$, checkable in $O(\text{nnz})$ exact arithmetic.

## Applicability

The findings in this report apply to the following pinned implementations, algorithms, and logical formalisms:

- **`moves-rwth/storm` at commit `926b19c62afe6eac917e87ecf1058f5ee116fbc2` (`VERSION 2.0.0.3`):** C++20 probabilistic model checker spanning four engines (`sparse` explicit CSR row-group matrices, `dd` symbolic MTBDDs via Sylvan/CUDD, `hybrid`, and `abstraction-refinement`), template-parameterized across `double`, exact `storm::RationalNumber` (GMP `mpq_class` or CLN `cl_RA` via `carl-storm` tag `14.37`), parametric `storm::RationalFunction` (`carl::RationalFunction<Polynomial, true>`), and uncertain intervals (`storm::Interval`, `storm::RationalInterval`).
- **`prismmodelchecker/prism` at commit `5a534b02fd1f17c6b30affc6231e280b40ae0860` (`versionString = "4.12.1"`, `versionSuffixString = "dev"`):** Java + C/C++ JNI probabilistic model checker providing `mtbdd`, `sparse`, `hybrid` (CUDD-backed symbolic/explicit engines), and `explicit` pure-Java engines (`DTMCModelChecker`, `CTMCModelChecker`, `MDPModelChecker`, `IDTMCModelChecker`, `IMDPModelChecker`), interval iteration (`-intervaliter`), and exact `BigRational` verification (`-exact`).
- **Foundational Algorithmic Specifications:** Hensel et al. (*STTT* 2022, `10.1007/s10009-021-00633-z`), Kwiatkowska, Norman, & Parker (*CAV* 2011, `10.1007/978-3-642-22110-1_47`), Haddad & Monmege (*TCS* 2018, `10.1016/j.tcs.2016.12.003`), Baier et al. (*CAV* 2017, `10.1007/978-3-319-63387-9_8`), Quatmann & Katoen (*CAV* 2018, `10.1007/978-3-319-96145-3_37`), Hartmanns & Kaminski (*CAV* 2020, `10.1007/978-3-030-53291-8_26`), Bauer et al. (*FMSD* 2020, `10.1007/s10703-020-00348-y`), and Funke, Jantsch, & Baier (*TACAS* 2020, `10.1007/978-3-030-45190-5_18`).

**Scope Conditions:** Quantitative unbounded and step/reward-bounded reachability (`PCTL` $\mathbb{P}_{\sim \lambda}[\Phi \mathbin{\mathcal{U}} \Psi]$, expected cumulative reachability rewards $\mathbb{R}_{\sim \kappa}[\Diamond \Psi]$), LTL/PCTL* $\omega$-regular properties (via Rabin/deterministic $\omega$-automata product + accepting `MEC`s), and `CSL` continuous-time properties on finite-state `DTMC`, `CTMC`, `MDP`, and interval `IMDP` models.

## Findings

### 1. Model Reductions, Qualitative Precomputation, and Engine Architecture (`Storm` vs. `PRISM`)

`Basis: documentation + source`

Let $\mathcal{M} = (S, s_0, \mathit{Act}, \mathbf{P}, \mathit{rew})$ be a finite `MDP` where $\mathit{Act}(s)$ is the finite non-empty set of enabled choices at state $s \in S$ and $\mathbf{P}(s, \alpha, s') \in [0, 1]$ satisfies $\sum_{s' \in S} \mathbf{P}(s, \alpha, s') = 1$ (a `DTMC` is the degenerate case $|\mathit{Act}(s)| = 1$). Both Storm and PRISM execute a three-phase reduction before invoking any numerical solver (`SparseMdpPrctlHelper.cpp:533-568`, `MDPModelChecker.java:508-560`):

1. **Graph-Based Qualitative Partitioning ($S = S_0 \sqcup S_1 \sqcup S_?$):**
   - For constrained reachability $\Phi \mathbin{\mathcal{U}} \Psi$ under optimization direction $\mathit{opt} \in \{\min, \max\}$, backward graph search (`performProb01Min` / `performProb01Max` in Storm; `prob0` + nested fixed-point `prob1` in `MDPModelChecker.java:680-752, 980-1074`) computes in exact boolean arithmetic:
     - $S_0 = \{s \in S \mid \Pr^{\mathit{opt}}_s(\Phi \mathbin{\mathcal{U}} \Psi) = 0\}$, pinned to exact `0`;
     - $S_1 = \{s \in S \mid \Pr^{\mathit{opt}}_s(\Phi \mathbin{\mathcal{U}} \Psi) = 1\}$, pinned to exact `1`;
     - $S_? = S \setminus (S_0 \cup S_1)$ ("maybe" states), over which the quantitative Bellman operator $T_{\mathit{opt}} : [0, 1]^{S_?} \to [0, 1]^{S_?}$ is defined:
       $$T_{\mathit{opt}}(x)(s) = \underset{\alpha \in \mathit{Act}(s)}{\mathit{opt}} \left( b(s, \alpha) + \sum_{s' \in S_?} \mathbf{P}(s, \alpha, s') \cdot x(s') \right), \qquad b(s, \alpha) = \sum_{t \in S_1} \mathbf{P}(s, \alpha, t)$$
   - For expected reachability rewards $\mathbb{R}_{\mathit{opt}}[\Diamond \Psi]$, qualitative precomputation first identifies $S_\infty$ where expected reward diverges to $\infty$: for $\mathbb{R}_{\max}[\Diamond \Psi]$, $s \in S_\infty$ whenever *some* scheduler avoids $\Psi$ with positive probability ($\Pr^{\min}_s(\Diamond \Psi) < 1$); for $\mathbb{R}_{\min}[\Diamond \Psi]$, $s \in S_\infty$ iff *every* scheduler avoids $\Psi$ with positive probability ($\Pr^{\max}_s(\Diamond \Psi) < 1$; see `MDPModelChecker.java:755-779`).
2. **CTMC Unbounded vs. Time-Bounded Dichotomy (`SparseCtmcCslHelper.cpp:57-264`, `CTMCModelChecker.java:180-222, 324-450`):**
   - For **unbounded** `CSL` until $\Phi \mathbin{\mathcal{U}} \Psi$, residence times cancel out: both Storm (`computeProbabilityMatrix(rateMatrix, exitRateVector)`) and PRISM (`ctmc.getImplicitEmbeddedDTMC()`) reduce the rate matrix $\mathbf{R}$ with exit rates $E(s) = \sum_{s'} \mathbf{R}(s, s')$ directly to the embedded `DTMC` $\mathbf{P}_{\text{emb}}(s, s') = \mathbf{R}(s, s') / E(s)$ (for $E(s) > 0$), which admits **exact rational** solving.
   - For **time-bounded** `CSL` until $\Phi \mathbin{\mathcal{U}}^{[t_1, t_2]} \Psi$ ($t_2 < \infty$ or $t_1 > 0$), transient probabilities follow the matrix exponential $\Pi(t) = e^{\mathbf{Q} t} = \sum_{k=0}^\infty \psi_{q t}(k) \mathbf{P}_{\text{unif}}^k$, where $\mathbf{P}_{\text{unif}} = \mathbf{I} + \frac{1}{q}\mathbf{Q}$, $q \ge \max_s E(s)$ (`uniformizationRate = 1.02 * max_exit_rate` in Storm `SparseCtmcCslHelper.cpp:115, 151`), and $\psi_{qt}(k) = e^{-qt}\frac{(qt)^k}{k!}$ are Poisson weights truncated to $[L, R]$ via the **Fox–Glynn** algorithm with truncation budget $\varepsilon_{\text{FG}} = \varepsilon / 8$ (`SparseCtmcCslHelper.cpp:78`, `CTMCModelChecker.java:449-450`). Storm explicitly throws `InvalidOperationException("Exact computations not possible for bounded until probabilities")` when `--exact` is requested on time-bounded `CSL` (`SparseCtmcCslHelper.cpp:61-62`) because $e^{-qt}$ is transcendental for rational $qt \neq 0$; under `--sound` with relative precision, `checkAndUpdateTransientProbabilityEpsilon` (`SparseCtmcCslHelper.cpp:22-53`) iteratively shrinks $\varepsilon_{\text{FG}}$ whenever $\varepsilon_{\text{FG}} / x_s > \varepsilon_{\text{rel}}$.
3. **Engine Representation Matrix (`Storm` vs. `PRISM`):**

| Architectural Dimension | `moves-rwth/storm` (`v2.0.0.3`) | `prismmodelchecker/prism` (`v4.12.1-dev`) |
| :--- | :--- | :--- |
| Sparse `MDP` matrix layout | Contiguous C++ CSR `SparseMatrix<ValueType>` with `rowGroupIndices` mapping state $s \mapsto [\text{row}_s, \text{row}_{s+1})$ | `explicit.MDPSparse` (Java arrays) & JNI `sparse/NDSparseMatrix` (`C++` `PS_*` kernels) |
| Symbolic `DD` backend | Dual-backend adapter over **Sylvan** (multi-core lock-free MTBDDs, including GMP rational leaves!) and **CUDD** | **CUDD** (`mtbdd/` & `hybrid/` C++ JNI kernels, `double` terminal leaves) |
| Exact / Parametric types | Native C++ templates over `mpq_class` / `cl_RA` (`--exact`) and `carl::RationalFunction` (`storm-pars`) | Java `explicit` engine parameterized over `BigRational` (`-exact`) and parametric `Function` |
| Default `--sound` `MDP` solver | `OptimisticValueIteration` (`IterativeMinMaxLinearEquationSolver.cpp:72`) | `-intervaliter` (`doIntervalIterationReachProbs` / `PS_NondetUntilInterval.cc`) |
| Default `--exact` `MDP` solver | `PolicyIteration` (`IterativeMinMaxLinearEquationSolver.cpp:63`), plus `RationalSearch` and `ViToPi` | `PolicyIteration` / exact linear solver over `MDP<BigRational>` |

### 2. Why Standard Floating-Point Value Iteration Is Catastrophically Unsound

`Basis: source + derived + execution`

In both Storm (`ValueIterationHelper.cpp:35-41`) and PRISM (`IterationMethodPower` / `IterationMethodGS`), standard Value Iteration initializes $x^{(0)} = \mathbf{0}$ on $S_?$, computes $x^{(k)} = T_{\mathit{opt}}(x^{(k-1)})$ (Jacobi or Gauss-Seidel), and halts as soon as:
$$\text{Absolute:} \quad \max_{s \in S_?} |x^{(k)}_s - x^{(k-1)}_s| \le \varepsilon, \qquad \text{or Relative:} \quad \max_{s \in S_?} \frac{|x^{(k)}_s - x^{(k-1)}_s|}{|x^{(k)}_s|} \le \varepsilon$$
(default $\varepsilon = 10^{-6}$).

**Mathematical Mechanism of Failure:** By Banach's theorem on a sub-stochastic matrix $\mathbf{P}_?$ with spectral radius $\rho(\mathbf{P}_?) = 1 - \gamma < 1$, one-step progress bounds true error only up to the amplification factor $(1 - \rho)^{-1} = 1/\gamma$:
$$\|x^* - x^{(k)}\|_\infty \le \frac{\rho}{1 - \rho} \|x^{(k)} - x^{(k-1)}\|_\infty$$
Whenever a Markov chain or `MDP` contains a metastable cycle or retry loop with small exit probability $\delta \in (0, 1)$, $1 - \rho = \Theta(\delta)$ can be arbitrarily small! Consider the 2-maybe-state chain $s_0 \xrightarrow{1-\delta} s_1, s_0 \xrightarrow{\delta} s_{\text{yes}}, s_1 \xrightarrow{1-\delta} s_0, s_1 \xrightarrow{\delta} s_{\text{no}}$. Its exact reachability probability is $x^*_0 = \frac{\delta}{1 - (1-\delta)^2} = \frac{1}{2 - \delta} > \frac{1}{2}$ for every $\delta \in (0, 1)$. Yet starting from $x^{(0)} = (0, 0)$, the first iterate is $x^{(1)} = (\delta, 0)$, so $\|x^{(1)} - x^{(0)}\|_\infty = \delta$. Whenever $\delta \le \varepsilon = 10^{-6}$, **absolute `VI` halts at iteration $k = 1$** reporting $x^{(1)}_0 = \delta \le 10^{-6}$ when $x^*_0 > 0.5$! Even under *relative* stopping ($|x^{(k)}_s - x^{(k-1)}_s| \le \varepsilon |x^{(k)}_s|$), a chain where $s_0$ first traverses a benign $\frac{1}{2}$-probability edge ($x^{(1)}_0 = 0.5$) before entering a $(1-\delta)$-mixing component stalls with step increments $\approx 0.5 \delta \le \varepsilon \cdot 0.5$ on iteration 2 while missing half the true probability mass!

**Empirical Comparison Across $\delta \in \{10^{-3}, 10^{-4}, 10^{-7}\}$ at $\varepsilon = 10^{-6}$ (`Basis: execution`):**

| Exit Rate $\delta$ | Exact $x^*_0 = \frac{1}{2-\delta}$ | Standard `VI` Iters | Standard `VI` Output | Standard `VI` True Error | `II` Iters | `SVI` Iters | `OVI` Iters (Refinements) | Max Error (`II` / `SVI` / `OVI`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| $10^{-3}$ | `0.500250125` | `6,906` | `0.499750725` | **`4.99e-4`** ($499\times \varepsilon$) | `13,116` | `5,520` | `6,250` (`9`) | $\le 1.00 \times 10^{-6}$ (all sound) |
| $10^{-4}$ | `0.500025001` | `46,051` | `0.495026052` | **`5.00e-3`** ($5{,}000\times \varepsilon$) | `131,218` | `32,188` | `64,647` (`13`) | $\le 1.00 \times 10^{-6}$ (all sound) |
| $10^{-7}$ | `0.500000025` | **`1`** | **`0.000000100`** | **`0.4999999`** ($5\times 10^5 \varepsilon$) | `131,223,628` | `2` (sym) / $\Theta(\delta^{-1})$ | $\Theta(\delta^{-1})$ | $\le 1.00 \times 10^{-6}$ (all sound) |

### 3. Maximal End Component (`MEC`) Decomposition and Quotienting Invariants

`Basis: source + derived + execution`

An **End Component (`EC`)** of an `MDP` is a pair $(T, A)$ with $\emptyset \neq T \subseteq S$ and $\emptyset \neq A(s) \subseteq \mathit{Act}(s)$ for all $s \in T$ such that: (i) for all $s \in T, \alpha \in A(s)$, $\mathrm{Post}(s, \alpha) \subseteq T$ (probabilistic closure), and (ii) the directed graph $(T, \{(s, s') \mid \exists \alpha \in A(s).\ \mathbf{P}(s, \alpha, s') > 0\})$ is strongly connected. A **Maximal End Component (`MEC`)** is an `EC` maximal under componentwise inclusion (every state belongs to at most one `MEC`).

#### Why Unquotiented `MEC`s Break Upper-Bound Solvers

By Bellman characterization, true reachability probabilities $p^{\max}_s = \Pr^{\max}_s(\Phi \mathbin{\mathcal{U}} \Psi)$ and $p^{\min}_s = \Pr^{\min}_s(\Phi \mathbin{\mathcal{U}} \Psi)$ are always the **least fixed points** ($\mathrm{lfp}$) of $T_{\max}$ and $T_{\min}$ on $[0, 1]^{S_?}$. Sound bracketing from *above* converges instead to the **greatest fixed point** ($\mathrm{gfp}$):
- **Minimizing Reachability ($P_{\min}$):** Any `EC` $(T, A)$ inside $S_?$ would allow the minimizing scheduler to stay in $T \subseteq S \setminus \Psi$ forever with probability $1$, forcing $\Pr^{\min}_s = 0$, which means $T \subseteq S_0$ was **already removed** by qualitative `Prob0E`! Hence $S_?$ contains **zero** `EC`s for $P_{\min}$ (`SparseMdpPrctlHelper.cpp:328`), and $\mathrm{lfp}(T_{\min}) = \mathrm{gfp}(T_{\min})$ is unconditionally unique.
- **Maximizing Reachability ($P_{\max}$):** Suppose $(T, A)$ is a `MEC` inside $S_?$, e.g., $T = \{s_1, s_2\}$ where $s_1$ has cycle choice $\alpha$ ($\mathbf{P}(s_1, \alpha, s_2) = 1$) and exit choice $\beta$ ($\mathbf{P}(s_1, \beta, s_{\text{yes}}) = 1/3, \mathbf{P}(s_1, \beta, s_{\text{no}}) = 2/3$), while $s_2$ has cycle choice $\gamma$ ($\mathbf{P}(s_2, \gamma, s_1) = 1$). Neither $s_1$ nor $s_2$ is in $S_0$ or $S_1$ ($\Pr^{\max} = 1/3$). Evaluating $T_{\max}$ at $u = (1, 1)$ gives:
  $$T_{\max}(1, 1)(s_1) = \max(u_{s_2}, 1/3) = \max(1, 1/3) = 1, \qquad T_{\max}(1, 1)(s_2) = u_{s_1} = 1$$
  Thus $u^* = (1, 1) = \mathrm{gfp}(T_{\max}) \neq (1/3, 1/3) = \mathrm{lfp}(T_{\max})$! Execution confirms (`Probe 2B`) that unquotiented `II` stalls forever with $l^{(k)} = [1/3, 1/3], u^{(k)} = [1.0, 1.0]$ (`width = 2/3`), while `SVI` keeps $y_{s_1} = y_{s_2} = 1.0$ (`allYLessOne == false`, trapped in `SVIStage::Initial`).
- **Expected Reachability Rewards ($R_{\min}$ vs. $R_{\max}$):** Dually, for $R_{\max}$, any `EC` in $S_?$ would let the maximizer avoid $\Psi$ forever ($\Pr^{\min} < 1 \implies S_\infty$), so $S_?$ is `EC`-free (`SparseMdpPrctlHelper.cpp:329`). For $R_{\min}$, **zero-reward `EC`s** (where every internal action has reward $0$) create non-unique fixed points because staying inside the zero-reward cycle preserves any optimistic/pessimistic value; positive-reward `EC`s strictly increase under $T_{\min}$ and therefore preserve fixed-point uniqueness (`SparseMdpPrctlHelper.cpp:332-354`).

#### `MEC` Decomposition and Quotienting Implementations

- **Storm (`MaximalEndComponentDecomposition.cpp:149-243` & `EndComponentEliminator.h:42-96`):** Iteratively runs Tarjan SCC decomposition (`performSccDecomposition` with `dropNaiveSccs()`), prunes choices `choice` with any positive transition leaving their SCC (`ecChoices.set(choice, false)`), emits stable SCCs immediately as `MaximalEndComponent` blocks, and filters remaining candidates via `performProbGreater0A` before repeating. `EndComponentEliminator::transform` replaces each `MEC` $T_i$ with a single representative row group $s_{T_i}$ containing the union of all **exit choices** $\bigcup_{s \in T_i} (\mathit{Act}(s) \setminus A_i(s))$, merging parallel transitions into identical quotient columns (`sortedEntries`, `EndComponentEliminator.h:187-200`) and optionally adding a zero-outgoing sink row (`addSinkRowStates`) when needed.
- **PRISM (`ECComputerDefault.java:135-247` & `MDPModelChecker.java:561-600`):** Implements de Alfaro's algorithm via a memory-bounded streaming Tarjan consumer (`findMECsStreaming`), recursing into one SCC at a time so peak memory stays $O(\text{depth} \times |S|)$ rather than $O(\#\text{MECs} \times |S|)$. When `!min && doPmaxQuotient` holds (enabled automatically under `-intervaliter`), `maxQuotient(mdp, yes, no)` builds an `MDPSparse` quotient and maps values back via `maxQuotient.mapStateToRestrictedModel(i)`.

### 4. Sound Iterative Solvers: `Interval Iteration`, `SVI`, and `OVI`

`Basis: source + derived + execution`

Once $T_{\mathit{opt}}$ has a unique fixed point $x^*$ on $S_?$ (via `MEC` quotienting where required), Storm and PRISM provide three sound numerical fixed-point schemes:

| Property / Requirement | Interval Iteration (`II`) | Sound Value Iteration (`SVI`) | Optimistic Value Iteration (`OVI`) |
| :--- | :--- | :--- | :--- |
| Primary source | Storm `IntervalterationHelper.cpp:21-256`; PRISM `IntervalIteration.h:33-141`, `MDPModelChecker.java:1199-1291` | Storm `SoundValueIterationHelper.cpp:29-318` | Storm `OptimisticValueIterationHelper.cpp:23-318` |
| Unique fixed point (`MEC`-free / quotiented)? | **Required** | **Required** ($y_s < 1$ eventually) | **Required** |
| Apriori finite upper bound $u^{(0)} \ge x^*$? | **Required** ($1.0$ for probs; `Baier` / `DSMPI` / `Variant-2` precomputation for expected rewards!) | **Not required** (analytic $x_s + b \cdot y_s$ derived dynamically!) | **Not required** (synthesizes $u = v \oplus \varepsilon$ from below!) |
| Per-iteration vector work | **2$\times$** Bellman sweeps ($l$ and $u$ every step) | **2$\times$** coupled affine sweeps ($x$ and $y$ plus decision scalar $d$) | **1$\times$** Gauss-Seidel sweep during approximation; **2$\times$** only during short verification bursts |
| Early-abort bound soundness | Both $l^{(k)}$ and $u^{(k)}$ are sound at **every** step (`IntervalterationHelper.cpp:241-246`) | Both lower & upper bounds valid once `SVIStage::y_less_1` is reached | `vu.first` ($v$) is always a sound lower bound; `vu.second` ($u$) is sound **only** upon `Converged` (`OptimisticValueIterationHelper.cpp:285-291`) |

#### Subtle IEEE 754 Floating-Point Hazards Inside Sound Solvers

1. **Non-Monotonicity Under IEEE 754 Rounding (`II`):** In exact real arithmetic, $l^{(0)} \le T(l^{(0)})$ implies $l^{(k)} \le l^{(k+1)}$ and $u^{(k+1)} \le u^{(k)}$. Under IEEE 754 `double` rounding, evaluating $\sum_{s'} P(s, \alpha, s') u^{(k)}_{s'}$ can round **upward** above $u^{(k)}_s$ by 1–2 ULPs (or round $l^{(k+1)}_s$ slightly below $l^{(k)}_s$), causing oscillations or premature crossover! Both Storm (`IntervalterationHelper.cpp:72-74`: `xCurr = std::max(xCurr, *xBest); yCurr = std::min(yCurr, *yBest)`) and PRISM (`IntervalIteration.h:62-85`: `enforceMonotonicityBelow = true`, `enforceMonotonicityAbove = true`) clamp updates monotonically, and PRISM computes the final midpoint as `soln_below[i] + ((soln_above[i] - soln_below[i]) / 2.0)` with an explicit `d >= soln_below[i] && d <= soln_above[i]` guard (`IntervalIteration.h:128-136`). Note however that pure IEEE 754 `roundTiesToEven` dot products can still slightly under-approximate $T(u)$ by $O(|S|\text{ ULP})$ unless directed rounding (`roundII` with `RoundingTowardsInf = true` negating lower iterates `-xy.first`, `IntervalterationHelper.cpp:43-48, 101, 175-199`) or exact arithmetic is used!
2. **Smooth Interval Iteration Stall Guard (`IntervalterationHelper.cpp:52-66`):** When damping cyclic oscillations via `smoothII` ($x' = x_{\text{best}} - \gamma (x_{\text{best}} - x_{\text{curr}})$), if $\gamma (x_{\text{best}} - x_{\text{curr}})$ underflows below $\frac{1}{2}\text{ULP}(x_{\text{best}})$, `xCurr == *xBest` would jump prematurely or stall; Storm explicitly nudges via `std::nextafter`.
3. **SVI Decision-Value Staging (`SoundValueIterationHelper.cpp:29-151`):** Decomposing $k$-step reachability on a `DTMC` gives $x^*_s = x^{(k)}_s + \sum_{s' \in S_?} \mathbf{P}_?^k(s, s') x^*_{s'}$, where $y^{(k)}_s = \sum_{s' \in S_?} \mathbf{P}_?^k(s, s')$ is the $k$-step retention probability in $S_?$. Once $\max_s y^{(k)}_s < 1$ (`SVIStage::y_less_1`), $\min_{s'} \frac{x^{(k)}_{s'}}{1 - y^{(k)}_{s'}} \le x^*_s \le \max_{s'} \frac{x^{(k)}_{s'}}{1 - y^{(k)}_{s'}}$. On an `MDP`, optimal choices can switch as the upper bound $b$ shrinks! Quatmann & Katoen's `SVIBackend` therefore tracks a **decision threshold $d$** (`dValue &= (rowVal.first - xCurr) / (yCurr - rowVal.second)`, lines 103–107)—the largest scalar weight below which a sub-optimal choice with smaller $y$ overtakes the current choice—clamping $b$ at $d$ until `SVIStage::b_eq_d` locks and transitions safely past the scheduler switch!
4. **OVI Verification-Stage Termination and Crossing (`OptimisticValueIterationHelper.cpp:135-232`):** After the lower-bound Gauss-Seidel stage (`GSVI`) reaches step residual $\le \varepsilon_{\text{guess}}$, `guessCandidate` constructs $u_s = v_s (1 + \varepsilon)$ (relative) or $v_s + \varepsilon$ (absolute, keeping $0 \mapsto 0$). The inductive verification stage runs at most $\lceil 1 / \varepsilon_{\text{guess}} \rceil$ coupled iterations updating $u_s \leftarrow \min(u_s, T(u)_s)$:
   - If $\forall s \in S_?:\ T(u)_s \le u_s$ (`backend.allDown()`), Park's induction principle ($\mathrm{lfp}(T) \le u$ whenever $T(u) \le u$ for monotone $T$ with unique fixed point) certifies $v \le x^* \le u$ immediately!
   - If $\forall s \in S_?:\ T(u)_s \ge u_s$ (`backend.allUp()`) or any component crosses $v_s > u_s$ (`crossed = true`), the guess $u$ was too low (below $x^*$); `OVI` aborts the verification burst immediately, tightens $\varepsilon_{\text{guess}} \leftarrow \text{error} / 2$ (`line 231`), and resumes `GSVI`. Note `line 230`: after 20 failed refinements, Storm logs a stall warning (which occurs if floating-point absorption prevents $T(u) \le u$ at ultra-tight $\varepsilon < 10^{-14}$).

### 5. Exact Rational Solvers, Kwek–Mehlhorn Rational Search, and Standalone Bellman / Farkas Certificates

`Basis: source + derived + execution`

When IEEE 754 ULP rounding is unacceptable (e.g., safety standards requiring mathematically sound probability bounds, ill-conditioned chains with $\delta < 10^{-12}$, or theorem-prover integration), Storm (`--exact`) and PRISM (`-exact`) operate over arbitrary-precision rationals $\mathbb{Q}$ (`mpq_class` / `BigRational`):

1. **Exact Policy Iteration and `ViToPi` (`IterativeMinMaxLinearEquationSolver.cpp:60-66, 335-350, 935-966`):** Policy Iteration evaluates a deterministic memoryless scheduler $\sigma : S_? \to \mathit{Act}$ by solving the exact linear system $(\mathbf{I} - \mathbf{P}_\sigma) x = b_\sigma$ over $\mathbb{Q}$ (via Gaussian elimination / topological SCC LU decomposition) and switches choices where $T_{\mathit{opt}}(x)_s \succ x_s$. Because pure rational Policy Iteration can pay heavy GMP GCD costs during early policy updates, Storm's `MinMaxMethod::ViToPi` runs fast IEEE 754 `double` `VI` first to extract a near-optimal initial scheduler `initialSched`, then finishes in 1–2 exact rational Policy Iteration steps!
2. **Kwek–Mehlhorn Continued-Fraction Rational Search (`RationalSearchHelper.cpp:61-167`, `KwekMehlhorn.cpp:13-70`):**
   - Given a `double` (or coarse rational) iterate $x_s$ at precision $10^{-p}$, `kwek_mehlhorn::sharpen(p, x_s)` computes the unique **minimal-denominator fraction** $r_s = \text{num}/\text{den} \in \big[\frac{\lfloor 10^p \{x_s\}\rfloor}{10^p}, \frac{\lfloor 10^p \{x_s\}\rfloor + 1}{10^p}\big]$ via recursive Euclidean continued-fraction expansion (`findRational(alpha, beta, gamma, delta)`).
   - `RSBackend` then evaluates **one exact Bellman sweep** over `storm::RationalNumber`: if $\forall s \in S_?:\ T_{\mathit{opt}}(r)_s == r_s$ (`allEqual == true`), $r$ is certified as the **exact** fixed point (assuming unique fixed point after `MEC` elimination)!
   - If `p > std::numeric_limits<double>::max_digits10` (`17` decimal digits, i.e., denominator $> \sim 10^8$), `sharpen` returns `RSResult::PrecisionExceeded` and `RationalSearchHelper::RS` seamlessly switches its inner `VI` operator from `double` to `storm::RationalNumber` (`RationalSearchHelper.cpp:154-159`)! Execution (`Probe 2C`) demonstrates recovering exact prime-denominator fixed points $(13/29, 11/29)$ after just 10 `double` `VI` sweeps (`tol = 1e-4, p = 3`).
3. **Standalone Inductive Bellman and Farkas Witness Certificates (Zero-Solver-TCB Verification):**
   Decoupling probabilistic verification from the ~300 KLOC C++/Java TCB of Storm/PRISM requires checking a compact rational certificate directly against the transition matrix $\mathbf{P}$ (after qualitative `Prob0` check where needed; Funke, Jantsch, & Baier *TACAS* 2020):

| Quantitative Claim on Reachability | Certificate Witness | Linear / Inductive Verification Conditions (Exact $\mathbb{Q}$, $O(\text{nnz})$) | Needs `MEC` Quotienting in Checker? |
| :--- | :--- | :--- | :--- |
| $P_{\max}(s_0 \models \Diamond \Psi) \le \lambda$ | Vector $u \in \mathbb{Q}_{\ge 0}^S$ | $u(s_0) \le \lambda$, $\forall t \in \Psi:\ u(t) \ge 1$, and $\forall s \in S \setminus \Psi, \forall \alpha \in \mathit{Act}(s):\ u(s) \ge \sum_{s'} \mathbf{P}(s, \alpha, s') u(s')$ | **No!** Park's induction ($\mathrm{lfp}(T_{\max}) \le u$ whenever $T_{\max}(u) \le u$) holds on the **raw unquotiented `MDP`**! |
| $P_{\max}(s_0 \models \Diamond \Psi) \ge \lambda$ | Occupancy measure $\mu \in \mathbb{Q}_{\ge 0}^{\sum_{s \notin \Psi} |\mathit{Act}(s)|}$ | Flow conservation $\forall s \in S \setminus \Psi:\ \sum_{\alpha} \mu(s, \alpha) - \sum_{s' \notin \Psi, \beta} \mu(s', \beta) \mathbf{P}(s', \beta, s) \le \mathbf{1}_{[s = s_0]}$, and target inflow $\sum_{s \notin \Psi, \alpha, t \in \Psi} \mu(s, \alpha) \mathbf{P}(s, \alpha, t) \ge \lambda$ | **No!** Positive `MEC` mass only hurts target inflow; every finite-flow $\mu \ge 0$ induces a valid randomized scheduler achieving $\ge \lambda$. |
| $P_{\min}(s_0 \models \Diamond \Psi) \le \lambda$ | Deterministic scheduler $\sigma : S \to \mathit{Act}$ + vector $u \in \mathbb{Q}_{\ge 0}^S$ | $u(s_0) \le \lambda$, $\forall t \in \Psi:\ u(t) \ge 1$, and $\forall s \in S \setminus \Psi:\ u(s) \ge \sum_{s'} \mathbf{P}(s, \sigma(s), s') u(s')$ | **No!** Induces a `DTMC` $\mathcal{M}^\sigma$ where $\mathrm{lfp}(T^\sigma) \le u$, and $\Pr^{\min} \le \Pr^\sigma \le u(s_0) \le \lambda$. |
| $P_{\min}(s_0 \models \Diamond \Psi) \ge \lambda$ | Vector $l \in \mathbb{Q}^S$ + `Prob0E` set $S_0$ (or ranking witness) | $l(s_0) \ge \lambda$, $\forall s \in S_0:\ l(s) \le 0$, $\forall t \in \Psi:\ l(t) \le 1$, and $\forall s \in S_?:\ \forall \alpha \in \mathit{Act}(s):\ l(s) \le \sum_{s'} \mathbf{P}(s, \alpha, s') l(s')$ **plus** verified `Prob0E` (ensuring $S_?$ has no `EC`s so $\mathrm{gfp}(T_{\min}) = \mathrm{lfp}(T_{\min})$!) | Requires **verified `EC`-freedom** on $\{s \mid l(s) > 0\} \setminus \Psi$ (otherwise $l \equiv 1$ on a trap cycle would falsely satisfy $l \le T_{\min}(l)$!). |

Observe that asymmetry carefully: an **upper** bound $T_{\max}(u) \le u$ certifies $\mathrm{lfp}(T_{\max}) \le u$ *with zero graph or `MEC` checks* because $\mathrm{lfp}(T_{\max})$ is the least pre-fixed point ($\mathrm{lfp}(T) = \inf\{u \mid T(u) \le u\}$ by Knaster–Tarski!), whereas a **lower** bound $l \le T_{\min}(l)$ only bounds $\mathrm{gfp}(T_{\min}) \ge l$ and therefore requires certifying that $\mathrm{gfp}(T_{\min}) = \mathrm{lfp}(T_{\min})$ (via `Prob0E` or a supermartingale ranking certificate)!

## Boundaries

- **IEEE 754 Floating-Point "`Sound`" Modes vs. Strict Directed-Rounding Proof Certificates (`known not to apply`):** While `--sound` (`OVI`, `SVI`, `II`) in Storm and `-intervaliter` in PRISM eliminate algorithmic premature-convergence errors (the $1/(1-\rho)$ contraction magnification bug), their default `double` instantiations still evaluate matrix-vector products in standard IEEE 754 round-to-nearest-even without interval arithmetic on matrix entries or outward FPU rounding modes (except Storm's specialized `roundII` mode). On extreme ill-conditioned chains where $(1 - \rho) \lesssim 10^{-15}$ approaches binary64 machine epsilon $2^{-53} \approx 1.11 \times 10^{-16}$, `double` `II`/`OVI`/`SVI` can stall or incur ULP drift; strict mathematical proof obligations must use `--exact` (`storm::RationalNumber` / PRISM `-exact`) or check the exported rational Bellman/Farkas inequality in exact arithmetic.
- **Exact Rational Solving for Time-Bounded `CSL` on `CTMC`s (`unsupported`):** Neither Storm (`SparseCtmcCslHelper.cpp:61-62`) nor PRISM supports `--exact` rational evaluation for continuous-time bounded until $\Phi \mathbin{\mathcal{U}}^{[t_1, t_2]} \Psi$ ($0 < t_2 < \infty$), because uniformization weights $e^{-qt} (qt)^k / k!$ are transcendental; only sound numerical Fox–Glynn error bounds are available.
- **Policy Iteration, `ViToPi`, and `RationalSearch` on Uncertain Interval Models (`IMDP` / `IDTMC`) (`unsupported`):** Storm explicitly rejects `PolicyIteration`, `ViToPi`, and `RationalSearch` when `ValueType` is `storm::Interval` or `storm::RationalInterval` (`IterativeMinMaxLinearEquationSolver.cpp:84-87, 338-340, 937-939, 972-974`), falling back to robust Value Iteration; PRISM similarly restricts `IMDPModelChecker` methods.
- **Parametric `MDP` Strategy-Independent Rational Functions (`known not to apply`):** Storm's `RationalFunction` engine (`storm-pars`) synthesizes closed-form rational functions $f(p_1, \dots, p_k) \in \mathbb{Q}(p_1, \dots, p_k)$ via state elimination for parametric `DTMC`s (`pMC`), where no scheduler choice exists. For parametric `MDP`s (`pMDP`), optimal schedulers vary piecewise across parameter regions, so no single rational function represents $P_{\max}$ globally; parameter lifting (`PLA`) over region boxes is used instead.
- **Partially Observable `MDP`s (`POMDP`s) and Stochastic Two-Player Games (`not examined`):** Quantitative reachability in `POMDP`s is undecidable in general and solved via belief-grid/cut-set under/over-approximations (`storm-pomdp`, PRISM `POMDPModelChecker.java`); two-player stochastic games (`SMG`s, Kelmendi et al. deflating `MEC`s) generalize `MEC` quotienting to Simple End Components and were not examined in this report.

## Evidence

### Primary Source Locations Examined

- **`moves-rwth/storm` (`926b19c62afe6eac917e87ecf1058f5ee116fbc2`, v2.0.0.3):**
  - `CMakeLists.txt:4-11, 69-88` (`VERSION 2.0.0.3`, GMP vs CLN exact arithmetic options, `carl-storm` `14.37`).
  - `src/storm/adapters/RationalNumberAdapter.h:1-48` & `RationalFunctionAdapter.h:1-74` (`mpq_class`, `cl_RA`, `carl::RationalFunction`).
  - `src/storm/solver/IterativeMinMaxLinearEquationSolver.cpp:56-130, 326-350, 900-1051` (automatic selection of `PolicyIteration` under `--exact` and `OptimisticValueIteration` under `--sound`; `ViToPi` and `RationalSearch` orchestration).
  - `src/storm/solver/helper/ValueIterationHelper.cpp:11-146` (standard absolute/relative stopping criterion `abs(currValue - *best) <= precision` and Gauss-Seidel monotonicity tracking).
  - `src/storm/solver/helper/IntervalterationHelper.cpp:21-256` (`IIBackend`, `smoothII` `std::nextafter` stall guard, `roundII` `RoundingTowardsInf`, `doublePrec = 2 * precision - 1e-6 * precision`, early-abort bound preservation).
  - `src/storm/solver/helper/SoundValueIterationHelper.cpp:29-318` (`SVIStage::{Initial, y_less_1, b_eq_d}`, decision threshold `dValue &= (rowVal.first - xCurr) / (yCurr - rowVal.second)`).
  - `src/storm/solver/helper/OptimisticValueIterationHelper.cpp:23-318` (`GSVIBackend`, `guessCandidate`, `OVIBackend` `allDown`/`allUp`/`crossed`, `ceil(1 / currentGuessValue)` verification budget, 20-refinement warning).
  - `src/storm/solver/helper/RationalSearchHelper.cpp:21-193` & `src/storm/utility/KwekMehlhorn.cpp:12-85` (continued-fraction `findRational`, `sharpen`, `RSBackend` exact fixed-point verification, `max_digits10` `double`-to-`RationalNumber` fallback).
  - `src/storm/storage/decomposition/MaximalEndComponentDecomposition.cpp:149-243` & `src/storm/transformer/EndComponentEliminator.h:12-206` (iterative Tarjan SCC + choice pruning + `performProbGreater0A`; `MEC` row-group collapsing).
  - `src/storm/modelchecker/prctl/helper/SparseMdpPrctlHelper.cpp:319-568` (`noEndComponents` for `(Minimize, UntilProbabilities)` and `(Maximize, ExpectedRewards)` vs `eliminateEndComponents` for non-unique fixed points).
  - `src/storm/modelchecker/csl/helper/SparseCtmcCslHelper.cpp:21-264` (rejection of `--exact` on bounded `CSL`; `1.02 * max_exit_rate` uniformization; `epsilon / 8.0` Fox–Glynn budget and relative-precision refinement loop).
- **`prismmodelchecker/prism` (`5a534b02fd1f17c6b30affc6231e280b40ae0860`, v4.12.1-dev):**
  - `prism/src/prism/Version.java:5-9` (`versionString = "4.12.1"`, `versionSuffixString = "dev"`).
  - `prism/src/prism/OptionsIntervalIteration.java:31-216` (`BoundMethod` enum: `DEFAULT`, `VARIANT_1_COARSE`, `VARIANT_1_FINE`, `VARIANT_2`, `DSMPI`; monotonicity toggles).
  - `prism/include/IntervalIteration.h:33-141` (`updateValueFromBelow`/`Above` monotonicity clamping; overflow-safe midpoint `x + (y - x) / 2` with bounds guard).
  - `prism/src/explicit/ECComputerDefault.java:40-248` (streaming de Alfaro Tarjan `findMECsStreaming`).
  - `prism/src/explicit/MDPModelChecker.java:508-666, 680-779, 980-1411` (`prob0`, nested `prob1`, `maxQuotient` for `!min && doPmaxQuotient`, `doValueIterationReachProbs` vs `doIntervalIterationReachProbs`, `computeReachProbsPolIter`).
  - `prism/src/explicit/CTMCModelChecker.java:180-222, 324-450` (implicit embedded `DTMC` reduction vs `FoxGlynn` uniformization with `termCritParam / 8.0`).

### Execution Evidence (Observed `2026-11-19`, Linux `x86_64`, Python `3.13.15`)

1. **Premature `VI` Convergence vs. `II` / `SVI` / `OVI`, `MEC` Quotienting, and Kwek–Mehlhorn + Farkas Certificate Probe:**
   - Command:
     ```bash
     python3 -c '
     from fractions import Fraction
     import math
     # 1. Slowly mixing chain delta = 1e-7, eps = 1e-6: exact x0* = 1 / (2 - delta)
     d, eps = 1e-7, 1e-6
     x0_ex = float(Fraction(1, 10_000_000) / (1 - (1 - Fraction(1, 10_000_000))**2))
     x, vi_k = [0.0, 0.0], 0
     while True:
         vi_k += 1
         nx = [(1.0 - d)*x[1] + d, (1.0 - d)*x[0]]
         if max(abs(nx[0]-x[0]), abs(nx[1]-x[1])) <= eps: x = nx; break
         x = nx
     # 2. Unquotiented 2-state MEC {s1, s2} under Pmax: T(v) = [max(v[1], 1/3), v[0]]
     l, u = [0.0, 0.0], [1.0, 1.0]
     for _ in range(100):
         l, u = [max(l[1], 1/3), l[0]], [max(u[1], 1/3), u[0]]
     # 3. Kwek-Mehlhorn sharpen + Farkas certificate on 2-state MDP
     def km(a, b, g, de):
         q1, r1 = divmod(a, b); q2, r2 = divmod(g, de)
         if q1 == q2 and r1 != 0:
             sp, sq = km(de, r2, b, r1); return q1*sp + sq, sp
         return (q1 if r1 == 0 else q1 + 1, 1)
     def sharpen(p, v):
         i = math.floor(v); t = int(math.trunc((v - i)*(10**p)))
         n, dn = km(t, 10**p, t + 1, 10**p); return Fraction(i) + Fraction(n, dn)
     vf = [0.0, 0.0]
     for _ in range(10):
         vf = [max((3/7)*vf[1] + 2/7, (1/2)*vf[1] + 1/5), max((5/6)*vf[0], (2/5)*vf[0] + 1/5)]
     cand = [sharpen(3, vf[0]), sharpen(3, vf[1])]
     assert cand == [max(Fraction(3,7)*cand[1]+Fraction(2,7), Fraction(1,2)*cand[1]+Fraction(1,5)),
                     max(Fraction(5,6)*cand[0], Fraction(2,5)*cand[0]+Fraction(1,5))]
     mu0, mu1 = Fraction(35, 29), Fraction(15, 29)
     assert mu0 == 1 + Fraction(2,5)*mu1 and mu1 == Fraction(3,7)*mu0
     assert Fraction(2,7)*mu0 + Fraction(1,5)*mu1 == cand[0]
     print(f"VI_k={vi_k} VI_err={abs(x[0]-x0_ex):.7f}; unq_MEC_gap={u[0]-l[0]:.6f}; RS={cand}; mu={(mu0,mu1)}")
     '
     ```
   - Recorded output:
     `VI_k=1 VI_err=0.4999999; unq_MEC_gap=0.666667; RS=[Fraction(13, 29), Fraction(11, 29)]; mu=(Fraction(35, 29), Fraction(15, 29))`
   - Full sweep across $\delta \in \{10^{-3}, 10^{-4}, 10^{-7}\}$ and asymmetric chains (`probe_pkg2.py`) confirmed `SVI` (`32,188` iters) and `OVI` (`64,647` iters, `13` refinements) reduce sweeps by $4.1\times$ and $2.03\times$ over `II` (`131,218` iters) at $\delta = 10^{-4}$ while maintaining actual error $\le 10^{-6}$, whereas `VI` halted at `46,051` iters with `5.00e-3` error.

## Revalidation

To determine cheaply whether these findings still hold on a newer commit of Storm or PRISM:

1. **Check Default Sound/Exact Solver Dispatch (`Storm`):** Inspect `IterativeMinMaxLinearEquationSolver::getMethod` in `src/storm/solver/IterativeMinMaxLinearEquationSolver.cpp` (`isExactMode` $\to$ `PolicyIteration`; `isForceSoundness()` $\to$ `OptimisticValueIteration`) and `computeHints` in `src/storm/modelchecker/prctl/helper/SparseMdpPrctlHelper.cpp` (`noEndComponents` conditions and `eliminateEndComponents = true` when `requirements.uniqueSolution()` holds).
2. **Check `II` / `SVI` / `OVI` Monotonicity and Stopping Criteria:** Diff `IntervalterationHelper.cpp`, `SoundValueIterationHelper.cpp`, and `OptimisticValueIterationHelper.cpp` in Storm alongside `prism/include/IntervalIteration.h` and `prism/src/explicit/MDPModelChecker.java` (`doPmaxQuotient` and `doIntervalIterationReachProbs`) in PRISM.
3. **Run Discriminating Model Probes:** Re-run the three-part one-liner above (or feed the 3-state PRISM model with $\delta = 10^{-7}$ to `storm --prism slow.pm --prop "P=? [F target]"` with default flags vs `--sound` vs `--exact`, and `prism slow.pm -pf "P=? [F target]"` with default flags vs `-intervaliter` vs `-exact`) to verify whether default flags still use unsound `VI` or have migrated to sound defaults (`OVI`/`II`).
