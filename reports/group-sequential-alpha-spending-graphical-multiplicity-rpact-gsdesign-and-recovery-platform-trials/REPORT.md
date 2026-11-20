# Group sequential error spending, adaptive combination tests, and graphical multiplicity: rpact, gsDesign, graphicalMCP, regulatory simulation expectations, and RECOVERY's interim monitoring

## Summary

- **rpact and gsDesign use the same spending functions and agree to about 1e-7 or better under emulation of their quadrature rules.** In both packages the Lan–DeMets O'Brien–Fleming-type function is `2·sided·(1 − Φ(z_{α/(2·sided)}/√t))`, written as `2(1 − Φ(z_{α/2}/√t))` with one-sided α in gsDesign; the Pocock-type, Kim–DeMets and Hwang–Shih–DeCani functions are written identically too.
  - The quadrature rules differ. rpact uses a composite 7-point Newton–Cotes rule on 91 equally spaced points over `[−6, c_{k−1}]`, with boundaries capped at 8. gsDesign uses the Jennison–Turnbull grid with `r = 18` (`12r − 3 = 213` points, Simpson), and also offers an optional Gauss–Legendre rule.
  - Python re-implementations of both rules were compared with a fine reference. They gave boundaries within `5.1e-8` (rpact rule) and `8.4e-7` (gsDesign rule), and attained α within `1e-9` and `7.2e-9`. Basis: source + execution (emulation of the rules, not the packages).
- **rpact's shipped smoke test pins numbers that independent computation reproduces.**
  - Default O'Brien–Fleming (kMax = 3, α = 0.025): critical values `3.4710914, 2.4544323, 2.0040356`, each matched to `≤ 4.4e-8`.
  - Default Fisher design: the cumulative α `0.0123085, 0.0196241, 0.025` is matched within Monte Carlo error over 2×10⁷ replications.
  - rpact's full unit-test suite is not in the public repository. `testPackage()` downloads it with `token`/`secret` credentials "distributed to members of the rpact user group". Basis: source + execution.
- **Two-sided O'Brien–Fleming-type spending is a convention, not a single formula.** rpact `sided = 2` and gsDesign symmetric designs spend `2(1 − Φ(z_{0.0125}/√t))` per side for total α = 0.05. Plugging total α into `2 − 2Φ(z_{α/2}/√t)` spends `1 − Φ(1.96/√t)` per side. At `t = 0.5` the per-side spending is 0.001525 versus 0.002787. Basis: source + derived.
- **Combination tests make data-dependent sample-size changes safe; the naive pooled z-test does not.** In a toy two-stage study under H0 (4×10⁶ replications) the CHW / inverse-normal test and Fisher's product test held α = 0.025 under every adaptation rule tried. The naive pooled test's α depended on the rule:

  | Adaptation rule | Naive pooled test α |
  | :--- | ---: |
  | Increase n2 in the "promising zone" 0.5 < z1 < 2 | 0.0239 |
  | Increase n2 when 0 < z1 < 1.2 | 0.0296 |
  | Adversarial choice of n2 | 0.0324 |

  The Bauer–Köhne size formula `α = α1 + c(ln α0 − ln α1)`, which rpact implements for two stages, gives 0.0250 when the futility rule is followed and 0.0276 when it is ignored. Basis: execution (toy model) + source.
- **The FDA's 2019 adaptive-design guidance expects simulation evidence when α control is not analytic.** It asks for a simulation report covering parameter configurations, iteration counts and their rationale, results, and code with random seeds. It states that 100,000 iterations per scenario give a 95% CI of about ±0.1%. rpact's simulation default is 1,000 iterations, a ±0.97 percentage-point half-width at α = 0.025 (derived). ICH E9 (1998) requires interim analyses to be planned in the protocol and "the overall probability of type I error" to be controlled. Basis: normative + derived.
- **graphicalMCP implements the Bretz et al. (2009) update rule exactly.** A toy re-implementation found no order dependence and no disagreement between the sequentially rejective shortcut and the Bonferroni closed test over 20,000 random 4-hypothesis graphs. The package uses different rejection tolerances in different paths:
  - shortcut: `round(adjusted_p, 10) <= alpha`;
  - closure: `alpha + .Machine$double.eps`, or `alpha + 1e-6` for parametric tests;
  - group sequential boundaries: Genz–Bretz quasi-Monte Carlo (`abseps = 1e-6`), with a silent fall back to `qnorm(1 − cumulative spend)` when root bracketing fails.

  Basis: source + execution (toy).
- **RECOVERY specified no numeric stopping boundaries in its protocol.** The DMC was asked whether the evidence on mortality was "strong enough (with a range of uncertainty around the results that is narrow enough) to affect national and global treatment strategies"; it reviewed unblinded analyses about every 2 weeks.
  - Multiplicity language changed across versions. V2.0 has "Due allowance will be made in the interpretation"; V8.0 has "Allowance for multiple treatment comparisons ... will be made"; V27.0 has no allowance sentence.
  - The tocilizumab report shows p values "without adjustment for multiple testing".
  - The dexamethasone arm closed when it passed the 2,000-patient enrolment target that the blinded steering committee had set for 90% power at two-sided P = 0.01.

  Basis: normative (protocol) + documentation (publications).

## Applicability

The software subjects are three R packages, each pinned to its GitHub HEAD on 2026-11-20:

- **rpact** 5.0.0 at `68538fbdd01d25c0516b488d82a5fc09b63362a9`: group sequential, inverse-normal and Fisher designs, and multi-arm simulation.
- **gsDesign** 4.0.0 at `d15fcff2e16f252f4b4e3963c89120abe1fc5cb6`: group sequential design with a library of spending functions.
- **graphicalMCP** 0.3.0.9000 at `74f2f31e3e49a209745a54a1b292463c5efeeb3a`: graphical multiple comparison procedures with closure, shortcut and group sequential extensions.

R was not available in the investigation environment, so **none of the packages was executed**. Their numerical behaviour is characterised in four ways:

1. from source;
2. from reference numbers they ship, namely rpact's smoke test and README;
3. by Python re-implementations of the algorithms read from source, labelled "emulation" or "toy";
4. by independent reference computations.

An emulation result measures the quadrature *rule* as re-implemented. It does not measure the package binary.

The regulatory subjects are the FDA's final November 2019 guidance and ICH E9 (Step 4, 1998). ICH E9(R1) and the ICH E20 draft were **not examined**.

The platform-trial subject is RECOVERY, read through:

- protocol versions V2.0 (2020-03-23), V8.0 (2020-07-08) and V27.0 (2023-09-13);
- three primary publications: dexamethasone (NEJM), hydroxychloroquine (NEJM) and tocilizumab (Lancet).

The statistical analysis plan and the DMC charter were **not examined**. RECOVERY did not use rpact, gsDesign or graphicalMCP as far as the examined documents show. The relationship is a contrast between formal error-spending machinery and a judgement-based monitoring rule; it is not a description of an implementation.

Unless stated otherwise:

- all boundaries are one-sided efficacy boundaries on the Z scale, without futility;
- information fractions `t_k` are equally spaced;
- α = 0.025 one-sided.

## Findings

### 1. The recursion every package approximates

Let `Z_k` be the standardised statistic at information fraction `t_k`, with increments `Δ_k = t_k − t_{k−1}`. Under H0 the canonical joint distribution has `Corr(Z_j, Z_k) = sqrt(t_j/t_k)` (Armitage–McPherson–Rowe; Jennison–Turnbull). The sub-density on the continuation region obeys:

```text
f_1(z) = φ(z)
f_k(z) = ∫_{-∞}^{c_{k-1}} f_{k-1}(u) · sqrt(t_k/Δ_k) · φ((z·sqrt(t_k) − u·sqrt(t_{k-1}))/sqrt(Δ_k)) du
P(cross at k) = ∫_{-∞}^{c_{k-1}} f_{k-1}(u) · [1 − Φ((c_k·sqrt(t_k) − u·sqrt(t_{k-1}))/sqrt(Δ_k))] du
```

An error-spending design (Lan–DeMets 1983) chooses `c_k` so that cumulative crossing probability equals `α(t_k)` for a spending function `α(·)`. A classical design instead fixes the shape: `c_k = C` (Pocock 1977) or `c_k = C/sqrt(t_k)` (O'Brien–Fleming 1979), and solves for `C`.

rpact's C++ (`src/f_design_group_sequential.cpp`, `getDensityValue`, lines 92–116, and `getSeqValue`, lines 217–231) is literally this recursion on the Z scale. `dn2` holds the quadrature-weighted previous sub-density. gsDesign's C code (`gsbound.c`, `gsbound1.c`, `gsdensity.c`, `gridpts.c`, `gsquad.c`) implements the same recursion following Jennison and Turnbull (2000, chapter 19). graphicalMCP instead calls `mvtnorm::pmvnorm` with `GenzBretz(maxpts = 25000, abseps = 1e-6)` on the `k`-dimensional normal with the correlation above (`R/gs_boundaries.R`).

Basis: source.

### 2. Quadrature rules and tolerances as implemented

| Aspect | rpact | gsDesign | graphicalMCP |
| :--- | :--- | :--- | :--- |
| Rule | Composite closed 7-point Newton–Cotes, weights `(41,216,27,272,27,216,41)·dx/140` (`C_NEWTON_COTES_MULTIPLIER = 6`) | Jennison–Turnbull grid: `6r−1` base points, logarithmic tails beyond ±3 SD, Simpson on points plus midpoints (`12r−3` points before truncation); option `gsDesign.quadrature = "gl"` selects Gauss–Legendre with 8–992 nodes | Genz–Bretz QMC for multivariate normal probabilities |
| Grid size | 91 points one-sided (`15 × 6 + 1`); 49 points per region two-sided (`8 × 6 + 1`) | `r = 18` default | `maxpts = 25000` |
| Region | `[futility bound or −6, min(c, 8)]`; values above 8 are capped (`C_UPPER_BOUNDS_DEFAULT = 8`; `if (decValue > C_UPPER_BOUNDS_DEFAULT)`, lines 304–306) | grid centred at the drift mean, truncated to the continuation region | upper limits `pmin(bounds, 20)` |
| Root finding | `bizero` on `[0, 8]` with `tolerance` (R default `C_DESIGN_TOLERANCE_DEFAULT <- 1e-08`), ≤ 100 iterations | `tol = 0.000001` | `stats::uniroot(..., tol = abseps)` with `abseps = 1e-6` |
| Documented accuracy | not stated | "accurate to about 10^-7 with the default r = 18"; Gauss–Legendre "accurate to about 10^-12" with "at most 992 nodes" (`R/gsDesign.R` lines 414–430) | Monte Carlo error "controlled by abseps" (comment in `graph_test_closure.R` line 310) |

Two small observations:

- rpact's normal density uses a float literal, `inv_sqrt_2pi / stDev * exp(-0.5f * a * a)` (line 70). Because 0.5 is exactly representable and the product is formed in `double`, this costs no precision.
- gsDesign's `sfLDOF` silently replaces an out-of-range parameter with 1: `if (is.null(param) || param < .005 || param > 20) param <- 1` (`R/gsSpending.R` line 706, introduced because gsDesign's default `sfupar = -4` is out of range for this family). A user who passes `sfupar = 25` gets the standard Lan–DeMets O'Brien–Fleming function without a warning.

Basis: source + documentation.

### 3. Measured accuracy of the two quadrature rules (emulation)

`support/gsd_numint.py` implements the recursion with three rules:

- the rpact rule above, re-implemented;
- the gsDesign `r = 18` grid, re-implemented;
- a 2,001-point Simpson reference on `[−10, c]`, cross-checked against 6,001 points, with a maximum boundary difference of `1.7e-11`.

Boundaries are solved by bisection, and attained α is re-evaluated with the reference rule.

| Spending function | K | Reference boundaries `c_1..c_K` | rpact-rule max\|Δc\| | rpact-rule α error | gsDesign-rule max\|Δc\| | gsDesign-rule α error |
| :--- | :---: | :--- | ---: | ---: | ---: | ---: |
| LD O'Brien–Fleming | 3 | 3.710303, 2.511427, 1.993047 | 1.9e-10 | −1.0e-11 | 4.7e-7 | +1.0e-9 |
| LD Pocock | 3 | 2.279428, 2.294911, 2.295940 | 3.6e-9 | −8.1e-11 | 3.3e-8 | −9.1e-10 |
| HSD γ = −4 | 3 | 3.010739, 2.546531, 1.999226 | 3.5e-10 | +1.1e-11 | 2.1e-8 | −1.1e-9 |
| LD O'Brien–Fleming | 5 | 4.876885, 3.357012, 2.680280, 2.289817, 2.031032 | 1.8e-8 | −8.0e-10 | 8.4e-7 | −7.2e-9 |
| LD Pocock | 5 | 2.437977, 2.426814, 2.410194, 2.396649, 2.386000 | 5.1e-8 | −9.4e-10 | 9.9e-8 | −2.6e-9 |
| HSD γ = −4 | 5 | 3.252668, 2.986046, 2.691657, 2.373667, 2.025321 | 1.7e-8 | −8.1e-10 | 2.0e-7 | −2.9e-9 |

Classical constants from the same reference, computed as one-sided 0.025 (equivalently two-sided 0.05, ignoring the negligible probability of crossing both sides):

| K | Pocock `C` | O'Brien–Fleming `C` (final boundary) |
| :---: | ---: | ---: |
| 2 | 2.1783 | 1.9774 |
| 3 | 2.2895 | 2.0040 |
| 4 | 2.3613 | 2.0243 |
| 5 | 2.4132 | 2.0401 |

These match independent upstream reference numbers:

- **README.** For classical O'Brien–Fleming with K = 2, t = (0.5, 1), the reference gives boundaries 2.796510 and 1.977431 and stage-1 α 0.002583. rpact's README example prints 2.797, 1.977 and 0.0026.
- **Smoke test.** The K = 3 O'Brien–Fleming boundaries and cumulative α reproduce the values in `inst/tests/testthat/test-rpact.R`:

  | Stage | Reproduced critical value | rpact test value | Reproduced cumulative α | rpact test value |
  | :---: | ---: | ---: | ---: | ---: |
  | 1 | 3.4710914 | 3.4710914 | 0.0002591737 | 0.00025917372 |
  | 2 | 2.4544323 | 2.4544323 | 0.0071600594 | 0.0071600594 |
  | 3 | 2.0040356 | 2.0040356 | 0.0250000000 | 0.02499999 |

  The rpact final α, `0.02499999`, sits `1e-8` below target, consistent with its `1e-8` root-finding tolerance.

Conclusion: discretisation error in either rule is at least two orders of magnitude below any clinically meaningful boundary difference for these designs. Disagreements between rpact and gsDesign larger than about `1e-6` therefore point to **specification** differences rather than numerics: the spending-function convention, binding versus non-binding futility, or the information-fraction definition.

Basis: execution (emulation and reference) + source.

### 4. Spending-function formulas and the two-sided convention

From rpact `getSpendingValueCpp` (lines 772–798) and gsDesign `R/gsSpending.R` (lines 579–735). Here `t ∈ [0, 1]`, and `sided ∈ {1, 2}` applies to rpact.

| Family | rpact | gsDesign |
| :--- | :--- | :--- |
| LD O'Brien–Fleming | `asOF`: `2·sided·(1 − Φ(z_{α/(2·sided)}/√t))` | `sfLDOF`: `2(1 − Φ(z_{α/2}/t^{ρ/2}))`, ρ = 1 default |
| LD Pocock | `asP`: `α·ln(1 + (e − 1)t)` | `sfLDPocock`: same |
| Kim–DeMets power | `asKD`: `α·t^γ` | `sfPower`: same family |
| Hwang–Shih–DeCani | `asHSD`: `α(1 − e^{−γt})/(1 − e^{−γ})`, `α·t` if γ = 0 | `sfHSD`: same |

Per-side cumulative spending for total two-sided α = 0.05, from `support/gsd_numint.py`:

| t | rpact `sided = 2` (= gsDesign symmetric with one-sided 0.025) | `2 − 2Φ(z_{α/2}/√t)` with α = 0.05, halved |
| ---: | ---: | ---: |
| 0.25 | 0.000007 | 0.000044 |
| 0.50 | 0.001525 | 0.002787 |
| 0.75 | 0.009649 | 0.011813 |
| 1.00 | 0.025000 | 0.025000 |

Both are valid spending functions with the same total. Interim boundaries differ, however, so a protocol that says only "Lan–DeMets O'Brien–Fleming, two-sided α = 0.05" is ambiguous. Which convention Lan and DeMets (1983) used for two-sided designs was **not examined** (the paper was not read in full text).

Basis: source + derived.

### 5. Adaptive combination tests and sample-size modification

**Formulas.**

- Fisher's product test (Bauer–Köhne 1994) rejects at stage 2 if `p1·p2 ≤ c`.
  - With no early stopping, `c = exp(−χ²_{4,1−α}/2) = 0.003804` for α = 0.025.
  - With early efficacy stopping at `α1` and binding futility at `α0`: `α = α1 + c(ln α0 − ln α1)`.
- rpact implements that closed form as `return piValue + c2 * (log(a1) - log(c1));` (`src/f_design_fisher_combination_test.cpp` lines 42–56). Here `piValue = c1` is the stage-1 level, `a1 = α0` and `c2` the product boundary. A weighted variant handles unequal stage weights.
- The size computation has exact closed forms for kMax = 2 and 3. The functions for kMax = 4, 5 and 6 are named `getFisherCombinationSizeApproximatelyKmax{4,5,6}Cpp`, and kMax is capped at 6 (`C_KMAX_UPPER_BOUND_FISHER <- 6L`).
- `getDesignFisher(iterations = …)` can simulate the design to check its critical values; the default is 0, meaning no simulation.
- The inverse-normal method (Lehmacher–Wassmer 1999) and the CHW weighted statistic (Cui–Hung–Wang 1999) combine stage-wise z statistics with weights fixed in advance: `Z = w1·z1 + w2·z2` with `w1² + w2² = 1`. Because `z2` is N(0,1) under H0 whatever the realised stage-2 size, `Z` keeps its null distribution under any data-dependent sample-size rule.

**Toy simulation** (`support/adaptive_ssr_toy.py`): two stages, known variance, no early stopping in the first block, 4×10⁶ replications, seed 20261120, Monte Carlo SE ≈ 0.00008. Each row allows stage 2 to grow from `n1` to `4·n1`.

| Adaptation rule (stage-2 size from z1) | P(increase) | naive pooled z | CHW / inverse normal | Fisher product |
| :--- | ---: | ---: | ---: | ---: |
| A: increase if 0.5 < z1 < 2.0 ("promising zone") | 0.2855 | 0.02393 | 0.02498 | 0.02492 |
| B: increase if 0 < z1 < 1.2 | 0.3844 | 0.02956 | 0.02498 | — |
| C: per z1, choose the size maximising the naive conditional rejection probability | 0.8772 | 0.03235 | 0.02498 | — |

The same run checked Bauer–Köhne with `α1 = 0.0102` and `α0 = 0.5`, so `c = 0.003802`:

| Scenario | Rejection rate |
| :--- | ---: |
| Closed form | 0.025000 |
| Simulated, futility followed | 0.02493 |
| Simulated, futility ignored | 0.02755 |

Interpretation:

- Rule A did not inflate the naive test. Raising the sample size only when interim results are favourable lowers the conditional rejection probability of the pooled statistic.
- Inflation appears when the size is raised after weak interim results (rule B) or chosen adversarially (rule C).
- The ignored-futility row is the binding-futility hazard. The FDA guidance says that under binding rules "the Type I error probability is controlled only if the stopping rules are followed" (2019 guidance, PDF page 16).
- rpact's Fisher design defaults to `bindingFutility = TRUE` (`C_BINDING_FUTILITY_FISHER_DEFAULT <- TRUE`). With the default `alpha0Vec = 1` (no futility) this has no effect.

**Multi-arm simulation in rpact** (`R/f_simulation_multiarm.R`, `src/f_simulation_multiarm.cpp`):

- It enumerates the closed system of `2^gMax − 1` intersection hypotheses (`.getIndicesOfClosedHypothesesSystemForSimulation`).
- Intersection tests are Bonferroni, Simes, Sidak, Dunnett (default) or Hierarchical; the conditional Dunnett test requires equal allocation ratios over stages.
- Treatment-selection rules are `best`, `rBest`, `epsilon`, `all` or `userDefined`.
- Stage-wise results are combined with the design's inverse-normal or Fisher combination function.
- The default number of simulation iterations is `C_MAX_SIMULATION_ITERATIONS_DEFAULT <- 1000L`.

Basis: source + execution (toy model).

### 6. What regulators ask of simulation-based α evidence

FDA, *Adaptive Designs for Clinical Trials of Drugs and Biologics* (November 2019), Section VI.A (PDF pages 22–24) and Section VIII documentation (PDF pages 32–33), says the following.

- **Null scenarios.** Type I error simulations are run "under a series of assumptions compatible with the null hypothesis". These assumptions include nuisance parameters such as control-arm rates and accrual. Monotonicity arguments can limit the scenarios needed. A grid of plausible values can support a claim that the maximal type I error is controlled "across the range covered by the grid". If observed nuisance values fall outside the grid ("unexpectedly 50 percent"), "additional simulations would be required".
- **Precision.** "Using 100,000 iterations per scenario, for instance, ensures a 95% confidence interval for estimated Type I error probability with a width of approximately ± 0.1%". Fewer iterations, for example 10,000, may suffice over a fine grid, or when the upper 95% confidence bound is below the target. The guidance prefers different random seeds per scenario.
- **Report contents** ("a detailed simulation report should be submitted, including"):
  - the design;
  - example trials;
  - the parameter configurations "including a justification of the adequacy";
  - iterations per scenario "and a rationale";
  - results;
  - code, including "the random seeds used to generate the simulation results", ideally runnable "in a widely-used statistical programming language";
  - conclusions.
- **Futility.** Nonbinding futility guidelines do "not increase the Type I error probability". With binding rules, a trial that continues despite meeting them "will likely" be considered "to have failed to provide evidence of efficacy" (PDF page 16).

ICH E9 (1998) §4.5 says "all interim analyses should be carefully planned in advance and described in the protocol". The protocol should describe "the schedule of interim analyses, or at least the considerations which will govern its generation, for example if flexible alpha spending function approaches are to be employed". And "the procedures selected should always ensure that the overall probability of type I error is controlled" (PDF pages 23–24).

Derived Monte Carlo precision at a true α of 0.025, using the half-width `1.96·sqrt(α(1−α)/n)`:

| Iterations | 95% half-width | Context |
| ---: | ---: | :--- |
| 1,000 | ±0.0097 | rpact simulation default |
| 10,000 | ±0.0031 | FDA's "fewer iterations might suffice" case |
| 100,000 | ±0.00097 | FDA's "±0.1%" example |
| 2×10⁷ | ±0.000068 | this report's Fisher cross-check |

Design features that force reliance on simulation include:

- unblinded sample-size re-estimation with a non-combination-test analysis;
- arm selection with a test that is not closed;
- response-adaptive randomisation;
- Bayesian decision rules;
- dependence of α on nuisance parameters.

The guidance discusses each of these in its sections V–VI. This report does not enumerate them further.

Basis: normative + derived.

### 7. Graphical multiplicity procedures in graphicalMCP

**The update rule.** Bretz, Maurer, Brannath and Posch (2009) update the graph when `H_j` is rejected:

```text
w_l ← w_l + w_j·g_jl                                   (l ≠ j)
g_lk ← (g_lk + g_lj·g_jk) / (1 − g_lj·g_jl)            (l ≠ k; l, k ≠ j)
```

All weights and transitions into or out of `j` are then set to 0. graphicalMCP's `graph_update()` implements this literally (`R/graph_update.R` lines 131–153), with a guard: `if (hyp_num == end_num || denominator <= 0) transitions[[hyp_num, end_num]] <- 0`.

**Procedures.**

- **Closed test** (`graph_test_closure()`). Intersection weights come from `graph_generate_weights()`, which removes the complement hypotheses with the same update. Local tests are Bonferroni, Simes, Hochberg or parametric. The parametric test uses `mvtnorm::pmvnorm` (Xi et al. 2017, per the package documentation). An intersection's adjusted p is the minimum over its test groups, and a hypothesis's adjusted p is the maximum over intersections containing it.
- **Shortcut** (`graph_test_shortcut()`). Sequentially rejective Bonferroni, at most `m` steps.
- **Group sequential shortcut** (`graph_test_shortcut_gsd()`, after Maurer–Bretz 2013). Each hypothesis has its own spending function and information fractions. With `look_back = FALSE` it uses adjusted repeated p-values; with `look_back = TRUE` it uses sequential p-values.

**Tolerances by code path.**

| Path | Rejection rule | Source |
| :--- | :--- | :--- |
| Shortcut | `rejected <- round(adjusted_p, 10) <= alpha` | `graph_test_shortcut.R` line 162 |
| Closure, non-parametric | `adjusted_p <= alpha + .Machine$double.eps` | `graph_test_closure.R` lines 313–321 |
| Closure, parametric | `adjusted_p <= alpha + 1e-6` ("to avoid false non-rejections at the boundary") | same |
| GSD boundaries | Genz–Bretz QMC, `uniroot(tol = abseps)`, `abseps = 1e-6` | `gs_boundaries.R` |

Two consequences follow from these lines (derived):

- For a consonant Bonferroni graph the shortcut and the closure are mathematically identical. An adjusted p in `(α + 2.2e-16, α + 5e-11]` is nevertheless rejected by the shortcut and not by the closure.
- The parametric closure tolerance knowingly permits rejection at up to `α + 1e-6`. That allowance equals the Monte Carlo error budget.

**Silent fallback.** `gs_boundaries()` returns `b_approx <- stats::qnorm(target_prob)` with no warning when bracketing fails (lines 107 and 124–127: `if (f_lower * f_upper > 0) { # Fallback: ... bounds_z[k] <- b_approx; next }`). Since `P(Z_1<b_1,…,Z_k<b) ≤ P(Z_k<b)`, the true boundary is never below `b_approx`, so the fallback is never conservative.

- Bracketing can fail only if the upper-end function value is not positive, i.e. when the spending increment at look `k` is zero or within QMC error of zero.
- The documented input domain admits this: information fractions "monotonically non-decreasing", and user spending functions may be flat.
- No such input was constructed or executed (**unknown** whether it occurs in practice).

**Toy check** (`support/graph_mcp_toy.py`, 20,000 random graphs, m = 4, seed 20261120). Weights and transitions were randomised, mostly complete graphs, with skewed small p-values. 17,155 graphs rejected at least one hypothesis. There were 0 order-dependence cases (three random rejection orders per graph) and 0 shortcut-versus-closure disagreements. This checks the re-implemented rule, not the package.

Basis: source + execution (toy).

### 8. RECOVERY: interim monitoring and multiplicity as specified and reported

| Item | V2.0 (2020-03-23) | V8.0 (2020-07-08) | V27.0 (2023-09-13) |
| :--- | :--- | :--- | :--- |
| DMC charge | Interim analyses supplied "in strict confidence"; DMC decides whether comparisons give evidence on mortality "strong enough (with a range of uncertainty around the results that is narrow enough) to affect national and global treatment strategies" | same text | same text |
| Numeric stopping boundary | none in protocol | none in protocol | none in protocol |
| Multiplicity | "The scope for multiple treatment comparisons will be taken into account in multiple pairwise tests. Due allowance will be made in the interpretation of all analyses" | "Allowance for multiple treatment comparisons due to the multi-arm design will be made. All p-values will be 2-sided." | allowance sentence absent; "All p-values will be 2-sided." |
| Shared control | phrase not present | controls included "only ... if, at the point of their randomisation, they could alternatively have been randomised to the active treatment of interest" | same |
| Blinding of trial team | until 28 days after last patient randomised to an arm | same | same |

Publications:

- **Dexamethasone** (NEJM, DOI 10.1056/NEJMoa2021436).
  - Sample sizes "could not be estimated" at the start. The steering committee, "unaware of the results", determined that 2,000 dexamethasone and 4,000 usual-care patients would give "at least 90%" power "at a two-sided P value of 0.01" to detect a 20% proportional reduction (4 percentage points at 20% mortality).
  - Recruitment to the arm closed on June 8, 2020.
  - Age adjustment "was not specified in the first version of the statistical analysis plan but was added once the imbalance in age became apparent"; unadjusted results are in the supplement.
  - Rate ratio 0.83 (95% CI 0.75–0.93), P < 0.001.
- **Hydroxychloroquine** (NEJM, DOI 10.1056/NEJMoa2022926). The DMC reviewed unblinded analyses "at intervals of approximately 2 weeks". On June 4, 2020, "in response to a request from the MHRA", it recommended that the chief investigators review the unblinded data. Enrolment closed June 5 for "no beneficial effect" (rate ratio 1.09, 95% CI 0.97–1.23).
- **Tocilizumab** (Lancet, DOI 10.1016/S0140-6736(21)00676-0): "All p values are two-sided and are shown without adjustment for multiple testing."

The power calculation's two-sided 0.01 level stands in for an explicit multiplicity allowance, but no formula for familywise error is given in the examined documents. Any quantitative familywise error-rate statement for RECOVERY would require the SAP, the DMC charter and the decision history (**not examined**).

Basis: normative (protocol) + documentation (publications).

### 9. Performance and resource footprint (six levels)

| Level | rpact | gsDesign | graphicalMCP | Probes in this report |
| :--- | :--- | :--- | :--- | :--- |
| L1 authoring/maintenance | `f_design_group_sequential.cpp` 1,599 lines; `f_design_group_sequential.R` 3,046; Fisher C++ 638; multi-arm R 1,344 + C++ 850 (measured, `wc -l`); effort **not measured** | `gsDesign.R` 2,241; `gsSpending.R` 1,836; integration C about 890 lines (measured) | closure 450, shortcut 275, gsd shortcut 895, update 183, boundaries 142 (measured) | 7 scripts plus a cross-check: 463 lines for the three main GSD probes (measured) |
| L2 build | repository 49,485 KB (GitHub API `size`); build **not measured** | 337,812 KB (API); build **not measured** | 44,018 KB (API); build **not measured** | none (Python 3.13, numpy 2.3.5) |
| L3 compute latency | per design **not measured**; one recursion step is O(91²) kernel evaluations (derived) | O((12r−3)²) ≈ 45,000 per step at r = 18 (derived) | per pmvnorm call ≤ 25,000 integrand evaluations (`maxpts`) | full boundary study 31 s wall (`gsd_numint.py`, all three rules); rule-only solves 0.00–0.03 s per design; SSR toy 3.9 s; graph toy 3.7 s; Fisher MC cross-check 3.7 s (measured with `/usr/bin/time`, 96-core x86-64 Linux workstation) |
| L4 executed-code throughput | **not measured** | **not measured** | **not measured** | not applicable |
| L5 checking | smoke test of 115 `test_that`/`expect_` lines public; full suite gated by credentials | 150 testthat files (tree listing) | 25 testthat files (tree listing) | — |
| L6 memory | **not measured** | **not measured** | **not measured** | peak RSS: GSD study 867 MB (the run includes the 6,001-point check grid), SSR toy 688 MB, Fisher cross-check 214 MB, graph toy 10 MB (measured) |

### 10. Human comprehensibility (C1) and conceptual simplicity (C2)

- **C1: the decisive parameters are not the numerically hard ones.** Section 3 shows discretisation error below `1e-6`. The mistakes a reviewer must catch are conventions:
  - two-sided spending (section 4);
  - binding versus non-binding futility (sections 5–6);
  - `round(·, 10)` versus `+eps` tolerances (section 7);
  - silent parameter coercion (`sfLDOF`) and silent boundary fallback (`gs_boundaries`).

  Each is local to one line of code, but its effect is non-local: it changes which hypotheses are rejected. None produces a diagnostic.
- **C1: legibility of upstream verification.** gsDesign and graphicalMCP ship their tests publicly. rpact's public smoke test pins defaults (section 3). Its full suite needs credentials, so a third party cannot read or rerun the package's own verification of non-default paths.
- **C2: one invariant, three mechanisms.** All three packages enforce one invariant: `P_H0(cross by look k) = α(t_k)` under the canonical joint normal law. They do so with three numerical mechanisms (Newton–Cotes recursion, Jennison–Turnbull or Gauss–Legendre recursion, and QMC on the full `k`-dimensional normal) and three tolerance conventions (`1e-8`, `1e-6`, `abseps = 1e-6`). The graph procedures add a fourth decision rule: shortcut rounding. A single "boundary oracle" interface, taking spending increments and correlation and returning boundaries with a certified error bound, would make these ordinary implementations of one contract. Rejection decisions would then use `alpha` plus a declared, propagated error budget instead of per-function constants.
- **C2: combination tests as the uniform abstraction.** Bauer–Köhne, inverse-normal and CHW are all instances of one idea: a fixed combination function of stage-wise p-values that are independent and uniform under H0. Sample-size re-estimation, arm selection (through closed testing) and early stopping are then ordinary cases. Simulation is needed only for the operating characteristics, not for α.

### 11. Validation of implementations and proposed checks (V1–V4)

- **V1, specification adequacy and non-vacuity.**
  - Reference values pinned in tests are only as good as their derivation. rpact's `0.02499999` at the last stage is tolerance-limited, which section 3 confirms independently.
  - A non-vacuity check for any spending design is that the attained α, re-evaluated with an independent quadrature, equals the spending function at every look. The emulation does this, to `≤ 1e-9` for the rpact rule.
  - For graph procedures, the order-invariance and shortcut-equals-closure theorems are executable properties (section 7).
- **V2, differential testing.**
  - Three independent numerical mechanisms implement the same law, so a design computed in rpact and in gsDesign, or by graphicalMCP's `gs_boundaries()`, should agree within the sum of their error budgets. This differential test was **not executed** against the packages, because R was unavailable.
  - No published rpact-versus-gsDesign comparison of boundaries was located (**not examined** in depth).
- **V3, concurrency or crash:** not applicable. rpact's `testPackage()` runs tests in parallel workers; its correctness under parallelism was **not examined**.
- **V4, field and human validation.**
  - RECOVERY shows the opposite design point. Monitoring rested on DMC judgement against a qualitative criterion, the multiplicity language changed across protocol versions, and publications report unadjusted p values.
  - ICH E9 asks that stopping guidelines and their properties be "clearly described". The protocol text examined describes the criterion qualitatively. Whether the DMC charter supplied quantitative guidelines is **not examined**.

## Boundaries

- **Not executed: the packages.** rpact, gsDesign and graphicalMCP were not run (no R). All "emulation" numbers re-implement the quadrature rules as read from source in Python, and their agreement with rpact's shipped reference values is the link to the real package. gsDesign's Gauss–Legendre option and graphicalMCP's QMC path were not emulated.
- **Unknown: the graphicalMCP fallback.** Whether `gs_boundaries()`'s silent fallback is reachable through the public API with realistic inputs was not established.
- **Not examined: other methods.** These include rpact's futility-bound algorithms (`f_design_futility_bounds.R`), optimal designs, enrichment designs, survival and count simulations, and the `bsXX` beta-spending paths; and gsDesign harm bounds (types 7–8) and `gsSurv` designs.
- **Not examined: other regulatory documents.** These are ICH E9(R1), the ICH E20 draft, EMA reflection papers, and the FDA multiple-endpoints guidance cited in the 2019 guidance.
- **Not examined: RECOVERY's governing documents.** The SAP, DMC charter, unpublished interim reports and the full arm-addition and removal history were not examined. No familywise error rate for RECOVERY is claimed.
- **Toy-model scope.** Toy results in sections 5 and 7 hold for the stated rules and seeds only. In particular, rule A's non-inflation is a property of that rule, not a general licence for pooled analyses after sample-size re-estimation.
- **Stronger conclusions not established:**
  - that rpact or gsDesign compute any particular design wrongly (no discrepancy was found);
  - that graphicalMCP's tolerance differences have changed a real decision;
  - that RECOVERY's α was inflated or controlled.

## Evidence

Observation date: all evidence was acquired on 2026-11-20 (UTC). The repositories were pinned to their HEAD commits that day via the GitHub API.

- **rpact** (`rpact-com/rpact` at `68538fbdd01d25c0516b488d82a5fc09b63362a9`):
  - `src/f_design_group_sequential.cpp`: lines 29–51 (constants), 66–71, 92–116, 151–197, 217–280, 296–310, 772–798;
  - `src/f_design_fisher_combination_test.cpp` 42–56 and 409–431;
  - `R/f_core_constants.R` 45–70, 134–146, 186–200, 399–403;
  - `R/f_simulation_multiarm.R` 20–45 and 292–311;
  - `R/f_test_execution.R` 565–664;
  - `inst/tests/testthat/test-rpact.R` (first two `test_that` blocks);
  - `README.md` lines 180–225;
  - `DESCRIPTION`.
- **gsDesign** (`keaven/gsDesign` at `d15fcff2e16f252f4b4e3963c89120abe1fc5cb6`): `R/gsDesign.R` 1–10, 128, 168, 414–430, 587–590; `R/gsSpending.R` 579–735; `src/gridpts.c` 1–93; `src/gsquad.c` 1–60.
- **graphicalMCP** (`openpharma/graphicalMCP` at `74f2f31e3e49a209745a54a1b292463c5efeeb3a`): `R/graph_update.R` 119–159; `R/graph_test_shortcut.R` 86–170; `R/graph_test_closure.R` 300–332; `R/gs_boundaries.R` 1–142; `R/adjust_p.R` 85–115; `R/graph_test_shortcut_gsd.R` 1–125 and 234–260.
- **Regulatory text:**
  - FDA guidance (November 2019), PDF pages 16, 22–24, 32–33;
  - ICH E9 (1998) §4.5, PDF pages 23–24.
- **RECOVERY:**
  - protocols V2.0 §3–4.4, V8.0 §3.2 and §4.4, V27.0 §3–4.4;
  - NEJM dexamethasone and hydroxychloroquine articles and the Lancet tocilizumab article, read via PubMed Central full text.
- **DOIs** were verified by lookup to publisher or index landing pages (Oxford Academic, PubMed, Taylor & Francis, CRAN for the Wassmer–Brannath monograph DOI). Paper content beyond titles and abstracts was not read for the 1969–1999 methodology papers. Their methods are described here as implemented by the packages and in standard form.
- **Execution.** Python 3.13 on x86-64 Linux; numpy 2.3.5. Scripts and outputs are in `support/`:
  - `gsd_numint.py` → `gsd_numint.out` (31 s, 867 MB peak RSS)
  - `rpact_reference_crosscheck.py 20000000 20261120` → `rpact_reference_crosscheck.out`
  - `adaptive_ssr_toy.py 4000000 20261120` → `adaptive_ssr_toy.out`
  - `graph_mcp_toy.py 20000 4 20261120` → `graph_mcp_toy.out`

## Revalidation

1. **Quadrature rules:** diff `src/f_design_group_sequential.cpp` lines 29–51 (grid constants) and `getW()`, and gsDesign `src/gridpts.c` and `src/gsquad.c`. If they are unchanged, the section 3 table stands. If they changed, edit the corresponding grid function in `support/gsd_numint.py` and rerun it (about 30 s).
2. **rpact reference values:** rerun `support/rpact_reference_crosscheck.py` against the current `inst/tests/testthat/test-rpact.R` numbers. With R available, `rpact::getDesignInverseNormal()$criticalValues` and `gsDesign::gsDesign(k=3, test.type=1, sfu="OF")$upper$bound` should both match `3.4710914, 2.4544323, 2.0040356` to about `1e-6`. That is the differential test this report could not run.
3. **Spending conventions:** diff `getSpendingValueCpp` and `sfLDOF`, including the `param < .005 || param > 20` coercion.
4. **graphicalMCP decisions:** grep `round(adjusted_p, 10)`, `.Machine$double.eps`, `1e-6` and `b_approx` in `R/graph_test_shortcut.R`, `R/graph_test_closure.R` and `R/gs_boundaries.R`. Rerun `support/graph_mcp_toy.py` if `R/graph_update.R` changes.
5. **Regulatory:** check whether the FDA 2019 guidance has been superseded or the ICH E20 guideline finalised. Re-read the simulation-report list.
6. **RECOVERY:** compare the multiplicity sentences across later protocol versions and read the SAP before making any familywise-error statement.
