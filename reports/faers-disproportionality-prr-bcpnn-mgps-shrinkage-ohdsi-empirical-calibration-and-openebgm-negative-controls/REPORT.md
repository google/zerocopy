# Pharmacovigilance disproportionality statistics (PRR, ROR, BCPNN IC, MGPS/EBGM, shrinkage O/E), their open implementations, reference-set evaluations, duplicate reports, and empirical calibration with negative and synthetic positive controls

## Summary

- **Five scores, one table.** PRR, ROR, the BCPNN information component (IC), the gamma-Poisson shrinker EBGM/EB05, and the shrinkage observed-to-expected IC all reduce a drug-event pair to `(a, n1., n.1, N)` or to an observed count `O` and an expected count `E = n1.·n.1/N`. Most disagreements between implementations come from three choices: how `n1.`, `n.1`, and `N` are counted; how the prior and shrinkage are chosen; and which threshold rule is applied.
- **openEBGM 0.11.0 changes the scores it reports in ways its documentation does not show.**
  1. Every scoring function first clamps the fitted hyperparameters to `alpha ∈ [beta/2, 2·beta]`, with `alpha` and `beta` limited to `[0.25, 10]` and `P` to `[1e-5, 0.99999]` (`R/f_helpers.R:18-42`). On the package's own CAERS example the fitted `alpha1 = 3.777` becomes `1.028`. For the three single-report cells the vignette prints, EBGM drops from 1.96/1.42/1.72 to 1.27/1.19/1.24. The number of cells with `QUANT_05 ≥ 2` falls from 44 to 24 of 13,441. A Python port reproduces the pinned vignette's printed Qn, EBGM, QUANT_05, and QUANT_95 values exactly *with* the clamp.
  2. The truncated likelihood normalizes each negative-binomial component separately (`R/f_likelihoodEqs.R:281-294`). The function's documentation instead describes the conditional marginal of the mixture.
- **openEBGM computes expected counts from unique report IDs. PhViD computes them from sums of cell counts.** On CAERS, PhViD-style `E` is a median 1.57× (5–95%: 0.37–5.77×) the openEBGM value. PhViD's exact BCPNN branch also reports `IC025` in log2 units, while its Monte-Carlo branch reports it in natural-log units (`R/BCPNN.R:44-48` vs `:84-87`).
- **Threshold choice changes signal sets substantially.** On PhViD's simulated data (102,483 cells), the following rules give 10,067–23,612 signals: Evans criteria with and without a Yates correction, PRR or ROR lower bound above 1, BCPNN `IC025 > 0`, and shrinkage `IC025 > 0`. Pairwise Jaccard overlaps run from 0.44 to 0.96. Evaluations against the reference sets used by the Observational Medical Outcomes Partnership (OMOP) give AUCs of 0.71 (PRR) to 0.83 (logistic-regression lower bound) for FDA AERS (Harpaz 2013). EB05 ≥ 2 gives sensitivity 0.36 and specificity 0.96.
- **Empirical calibration (`EmpiricalCalibration` 3.1.4).** The package fits a Gaussian bias distribution `N(μ, σ²)` to negative-control estimates, with each estimate's own standard error added in quadrature. The second column of Schuemie et al. 2014's Table 1 is the standard deviation σ. Refitting the package's shipped data (the fit returns an SD) reproduces the table's values. Recomputing from the paper's rounded published estimates reproduces its calibrated p-values 0.01, 0.71, and 0.84 only under the SD reading. CI calibration in the package defaults to an SD that is *linear* in |true log RR|. The 2018 paper's Table 1 values match the `legacy = TRUE` log-linear model. Calibration on the package's Southworth replication data raises 95% CI coverage of the true effect from 0.366 to 0.953 under leave-one-out (toy port).
- **Weak upstream test oracles.**
  - An `EmpiricalCalibration` test uses `tolerance = 1e03`, which makes it effectively vacuous.
  - Another asserts that the expected absolute systematic error (EASE) equals the null mean. That holds only because μ/σ ≈ 2.8 for the test data; on the package's `cohortMethod` data, EASE is 0.435 against a mean of −0.046.
  - `MethodEvaluation`'s metric test checks only that 7 values are returned.

## Applicability

**Subjects and their relationship.** The report interprets four open implementations through the primary literature that defines their methods.

- `cran/openEBGM` @ `d731cb3ee8d5fe6013666e05b9e55e2494d51f25` (version 0.11.0, CRAN publication 2026-10-22) implements DuMouchel's gamma-Poisson shrinker (GPS). The repository is GitHub's **read-only mirror of the CRAN package archive**: every commit is a CRAN release snapshot, not developer history. Its DESCRIPTION says much of the code is derived from PhViD (`DESCRIPTION:25`).
- `cran/PhViD` @ `bbb450c3837c6001710a328d382a27e856e601d8` (version 1.0.8, 2016-11-03) is used as an independent comparison implementation of PRR, ROR, BCPNN, and GPS with false-discovery-rate (FDR) based decision rules. It is also a read-only CRAN mirror, and this is the newest snapshot it holds.
- `OHDSI/EmpiricalCalibration` @ `03d4747fd805e92744d0bcaf603f4c2d0b13370b` (version 3.1.4) implements p-value, CI, and EASE calibration.
- `OHDSI/MethodEvaluation` @ `d7305910f6c6a390a9e423ffc1685a97c017183e` (version 2.4.2) holds the reference sets and the positive-control synthesis.

The literature subjects in `REPORT.json` define the methods and report the evaluations. Findings about code apply only to these revisions. NEWS entries quoted here show that behaviour changed in openEBGM 0.10.0, which introduced the clamp, and in EmpiricalCalibration 2.0.0, which introduced the linear-SD error model. Earlier releases therefore differ.

**Execution scope.** R was not available on the observation host. Every "execution" finding comes from an independent Python 3.13 + numpy re-implementation (`support/probes/`) run on the data files shipped in the pinned repositories. It is labelled `Basis: execution (toy re-implementation of X, not X itself)`. These ports are tied to the real packages only through exact agreement with numbers printed in the packages' own pinned vignettes, listed in each table. Paths or options that this check does not cover remain unverified against R.

**Domain scope.** The findings cover spontaneous-report disproportionality (FAERS, AERS, VigiBase, Yellow Card, CAERS/HFCS) and population-level effect estimation in claims and EHR data, the domain of the OMOP and OHDSI experiments. They do not cover regulatory decision procedures, causality assessment, or vaccine-specific methods.

## Findings

### 1. Shared notation and definitions

For drug `i` and event `j`, the 2×2 table has the following cells: `a = n11` reports with both, `b = n1. − a` reports with the drug but not the event, `c = n.1 − a` reports with the event but not the drug, and `d = N − a − b − c`. The expected count under independence is `E = n1.·n.1/N`. `O = a`.

| Score | Definition | Interval / signal rule as specified or implemented |
|---|---|---|
| PRR | `[a/(a+b)] / [c/(c+d)]` | Evans et al. 2001 minimum criteria: **≥3 cases, PRR ≥ 2, chi-squared ≥ 4**. PhViD: `var(log PRR) = 1/a − 1/(a+b) + 1/c − 1/(c+d)`, lower bound `qnorm(0.025, logPRR, sd)` (`R/PRR.R:62-63,85`) |
| ROR | `ad/(bc)` | `var(log ROR) = 1/a+1/b+1/c+1/d` (`R/ROR.R:61-62`); a common rule is lower 95% bound > 1 |
| IC (BCPNN) | `log2[p11/(p1.·p.1)]` with Beta/Dirichlet priors | PhViD exact branch (`R/BCPNN.R:38-48`); `IC025 = E[IC] − 1.96·sd[IC]` |
| Shrinkage O/E, IC | `(O+α1)/(E+α2)`; `IC = log2((O+α1)/(E+α2))`, usually `α1 = α2 = ½` | posterior `Gamma(O+α1, E+α2)`; credibility limits are `log2` gamma percentiles (Norén et al. 2013, §3.1, eqs. 11–12) |
| GPS EBGM | `exp(E[ln λ | N=n])` under a two-gamma mixture prior on `λ = μ/E` | EB05 = 5th percentile of the posterior; FDA screening has used EB05 ≥ 2 (Szarfman et al. 2002) |

Basis: documentation (Evans 2001 abstract; Norén 2013 §3.1 text; Szarfman 2002 abstract) + source (PhViD and openEBGM at their pinned revisions).

**PRR and the Evans criteria.** Evans et al. used the UK Yellow Card database and defined the minimum criteria for a signal as "3 or more cases, PRR at least 2, chi-squared of at least 4". Applied retrospectively to 15 newly marketed drugs (1996–8), the criteria produced 481 signals: 70% were known reactions, 13% were related to the underlying disease, and 17% needed further evaluation. Basis: documentation (indexed abstract). The abstract does not say whether the chi-squared statistic carries a Yates continuity correction. That choice moves the signal count by 10.5% (§4.4).

**BCPNN.** Bate et al. 1998 introduced the BCPNN for the WHO database. In one quarterly run, 1,004 drug-ADR combinations reached the "97.5% confidence level" (Basis: documentation, abstract). PhViD's exact branch implements Beta posteriors:

```r
  p1  <- 1 + n1.
  p2  <- 1 + N - n1.
  q1  <- 1 + n.1
  q2  <- 1 + N - n.1
  r1  <- 1 + n11
  r2b <- N - n11 -1 + (2+N)^2/(q1*p1)
  EICb <- log(2)^(-1) * (digamma(r1) - digamma(r1+r2b) - (digamma(p1) - digamma(p1+p2) + digamma(q1) - digamma(q1+q2)))
  VICb <- log(2)^(-2) * (trigamma(r1) - trigamma(r1+r2b) + (trigamma(p1) - trigamma(p1+p2) + trigamma(q1) - trigamma(q1+q2)))
```

(`cran/PhViD@bbb450c3…:R/BCPNN.R:38-45`). Norén et al. 2006 proposed more accurate credibility intervals than the earlier large-sample approximations, evaluated against Monte Carlo (abstract). Norén et al. 2013 state that the 2006 IC "is very well approximated by (12) with α1 = α2 = 1/2" for data sets with at least 1,000 records, with discrepancies "only in the second decimal" (§3.1). They also state that α1 = α2 = 1 approximates the earlier IC implementation. Basis: source + documentation.

**GPS and MGPS model** (DuMouchel 1999; equation numbers as cited in openEBGM's source comments).

- Counts follow `N_ij ~ Poisson(μ_ij)`, and `λ_ij = μ_ij/E_ij` has prior `P·Γ(α1, β1) + (1−P)·Γ(α2, β2)` (rate parameterisation).
- The marginal of `N` is therefore a two-component negative-binomial mixture with `size = α_k` and `prob = β_k/(β_k+E)`.
- The posterior is `Q_n·Γ(α1+n, β1+E) + (1−Q_n)·Γ(α2+n, β2+E)`, with `Q_n = P f1(n)/(P f1(n) + (1−P) f2(n))` (openEBGM `R/f_posteriorCalcs.R:61-74`, commented "Eq.5", "Eq. 6").
- `E[ln λ] = Q_n[ψ(α1+n) − ln(β1+E)] + (1−Q_n)[ψ(α2+n) − ln(β2+E)]`, `EBlog2 = E[ln λ]/ln 2`, and `EBGM = 2^EBlog2` (`:138-143`, "Eq.9", "Eq.10", "Eq.11").

DuMouchel's example table had 1,398 drugs × 952 events with total cell count 4.9 million (abstract). The derived cell count is 1,330,896. Szarfman et al. 2002 report that "only 3.4% of all 1.2 million drug-event pairs ever reported … generate signals (EB05 ≥ 2)", and that these pairs account for 23% (2.4 million) of 10.4 million reported pair counts. Basis: source + documentation.

**Shrinkage O/E** (Norén et al. 2013 §3.1). The paper describes (11) as the posterior mean of μ when `O ~ Po(μ·E)` with a `G(α1, α2)` prior. Credibility limits are percentiles of `G(O+α1, E+α2)` and "can be computed … as the inverse of the Gamma cumulative distribution function". The back-of-envelope approximations (13)–(14) lose accuracy "in the second decimal" provided `O + α1 > 1`. The paper also warns against fitting empirical-Bayes priors only to pairs with `O ≥ 1`, because this "will bias the prior towards higher values, since true negative associations are more likely … to result in zero counts". openEBGM's defaults (`zeroes = FALSE`, `N_star = 1`) take that route and attempt to correct it with a truncated likelihood (§2, §3). Basis: documentation (PMC full text).

### 2. openEBGM 0.11.0 implementation choices that change reported numbers

All references are to `cran/openEBGM@d731cb3ee8d5fe6013666e05b9e55e2494d51f25`. Basis: source.

| Stage | Choice at the pinned revision | Location |
|---|---|---|
| Counting `N` | `N = .countUnique(id)` per `(var1, var2)`; a report counts once per pair | `R/f_transformInput.R:95` |
| Marginals, `N_tot` | unique report IDs per `var1`, per `var2`, overall | `:103-104,109` |
| Expected count | `E := (N_v1 / N_tot) * N_v2` (unstratified) | `:110` |
| Stratified `E` | `Σ_s N_v1,s·N_v2,s/N_tot,s` over strata formed by pasting all columns whose names contain `strat` | `:112-127`; `R/f_checkInputs.R:162,179` |
| Stratum guards | error if any stratification variable has > `max_cats` (default 10) levels; warning if a stratum has < 50 unique IDs | `R/f_checkInputs.R:172-178,185-187` |
| Tiny `E` | `counts[E < 1e-10, E := 1e-10]` | `R/f_transformInput.R:134` |
| RR, PRR | `RR := round(N / E, digits)` (digits = 2); `PRR = (N/N_v1)/((N_v2−N)/(N_tot−N_v1))`; `NaN` PRR → `Inf` | `:142-146,152` |
| Zero cells | default `zeroes = FALSE`; with `TRUE`, full cross join `CJ(unique(var1), unique(var2))` filled with `N := 0` | `:97-101` |
| Squashing | `squashData(count = 1, bin_size = 50, keep_pts = 100, min_bin = 50, min_pts = 500)`: within one `N`, sort by `E`, leave the `keep_pts` largest-`E` points unsquashed, average `E` within bins, weight = bin size; final partial bin keeps its true size | `R/f_dataSquashing.R:73-111` |
| Auto-squashing | `keep_pts = c(100, 75, 50, 25)`, `cut_offs = c(500, 1e3, 1e4, 1e5, 5e5, 1e6, 5e6)`, `num_super_pts = c(50, 75, 150, 500, 750, 1e3, 2e3, 5e3)`, bin size `max(floor(...), 2)` | `:190-193,220` |
| Likelihood | four functions (squashed or not × zeros or not); truncated forms at `N_star` (default 1) | `R/f_likelihoodEqs.R:54-422` |
| Truncation form | `log_f - log_comp_f_cumul` **per component**, then `P·f1* + (1−P)·f2*` | `:278,290-293,406,418-421` |
| Numerical guards | `alpha, beta < 1e-100 → 1e-100`; `P ∈ [1e-10, 1−1e-10]`; NB `prob` clamped to `[1e-10, 1−1e-10]`; infinite log-lik terms → `±230` | `:257-259,286-288,393-394` |
| Starting values | **no default**: `theta_init` is a required argument of `exploreHypers`/`autoHyper` | `R/f_hyperEstimation.R:108-111,304-308` |
| Optimizers | `nlminb` (`eval.max = 1000, iter.max = 1000, abs.tol = 1e-20, xf.tol = 5e-14`) → `nlm` (`iterlim = 1000, fscale = 1000, stepmax = 100`) → `optim` BFGS (`fnscale = 1e3, parscale = 0.5, ndeps = 1e-5, maxit = 1000`), all on log/logit scale | `:129-133,161-193` |
| Convergence and acceptance | `converge`: nlm code 1 or 2, else code 0; `in_bounds`: `0 < α, β ≤ param_limit` (100), `0 < P < 1`; `autoHyper` takes the smallest negLL and requires ≥ `min_conv` (1) other estimates within `tol = c(0.2, 0.2, 0.2, 0.2, 0.05)` absolute or 10% relative | `:184,200-207,305-348` |
| Max data size | `max_pts = 20000` | `:111,307` |
| ECM alternative | `hyperEM`: `LL_tol = 1e-04` on the **proportional** LL change, `consecutive = 100`, `max_iter = 10000`, Millar-style acceleration every 100 iterations; log-scale estimates beyond ±11.5 are reset by random uniform draws, and the RNG is initialised from a default argument of 1234 | `R/f_EM_hyperEstimation.R:118-123,127,179-189,198`; `R/f_EM_updateTheta.R:22-23,57-58`; `R/f_EM_helpers.R:74-75` |
| Clamp before scoring | `min_theta = c(.25, .25, .25, .25, .00001)`, `max_theta = c(10, 10, 10, 10, .99999)`; then `alpha ≤ 2·beta` and `alpha ≥ 0.5·beta` | `R/f_helpers.R:18-42`; applied at `R/f_posteriorCalcs.R:60,135,219`, `R/f_createObject.R:56` |
| Quantiles | bisection on `[−1e5, 1e5]` from initial guess 1, tolerance `0.5·10^-digits`, result **rounded** to 2 decimals; default `ebScores(quantiles = c(5, 95))` | `R/f_posteriorCalcs.R:215-246`; `R/f_createObject.R:52` |
| Scores returned | `ebScores` returns `RR`, `PRR`, `EBGM`, `QUANT_05`, `QUANT_95` per pair, plus the hyperparameter object | `R/f_createObject.R:52-111` |

The clamp source, quoted verbatim:

```r
  theta_hat <- pmax(theta_hat, min_theta)
  theta_hat <- pmin(theta_hat, max_theta)
  # 'alpha' cannot be more than twice 'beta'
  theta_hat[1] <- min(theta_hat[1], 2 * theta_hat[2])
  theta_hat[3] <- min(theta_hat[3], 2 * theta_hat[4])
  # 'alpha' cannot be less than half of 'beta'
  theta_hat[1] <- max(theta_hat[1], 0.5 * theta_hat[2])
  theta_hat[3] <- max(theta_hat[3], 0.5 * theta_hat[4])
```

(`R/f_helpers.R:33-40`). `NEWS.md:15-17` (v0.10.0) records: "Added 'min_theta' & 'max_theta' arguments to Qn(), ebgm(), quantBisect(), & ebScores(). Alpha values now must also be between one half & twice the value of the corresponding beta values." The constraint bounds each prior component's mean `α/β` to `[0.5, 2]`. With the 0.11.0 vignette's own estimates (`α1/β1 = 3.777/0.514 = 7.35`), the most extreme component therefore cannot express a prior mean above 2. Basis: source + derived.

The truncated-likelihood code, quoted verbatim:

```r
  log_f <- dnbinom(N, size = size_f, prob = prob_f, log = TRUE)
  log_comp_f_cumul <- pnbinom(sum_limit, size = size_f, prob = prob_f,
    lower.tail = FALSE, log.p = TRUE
  )
  log_f - log_comp_f_cumul  #log(f / (1-f_cumul))
```

(`R/f_likelihoodEqs.R:289-293`; mixed at `:278` as `exp(log_P + log_f_star1) + exp(log_1_minus_P + log_f_star2)`). The roxygen text at `:198-201` says the function "computes the negative log-likelihood based on the conditional marginal distribution of the counts, *N*, given that *N >= N\**". For a two-component mixture that conditional is `[P f1 + (1−P) f2] / [P S1 + (1−P) S2]`, where `S_k = P_k(N ≥ N*)`. The implemented form is `P f1/S1 + (1−P) f2/S2`. The two coincide only if `S1 = S2` or `P ∈ {0, 1}`. Because `S_k` depends on each cell's `E`, no single `P` reparameterises one form into the other. Basis: source + derived. PhViD's truncated GPS likelihood uses the same per-component form (`R/GPS.R:212-219`). The mixture-level form survives only as a commented-out block (`R/GPS.R:203-209`).

### 3. Measured consequences on openEBGM's bundled data (toy port)

Basis: execution (toy re-implementation of openEBGM 0.11.0 in Python, not openEBGM itself). Input: `data/caers.rda` (15,204 rows; HFCS dietary-supplement reports received in 2025 per `R/data_caers.R`). Script and full output: `support/probes/probe_openebgm.py`, `support/outputs/probe_openebgm.txt`.

| Quantity | Pinned vignette prints | Toy port |
|---|---|---|
| `nrow(processRaw(caers))` | 13,441 | 13,441 (2,776 unique report IDs) |
| `E` for 3 named pairs | 0.0003602305, 0.1253602305, 0.0407060519 | identical to 10 decimals |
| RR / PRR, second pair | 7.98 / 8.00 | 7.98 / 8.0 |
| `nrow(squashData(processed))` | 1,202 | 1,202 |
| `autoHyper` on 2× squashed data | 3.77687, 0.51432, 3.75500, 3.66463, 0.04829; negLL 2994.068 | 3.77687, 0.51432, 3.75497, 3.66461, 0.04829; negLL 2994.068 |
| `Qn` for first 3 cells (θ̂ = 3.77699506, 0.51388202, 3.73820989, 3.64892019, 0.04817177) | 0.08983976 0.06931687 0.08191145 | identical (with clamp) |
| EBGM / QUANT_05 / QUANT_95 | 1.27 1.19 1.24 / 0.50 0.48 0.50 / 3.31 2.75 3.05 | identical (with clamp) |
| Cells with QUANT_05 ≥ 2 | 24 of 13,441 | 24 (with clamp) |

Running the same scoring **without** the clamp, i.e. using the vignette's raw MLE θ̂, gives:

- `Qn` 0.2658, 0.1306, 0.2100;
- EBGM 1.96, 1.42, 1.72;
- QUANT_95 12.77, 7.98, 11.02;
- **44** cells with QUANT_05 ≥ 2 instead of 24.

The clamp moves `α1` from 3.777 to 1.028 (`= 2·0.51388`). The exact match to the vignette shows that the published 0.11.0 example output already includes the clamp. Basis: execution + derived.

Further measurements on the same data:

- The mixture-level ("conditional marginal") truncated likelihood, fitted to the same squashed data, runs to a degenerate boundary: `α1 = 5.0e−11`, `P → 1`, negLL 3008.898. At openEBGM's estimate the same likelihood is 3111.247. So swapping in the mixture-level form as a "fix" would not yield usable hyperparameters for this data. The interpretation that zero-truncated data cannot identify prior mass near `λ = 0` is consistent with this result but untested. Basis: execution (toy) + derived.
- With stratification by `strat1` (sex: Female/Male/Not reported), stratified-to-unstratified `E` ratios run from 0.137 to 4.940 (median 1.096). Basis: execution (toy).
- Canida and Ihrie (2017, §7.1) report, for the 2017 CAERS subset on their machine:
  - `autoHyper` took 321.83 s elapsed with zero counts versus 2.58 s without. The hyperparameters were radically different: `P = 0.458` versus `0.0654`.
  - Squashed versus unsquashed fits took 2.54 s versus 24.79 s and produced nearly identical estimates.
  
  The pinned 0.11.0 vignette prints 8.59 s elapsed for the full 13,441 points versus 0.53 s for a twice-squashed set. The toy port reproduces that set as 911 points. Basis: documentation (timings on unstated hardware) + execution (toy row count). Of the 13,441 non-zero cells, 12,589 (93.7%) have `N = 1` (toy count), which is why squashing the `N = 1` stratum dominates the reduction.
- With `zeroes = TRUE` the CAERS table has 2,594 × 1,144 = 2,967,536 cells, of which 13,441 (0.45%) are non-zero. The test file therefore keeps only rows `2940000:nrow(...)` (`tests/testthat/testHypers.R:25`). Basis: execution (toy count) + source.

### 4. PhViD 1.0.8 versus openEBGM: counting, units, and thresholds

**4.1 Margins.** `as.PhViD` builds `n1.`, `n.1`, and `N` from sums of cell counts: `data_cont <- xtabs(n11 ~ .,data=data)`, `n1._mat <- apply(data_cont,1,sum)`, `N <- sum(n11)` (`R/as.PhViD.R:38-40,67`). A report that lists `k` events therefore adds `k` to its drug's margin. openEBGM counts unique reports instead (§2). On CAERS (13,441 pairs; 2,776 reports; sum of pair counts 15,164), the ratio of PhViD-style `E` to openEBGM `E` has median 1.569, 5–95% range 0.366–5.767, and maximum 38.078. Basis: execution (toy) + source.

**4.2 Units in BCPNN.** The exact branch puts `EICb` in log2 units (`log(2)^(-1) * (...)`, `R/BCPNN.R:44`). It then tests the posterior null as `post.H0 <- pnorm(log(RR0),EICb,sqrt(VICb))` (`:46`), which compares a natural-log threshold with a log2 distribution. The Monte-Carlo branch computes `IC_monte <- log(p11/(p1.* p.1))` (`:84`), in natural-log units, and takes `LB[m] <- sort(IC_monte)[round(NB.MC * 0.025)]` (`:87`). The reported lower bound therefore differs by a factor of 1/ln 2 ≈ 1.443 between `MC = FALSE` and `MC = TRUE`. At the default `RR0 = 1`, `log(RR0) = 0` and `post.H0` is unaffected. Basis: source + derived.

**4.3 Defaults.**

- `GPS` defaults to `PRIOR.INIT = c(alpha1= 0.2, beta1= 0.06, alpha2=1.4, beta2=1.8, w=0.1)`.
- With `TRONC = FALSE` it fits the untruncated likelihood to the full table including zeros (`xtabs`, `nlm`, `iterlim=500`; `R/GPS.R:2,19-29`).
- It reports `postE` as `E[log2 λ]` (EBlog2), not EBGM (`:67`).
- Its default lower bound is the 5th percentile (`.QuantileDuMouchel(0.05, …)`, `:76`). The bisection stops when `round(Cout*1e4) == 0`, i.e. when the CDF error is below 5e−5, rather than on an x-tolerance (`:189`).
- PRR and ROR rank by one-sided normal p-values and estimate FDR with `LBE` (`R/PRR.R:64,72-80`). BCPNN and GPS compute FDR from posterior null probabilities (`R/BCPNN.R:97`, `R/GPS.R:86`). The default `DECISION = 1` is FDR ≤ 0.05.

Basis: source.

**4.4 Threshold rules on PhViD's simulated data set.** The data set has 102,483 cells, 634 drugs, and 756 events, with `N = 1,196,487`; 39.4% of cells have `n11 = 1`. The documentation describes it as simulated to mimic the French database. Basis: execution (toy re-implementation of the formulas in §1, not PhViD's functions or its FDR rules). Output: `support/outputs/probe_disproportionality.txt`.

| Rule | Signals | of which `n11 ≤ 2` |
|---|---|---|
| Evans: `n ≥ 3`, PRR ≥ 2, χ² (no Yates) ≥ 4 | 11,442 | 0 |
| Evans with Yates-corrected χ² | 10,240 | 0 |
| PRR lower 95% bound > 1 | 23,612 | 10,047 |
| ROR lower 95% bound > 1 | 23,542 | 9,996 |
| ROR lower bound > 1 and `n ≥ 3` | 13,546 | 0 |
| BCPNN `IC025 > 0` (exact moments, normal limit) | 10,067 | 0 |
| shrinkage `IC025 > 0` (Gamma(O+½, E+½)) | 10,314 | 0 |

Jaccard overlaps between signal sets:

- Evans (uncorrected) vs Evans (Yates): 0.895;
- Evans vs PRR lower bound: 0.477;
- Evans vs shrinkage IC: 0.647;
- BCPNN vs shrinkage IC: 0.960;
- unrestricted ROR lower bound vs shrinkage IC: 0.438.

Interval-only rules admit thousands of 1–2-report pairs that Bayesian shrinkage excludes. This agrees with van Puijenbroek et al. 2002, who found the measures "broadly comparable when four or more cases per combination have been collected" (17,330 combinations, Lareb; abstract). Basis: execution (toy) + documentation.

### 5. Empirical evaluations against reference sets

| Study | Data | Methods | Reference set | Measured performance |
|---|---|---|---|---|
| Ryan et al. 2012 (OMOP experiment, *Stat Med* 31:4401–15) | 10 observational databases, > 130 million lives | 8 methods | 53 drug-outcome pairs (positive and negative) | at RR > 1, p < 0.05: false-positive rate > 18% and PPV < 38% for all methods; best AUC 0.77 (high-dimensional propensity score); at 50% sensitivity, FPR 16–30%; at 10% FPR, sensitivity 9–33% (abstract) |
| Ryan et al. 2013 reference set (*Drug Saf* 36 S1:33–47) | literature, structured product labels | — | 399 test cases: 165 positive, 234 negative, 4 outcomes | positives for kidney injury and GI bleeding mostly RCT-supported; liver injury and MI mostly case reports only (abstract) |
| Ryan et al. 2013 comparison (*Drug Saf* 36 S1:143–58) | 5 databases (4 claims, 1 EHR) | 7 methods incl. disproportionality, temporal pattern discovery, LGPS | the 399 cases | "AUC > 0.70 achievable for all outcomes and databases with more than one analytical approach"; self-controlled designs best; "All methods had lower coverage probability than the expected nominal properties" (abstract) |
| Harpaz et al. 2013 (*Clin Pharmacol Ther* 93:539–46) | FDA AERS 1968–2011Q3, 4,784,337 reports, duplicates removed, Empirica Signal 7.3 | MGPS, PRR, ROR, LR, ELR | OMOP gold standard as 398 cases (164+/234−), 394 used, 9 unreported | AUC from 0.71 (PRR) to 0.83 (LR05); lower-bound scores beat point estimates; EB05 stratified 0.79 vs unstratified 0.76; MI hardest (AUC 0.58–0.67); EB05 ≥ 2 → sensitivity 0.36, specificity 0.96; EB05 ≥ 1 → 0.74 / 0.67; Youden-optimal EB05 thresholds 0.91–2.18 depending on cost weighting (Results, Tables 3–4) |

Basis: documentation (PMC full text for Harpaz; indexed abstracts for the others).

**The reference set as shipped.** Basis: execution (independent `.rda` reader counting rows; `support/outputs/probe_reference_sets.txt`).

- `MethodEvaluation`'s `omopReferenceSet` has 399 rows: 165 positive and 234 negative, 182 distinct exposure concept IDs.
- Per outcome: acute liver failure 81+/37−, acute MI 36+/66−, acute renal failure 24+/64−, upper GI bleeding 24+/67−.
- Harpaz describes the gold standard as 398 cases (164 positive) spanning 181 drugs. The shipped table has one more positive row and one more exposure ID; which row differs was not examined.
- `euadrReferenceSet` has **93** rows (43+/50−, 10 outcomes; cardiac valve fibrosis has 0 positives). Its documentation says "A data frame with 399 rows" (`R/MethodEvaluation.R:72`), apparently copied from the OMOP entry.
- `ohdsiNegativeControls` has 200 rows. 100 are outcome controls, 25 for each of diclofenac, ciprofloxacin, metformin, and sertraline as target. The other 100 are exposure controls, 25 for each outcome of interest: acute pancreatitis, GI bleeding, stroke, and inflammatory bowel disease.

**What these evaluations do and do not test.**

- They test **ranking discrimination** (AUC) of a score against binary truth, and sometimes coverage and bias. They do not test calibration of disproportionality magnitudes, because the truth has no effect size; Ryan 2013 says magnitudes "cannot be reliably obtained".
- They do not test the effect of implementation choices such as hyperparameter estimation, clamps, or margin counting. Harpaz used one commercial MGPS implementation.
- They do not test timeliness. Harpaz did not examine signal onset.
- They do not fully test robustness to the reference set's own dependence on spontaneous reports, which Harpaz names as the main limitation.

Basis: derived from the cited designs.

### 6. Duplicate reports

- **Tregunno et al. 2014** applied the probabilistic record-matching algorithm vigiMatch to VigiBase reports from 2000–2010. Matching used drugs, ADRs, age, sex, country, and onset date. The UK, Danish, and Spanish national centres reviewed the flagged pairs.
  - 2.5% of evaluable reports were suspected duplicates: UK 1.4%, Denmark 1.0%, Spain 0.7%. Literature reports had a rate of 11%, fatal reports 5%, and consumer reports 0.5%.
  - The predictive value for confirmed or likely duplicates was 86% (UK), 64% (DK), and 33% (ES).
  - Previously unknown confirmed duplicates made up 89% (ES), 60% (UK), and 38% (DK), despite in-house rule-based screening. Fewer than 10% of flagged pairs were unrelated.
  
  Basis: documentation (abstract).
- **Norén et al. 2007** introduced the hit-miss-mixture method. It reached 94.7% accuracy in identifying the most likely duplicate, and 63% recall with 71% precision in separating true duplicates from random matches. Basis: documentation (abstract).
- **Consequence for the statistics (derived).** A duplicated report inflates `a` and both margins. Under openEBGM's unique-ID counting this happens only if the duplicates carry different IDs. PRR and ROR rules with `n ≥ 3` can be met by one patient reported three times. None of the four pinned packages performs record linkage. openEBGM's `processRaw` deduplicates only identical `id` values (`.countUnique`, `R/f_helpers.R:13-16`). Neither Tregunno's nor Norén's abstract reports the change in disproportionality scores after deduplication: **not measured** here.

### 7. Empirical p-value calibration

**Model** (Schuemie et al. 2014 §2.6). For negative control `i`, the paper assumes `y_i ~ N(θ_i, τ_i²)` and `θ_i ~ N(μ, σ²)`. It estimates `μ` and `σ` by maximum likelihood of `y_i ~ N(μ, σ² + τ_i²)`. For a new estimate it computes one-sided p-values `Φ((y − μ)/√(σ² + τ²))` and their complement, and the two-sided p-value is twice the smaller. Basis: documentation.

**Implementation** (`OHDSI/EmpiricalCalibration@03d4747f…`; Basis: source):

- `fitNull` drops non-finite inputs and estimates with `|logRr| > log(100)` (`R/EmpiricalCalibrationUsingAsymptotics.R:49-73`; NEWS 3.1.4). It optimises `(mean, precision)` from `theta <- c(0, 1)` with `optim` (default Nelder–Mead) and reports `sd = 1/sqrt(precision)` (`:78-81`).
- The likelihood is `-Σ log gaussianProduct(logRr_i, μ, se_i, sd)`, with point-mass handling when `sd < 1e-6` (`src/RcppWrapper.cpp:152-171`).
- `calibrateP` computes `pUpperBound <- pnorm((null[1] - logRr[i]) / sqrt(null[2]^2 + seLogRr[i]^2))`, the mirror lower bound, and `2 * min(...)` (`R/EmpiricalCalibrationUsingAsymptotics.R:148-152`).
- The MCMC null uses a Metropolis sampler with `iter = 100000` and a `Gamma(1e-4, 1e-4)` prior on the precision (`R/EmpiricalCalibrationUsingMcmc.R:159`; `R/Likelihoods.R:45-51`).

**Reproduction on the package's own data** (Basis: execution, toy re-implementation of EmpiricalCalibration, not EmpiricalCalibration; `support/outputs/probe_empirical_calibration.txt`).

| Shipped data set | Negatives | Toy μ̂, σ̂ | Paper Table 1 | Calibrated p, drug of interest | Paper / vignette | Traditional p < 0.05 among negatives | Leave-one-out calibrated p < 0.05 |
|---|---|---|---|---|---|---|---|
| `sccs` (sertraline, UGIB) | 45 | 0.7921, 0.2834 | 0.79, 0.28 | 0.8390 | 0.84 / vignette 0.7922, 0.2834, p 0.8389142 | 33/45 | 2/45 |
| `caseControl` | 46 | 0.9001, 0.3447 | 0.90, 0.35 | 0.7086 | 0.71 | 33/46 | 5/46 |
| `cohortMethod` (isoniazid, liver) | 30 | −0.0459, 0.5432 | −0.05, 0.54 | 0.0132 | 0.01 | 17/30 | 2/30 |

The paper reports 17/34 (cohort), 33/46 (case-control), and 33/46 (SCCS) nominally significant negatives, and 2/34, 5/46, and 3/46 after leave-one-out calibration (§3.1–3.2). The shipped `cohortMethod` and `sccs` tables contain 30 and 45 negatives rather than 34 and 46.

**Table 1's second column is σ (an SD).** The PMC caption describes it as the variance. A derived check using only the rounded published effect estimates and CIs reproduces the paper's calibrated p-values only when the column is read as an SD:

| Case | Column read as SD | Column read as variance | Paper |
|---|---|---|---|
| isoniazid cohort | 0.013 | 0.060 | 0.01 |
| sertraline case-control | 0.755 | 0.851 | 0.71 |
| sertraline SCCS | 0.868 | 0.928 | 0.84 |

Refitting the shipped data gives σ̂ = 0.28/0.34/0.54 and p = 0.84/0.71/0.013, which agree with the paper. Basis: execution (toy) + derived.

**Published effects of p-value calibration** (Schuemie et al. 2014 §1, §3.4, Fig. 4; Basis: documentation).

- Of 4,970 abstracts with effect estimates, drawn from 31,386 observational papers over 10 years, 82% were nominally significant.
- Under the smallest assumed bias (`μ = 0, σ = 0.25`), 38% remained significant, "at least 54% of significant findings would be deemed non-significant after calibration".
- Medium bias (`0.25, 0.25`) left 33% and large bias (`0.5, 0.5`) left 14%.

### 8. Confidence-interval calibration and synthetic positive controls

**Model** (Schuemie et al. 2018, Materials and Methods). For controls with true log effect `β_i` the paper models the bias as Gaussian with a mean and an SD that are each linear "after appropriate transformation" in `β_i`. Its Table 1 labels the second pair of parameters as intercept and slope "of a model for estimating the logarithm of the SD". The text naming the parameter values of an unbiased study renders as images in the PMC version. Derived from the model: no bias requires mean intercept 0, mean slope 1, and SD 0, i.e. log-SD intercept → −∞. The calibrated bounds solve `Φ((y − mean(β))/√(sd(β)² + τ²)) = 0.025, 0.975`; the point estimate uses 0.5. Basis: documentation + derived.

**Implementation differs by default.** `fitSystematicErrorModel(..., legacy = FALSE)` uses `sd <- theta[3] + theta[4] * abs(trueLogRr[i])`, a *linear* SD (`R/Likelihoods.R:56`). The paper's form `sd <- exp(theta[3] + theta[4] * trueLogRr[i])` survives only as `legacy = TRUE` (`:76`). Optimisation is BFGS from `c(0, 1, 0.1, 0)` (default) or `c(0, 1, -2, 0)` with `parscale = c(1, 1, 10, 10)` (legacy) (`R/ConfidenceIntervalCalibration.R:77-95`). NEWS 2.0.0 (line 115) records the switch. Two documentation lines still describe the log form:

- the roxygen for `fitSystematicErrorModel` says "The mean and log(standard deviations) of the error distributions are assumed to be linear" (`R/ConfidenceIntervalCalibration.R:22-24`);
- `convertNullToErrorModel` documents `sdSlope` as "The slope for the log of the standard deviation" (`:360`), although it builds a model named `sdIntercept`/`sdSlope` (`:383`).

For the default model, bounds come from `uniroot` on `[−100, 100]`, and `NA` is returned if the bracket does not change sign. The legacy model first grid-searches integer steps for a bracket (`:179-260`). The point estimate is the same root with `ciWidth = 0`, i.e. `(logRr − meanIntercept)/meanSlope` (`:272-282`). Basis: source + derived.

**Toy reproduction** (`support/outputs/probe_empirical_calibration.txt`; Basis: execution, toy, not EmpiricalCalibration):

| Data shipped in package | Default (linear-SD) model, toy | Vignette (`EmpiricalCiCalibrationVignette.pdf`) | Legacy model, toy | Paper Table 1 |
|---|---|---|---|---|
| `southworthReplication` (49 neg., 3×41 pos.) | −0.06655, 0.933292, 0.187466, 0.002977 | −0.066550795, 0.933292141, 0.187468405, 0.002979502 | −0.0665, 0.9333, −1.6742, 0.0158 | −0.07, 0.93, −1.67, 0.02 |
| `grahamReplication` (49 neg.) | −0.034011, 0.986155, 0.05294, 0.019959 | not printed | −0.034, 0.9862, −2.9194, 0.2921 | −0.03, 0.99, −2.92, 0.29 |

For the Southworth outcome of interest (GI bleeding):

- uncalibrated RR 0.699 (0.614–0.797);
- toy calibrated logRr −0.3118 with bounds [−0.7340, 0.1067];
- vignette prints −0.3117702 [−0.733957, 0.1067054], i.e. RR 0.732 (0.480–1.113).

Coverage of the true effect by the 95% CI over all controls, with leave-one-group-out calibration (a negative control plus the positive controls derived from it, as in the 2018 and 2020 papers):

- Southworth: **0.366 uncalibrated → 0.953 calibrated**;
- Graham: **0.863 → 0.927**.

These coverages come from the toy port on the package's data. The 2018 paper reports coverage only in Figs. 1–4 (images, not transcribed here) and states that "the 95% calibrated CI contains the truth ∼95% of the time". Schuemie et al. 2020 (OHDSI Methods Benchmark) report that "in most contexts, only half of the 95% confidence intervals … contain the corresponding true effect size". After calibration, the best SCCS variants reached 94% and 95% coverage in one claims database, with AUC 0.95–0.98 for the SCCS adjusting for all drugs. Basis: documentation.

**Positive-control synthesis by outcome injection** (`OHDSI/MethodEvaluation@d7305910…`; Basis: source).

- `synthesizePositiveControls` defaults:
  - `modelType = "poisson"`, `minOutcomeCountForModel = 100`, `minOutcomeCountForInjection = 25`;
  - an L1 (`laplace`) prior with cross-validation;
  - `washoutPeriod = 183`, `effectSizes = c(1, 1.25, 1.5, 2, 4)`, `precision = 0.01`.
  
  (`R/PositiveControlSynthesis.R:140-192`). The deprecated `injectSignals` is a wrapper that calls `.Deprecated("synthesizePositiveControls")` (`R/SignalInjection.R:124,177`).
- An outcome model is fitted only if the summed outcome count is at least `minOutcomeCountForModel` (`:748`). Injection happens only for pairs with `observedOutcomes > minOutcomeCountForInjection`, a strict inequality (`:1001`). Effect size 1 injects nothing (`:1114-1119`).
- Poisson injection:

```r
  targetCount <- resultSubset$observedOutcomes[1] * (effectSize - 1)
  ...
  while (round(abs(sum(newOutcomeCounts) - targetCount)) > precision * targetCount) {
    newOutcomeCounts <- rpois(
      nrow(exposures),
      multiplier * exposures$prediction * (effectSize - 1)
    )
```

(`:1170,1175-1179`). Counts are capped at days at risk (`:1180`). After every 100 draws the multiplier is rescaled by `1/mean(ratios)` (`:1182-1184`). The achieved effect is recorded as `injectedRr <- 1 + (nrow(newOutcomes) / resultSubset$observedOutcomes[1])` (`:1218`).

- Survival injection draws exponential times scaled by the predicted hazard. It corrects the target for censoring at new events and reports `rateAfter / rateBefore` (`:1231-1272`).

Schuemie et al. 2018 (Limitations) note that "injection of outcomes to synthesize positive controls can only maintain measured confounding", so calibration may underestimate systematic error. They also note that 50 negative controls per study might be reduced to about 30, and that one replication required 50 negative and 150 positive control outcome estimates. The outcome model for "ingrowing nail" had AUC 0.71, and the replications used 5,482–26,097 candidate covariates. Basis: documentation.

**Evaluation metrics** (`R/Metrics.R:44-114`; Basis: source).

- Non-estimable controls are imputed as `logRr = 0`, `seLogRr = 999`, `p = 1` before any metric is computed (`:82-87`).
- AUC comes from `pROC` on `logRr` against `trueLogRr > 0`.
- Coverage is the fraction with `ci95Lb < exp(trueLogRr) < ci95Ub`.
- `meanP` is the geometric mean precision minus one.
- Type 1 and type 2 error rates are computed at 0.05.
- All metrics are rounded to 2 decimals.

### 9. Expected absolute systematic error (EASE)

`closedFormIntegral(x, mu, sigma)` returns `mu * pnorm(x, mu, sigma) - 1 - sigma^2 * dnorm(x, mu, sigma)` (body quoted; the definition spans three lines). EASE is `F(∞) − 2F(0) + F(−∞) = μ(1 − 2Φ(−μ/σ)) + 2σ²φ(0; μ, σ)`, which is `E|X|` for `X ~ N(μ, σ²)` (`R/ExpectedSystematicError.R:19-25,58-65`). The toy closed form agrees with numerical integration to 4 decimals on all three shipped nulls (sccs 0.7926; caseControl 0.9011; cohortMethod 0.4350). Basis: source + execution (toy) + derived.

### 10. Test-suite adequacy at the pinned revisions

Basis: source + execution (toy) for the counter-examples.

- `EmpiricalCalibration/tests/testthat/test-EmpiricalCalibrationUsingAsymptotics.R:19-20`:
  ```r
    expect_equal(calibrateP(null, logRr, seLogRr), c(0.045500266, 0.002699796, NA), tolerance = 1e03)
    expect_equal(calibrateP(null, logRr, seLogRr, twoSided = FALSE), c(0.022750133, 0.001349898, NA), tolerance = 1e03)
  ```
  A relative tolerance of one thousand accepts almost any finite output, so these assertions are effectively vacuous.
- `tests/testthat/test-expected-systematic-error.R:6-12` ("computeExpectedAbsoluteSystematicError returns mean value") asserts `error == null["mean"]` with `tolerance = 1e-3` on the `sccs` negatives. The toy fit gives a relative gap of 5.5e−4 there, because μ/σ ≈ 2.8. By the same relative-difference criterion the assertion would narrowly fail on the shipped `caseControl` data (gap 1.08e−3) and clearly fail on `cohortMethod` (EASE 0.435 vs μ −0.046). The test therefore encodes a property of one data set, not of the function.
- `openEBGM/tests/testthat/testEBGM.R:29` compares 0.11.0's `Qn`, `ebgm`, and `quantBisect` against inline copies of the 0.9.1 functions at `theta <- c(1.23, 2.34, 1.4, 2.6, .1)`. Every element of that θ already satisfies the clamp (`α ∈ [β/2, 2β]`, bounds `[0.25, 10]`), so the regression check cannot detect the clamp's behavioural change. `testHypers.R:62-99` compares only squashed vs unsquashed fits and `nlminb` vs `nlm` vs BFGS (internal consistency). No test compares against externally published hyperparameters.
- `MethodEvaluation/tests/testthat/test-metrics.R:8-9`: `expect_equal(length(result), 7)` followed by `# TODO: need to check results (against gold-standard?)`.

### 11. Coverage of performance and resource levels (L1–L6)

Every cell is measured (with host stated), cited, derived, or `not measured`.

| Concept | L1 authoring/maintenance | L2 toolchain build | L3 compute latency | L4 runtime of produced artefact | L5 verification/checking speed | L6 memory/disk |
|---|---|---|---|---|---|---|
| openEBGM processing + GPS fit | Measured source size: 3,324 lines in `R/*.R` incl. roxygen (`wc -l`); person-months not measured | not measured (no R) | Cited: 321.83 s (zeros) vs 2.58 s (no zeros); 24.79 s vs 2.54 s unsquashed vs squashed (Canida–Ihrie 2017 §7.1). Cited: 8.59 s vs 0.53 s; `hyperEM` 4.03 s, 201 iterations (0.11.0 vignette). Measured toy port: processRaw 0.04 s, Nelder-Mead fit 3.4 s (x86_64 Linux workstation, Python) | known not to apply (no code generation); toy whole-pipeline run 8.1 s | not measured | Measured: `caers.rda` 88,360 bytes; 13,441 → 1,202 points (8.94%, also printed by the vignette); zero-filled table 2,967,536 cells (derived); peak RSS not measured |
| PhViD scores | Measured: 1,013 lines in `R/*.R` | not measured | not measured (R not run); toy all-rules run 12.8 s for 102,483 cells | known not to apply | not measured | Measured: `PhViDdata.frame.rda` 166,976 bytes |
| FAERS/AERS scale | not measured | — | not measured | — | — | Cited: 4,784,337 reports (Harpaz 2013); 1,398 × 952 cells, 4.9 M counts (DuMouchel 1999); 1.2 M non-zero pairs, 10.4 M counts (Szarfman 2002) |
| Empirical calibration | Measured: 3,684 lines in `R/*.R` (Plots.R alone 1,387) | not measured (Rcpp build not run) | Cited: MCMC default 100,000 iterations (source). Measured toy: all fits incl. leave-one-out 12.5 s | known not to apply | Cited qualitatively: "computationally expensive", 50 negative + 150 positive control estimates per study (Schuemie 2018) | not measured |
| Positive-control synthesis | Measured: 1,472 lines in `PositiveControlSynthesis.R` | not measured | not measured (requires an OMOP CDM database) | known not to apply | not measured | Cited: 5,482–26,097 candidate covariates per replication (Schuemie 2018) |

### 12. Comprehensibility and simplicity (C1–C2)

- **C1, PRR/ROR/IC.** Each needs about four quantities and one threshold. A reader can check them locally from a 2×2 table. The footgun is non-local: the margins depend on whether reports or pairs are counted (§4.1), and that is invisible in the formula. Shrinkage `log2((O+½)/(E+½))` keeps the Norén 2013 "back of an envelope" property; reported O and E make every score auditable.
- **C1, GPS.** It has five hyperparameters, four likelihood variants, three optimisers with acceptance heuristics, squashing, and a post-hoc clamp. The value of a printed EBGM cannot be recomputed from the printed θ̂ unless the reader also knows the clamp, which 0.11.0 applies silently (§3). That is a hidden, non-local dependency. Human comprehension was not measured empirically.
- **C1, calibration.** One Gaussian null (2 parameters) explains both p-value and CI calibration. Interpretability depends on knowing that Table 1 reports σ (§7), and that package defaults (linear SD) differ from the paper (log-linear SD).
- **C2, unifying abstraction.** All scores here are posterior or frequentist functionals of a Poisson rate ratio `O/E` given a baseline model. A single gamma prior `G(α1, α2)` (Norén 2013) subsumes the shrinkage IC, approximates the BCPNN IC, and is the one-component case of GPS. Empirical calibration then applies a second, orthogonal layer: an additive Gaussian bias on `log RR` that is estimated from controls. Several distinctions are realisation-medium accidents rather than semantics:
  - log2 vs ln (PhViD branches);
  - rounding to 2 decimals before thresholding (openEBGM);
  - per-component vs mixture truncation;
  - the hard clamp in place of a prior on θ.
  
  The minimal model refinement would be to state the scale and the hyperparameter regularisation explicitly in the model. Moving them into adapters is what hides them today.

### 13. Validation coverage (V1–V4)

| Level | What exists | Evidence |
|---|---|---|
| V1 spec adequacy and non-vacuity | Upstream tests are regression or self-consistency oracles, some vacuous (§10). This report adds differential re-implementation: Python ports reproduce the vignette numbers exactly (§3, §7, §8) and expose the clamp and Table 1 SD semantics. Mutation testing: not measured. | source + execution (toy) |
| V2 lowering/checker differential testing | Cross-implementation comparison PhViD vs openEBGM: margin counting and units differ (§4). Reference-set AUC studies act as end-to-end differential tests of methods, not of implementations (§5). No fuzzing found or run. | source + documentation |
| V3 concurrency/crash/physical | Known not to apply to the statistical semantics (single-process R; `data.table::setDTthreads(2)` only in tests and examples). Not examined. | source |
| V4 real-data falsification and human mental models | Negative controls are real-data falsification tests of a study design; synthetic positive controls preserve only measured confounding (Schuemie 2018). Duplicate-report review by national centres is real-world validation of record linkage (Tregunno 2014). Empirical studies of analysts' mental models of these scores: not examined. | documentation |

## Boundaries

- **Not examined: R execution.** No R package was run. openEBGM's `hyperEM`, `nlm`, and BFGS paths, PhViD's FDR/LBE rules, `fitMcmcNull`, the plotting functions, and the MaxSPRT/LLR calibration functions were read but not executed. They have no toy port either. The toy ports match the vignettes for the paths listed. Agreement elsewhere is not established.
- **Unknown: DuMouchel–Pregibon truncation.** It is unknown whether DuMouchel and Pregibon (2001) specify per-component or mixture-level truncation. Only the abstract (via an index) was available. The discrepancy in §2 is measured against openEBGM's own documentation, not against that paper.
- **Unsupported: fixing the truncation naively.** Replacing the per-component form with the mixture-level form drove the toy fit to a degenerate boundary (§3). The evidence does **not** show that openEBGM's hyperparameters are "wrong" in any operational sense, only that the likelihood is not the one its docs describe.
- **Not examined: openEBGM clamp rationale.** The clamp's purpose is documented only as "Helps prevent unusual shrinkage properties" (`R/f_helpers.R:19-20`). Whether it improves signal-detection accuracy against a reference set was not examined. The 24-vs-44 count is a change in the signal set, not a change in accuracy.
- **Not examined: full texts.** Ryan 2012, Ryan 2013 (both), Evans 2001, DuMouchel 1999, Bate 1998, Norén 2006, Norén 2007, Tregunno 2014, Szarfman 2002, and Hopstadius 2008 were examined through publisher or index abstracts only. Body-text numbers from these papers are absent.
- **Not examined: Hauben et al. 2007** ("Extreme duplication" in AERS, *Drug Saf* 30:551–4). It is a letter without an abstract and was not read.
- **Unknown: Yates correction in Evans 2001.** Whether Evans et al. applied a Yates correction is unknown; both readings are tabulated (§4.4).
- **Not examined: Norén 2013 approximation coefficients.** The coefficients of approximations (13)–(14) render as images in the retrieved text and are not reproduced.
- **Not measured: coverage values in Schuemie 2018 Figs. 1–4.** The coverage values in §8 come from the toy port on the shipped data. The shipped Southworth and Graham controls appear to match the paper's: the legacy-model refit equals the paper's Table 1 to its 2 printed decimals. They are not stated to be identical.
- **Not measured: duplicates and scores.** The effect of deduplication on PRR, IC, or EBGM values was not measured in any cited source available here, nor by this report.
- **Known not to apply.** The levels L4 (generated-code execution) and L5 (proof/certificate checking) have no artefact in these subjects. Calibration cost is the nearest analogue to L5 and is cited only qualitatively.
- **Unsupported (upstream).** Record linkage is not offered by any of the four packages. openEBGM deduplicates only identical report IDs.
- **Not examined: stratification consequences.** Hopstadius et al. 2008 report "spurious (and considerable) underestimation" of adjusted O/E ratios in the presence of very small strata. openEBGM only warns when a stratum has fewer than 50 IDs. Its practical effect was not measured beyond the CAERS `E`-ratio range (0.137–4.940).

## Evidence

Observation date for all upstream and literature evidence: 2026-11-20 (UTC).

**Repositories.** Each pin was resolved with the GitHub REST API (`gh api repos/<o>/<r>/commits/<sha>`) and equals that repository's HEAD on the observation date. Files were fetched from `raw.githubusercontent.com/<o>/<r>/<sha>/<path>`. Line numbers count physical lines after removing CR characters; the CRAN mirrors use CRLF.

- `cran/openEBGM@d731cb3ee8d5fe6013666e05b9e55e2494d51f25`: `DESCRIPTION`, `NEWS.md`, `R/f_transformInput.R`, `R/f_dataSquashing.R`, `R/f_hyperEstimation.R`, `R/f_EM_hyperEstimation.R`, `R/f_EM_updateTheta.R`, `R/f_EM_helpers.R`, `R/f_likelihoodEqs.R`, `R/f_posteriorCalcs.R`, `R/f_createObject.R`, `R/f_helpers.R`, `R/f_checkInputs.R`, `R/data_caers.R`, `tests/testthat/testEBGM.R`, `tests/testthat/testHypers.R`, `inst/doc/vignette03-hyperparameterEstimation.html`, `inst/doc/vignette04-posteriorCalculation.html`, `data/caers.rda`.
- `cran/PhViD@bbb450c3837c6001710a328d382a27e856e601d8`: `R/as.PhViD.R`, `R/PRR.R`, `R/ROR.R`, `R/BCPNN.R`, `R/GPS.R`, `man/PhViDdata.frame.Rd`, `data/PhViDdata.frame.rda`.
- `OHDSI/EmpiricalCalibration@03d4747fd805e92744d0bcaf603f4c2d0b13370b`: `NEWS.md`, `R/EmpiricalCalibrationUsingAsymptotics.R`, `R/EmpiricalCalibrationUsingMcmc.R`, `R/ConfidenceIntervalCalibration.R`, `R/ExpectedSystematicError.R`, `R/Likelihoods.R`, `R/Data.R`, `src/RcppWrapper.cpp`, `tests/testthat/*.R`, `inst/doc/EmpiricalPCalibrationVignette.pdf`, `inst/doc/EmpiricalCiCalibrationVignette.pdf` (text via `pdftotext -layout`), `data/{sccs,caseControl,cohortMethod,southworthReplication,grahamReplication}.rda`.
- `OHDSI/MethodEvaluation@d7305910f6c6a390a9e423ffc1685a97c017183e`: `R/PositiveControlSynthesis.R`, `R/SignalInjection.R`, `R/Metrics.R`, `R/MethodEvaluation.R`, `tests/testthat/test-metrics.R`, `data/{omopReferenceSet,euadrReferenceSet,ohdsiNegativeControls}.rda`.

**Literature.** Every DOI was checked twice. First, the doi.org handle API (`https://doi.org/api/handles/<doi>`) returned `responseCode 1` with a publisher URL. Second, OpenAlex (`api.openalex.org/works/doi:<doi>`) metadata confirmed title, authors, venue, volume, issue, and pages. Crossref's API was not reachable through the available web fetcher. Full text was read where PMC or the publisher served it:

| DOI | Work | Text used |
|---|---|---|
| 10.1007/s002280050466 | Bate et al. 1998, *Eur J Clin Pharmacol* 54(4):315–21 | abstract |
| 10.1080/00031305.1999.10474456 | DuMouchel 1999, *Am Stat* 53(3):177–90 | abstract (index) |
| 10.1002/pds.677 | Evans, Waller, Davis 2001, *Pharmacoepidemiol Drug Saf* 10(6):483–6 | abstract (index) |
| 10.1002/sim.5620 | Ryan et al. 2012, *Stat Med* 31(30):4401–15 | abstract (index) |
| 10.1177/0962280211403604 | Norén, Hopstadius, Bate 2013, *Stat Methods Med Res* 22(1):57–69 | full text (PMC6331976) |
| 10.1002/sim.5925 | Schuemie et al. 2014, *Stat Med* 33(2):209–18 | full text (PMC4285234) |
| 10.1007/s40264-014-0146-y | Tregunno et al. 2014, *Drug Saf* 37(4):249–58 | abstract |
| 10.32614/RJ-2017-063 | Canida, Ihrie 2017, *R J* 9(2) | full text |
| 10.1073/pnas.1708282114 | Schuemie et al. 2018, *PNAS* 115(11):2571–7 | full text (PMC5856503) |
| 10.1038/clpt.2013.24 | Harpaz et al. 2013, *Clin Pharmacol Ther* 93(6):539–46 | full text (PMC3857139) |
| 10.1007/s40264-013-0097-8 | Ryan et al. 2013, *Drug Saf* 36 S1:33–47 | abstract |
| 10.1007/s40264-013-0108-9 | Ryan et al. 2013, *Drug Saf* 36 S1:143–58 | abstract |
| 10.1002/sim.2473 | Norén et al. 2006, *Stat Med* 25(21):3740–57 | abstract (index) |
| 10.1007/s10618-006-0052-8 | Norén et al. 2007, *Data Min Knowl Disc* 14(3):305–28 | abstract |
| 10.1002/pds.668 | van Puijenbroek et al. 2002, *Pharmacoepidemiol Drug Saf* 11(1):3–10 | abstract (index) |
| 10.2165/00002018-200225060-00001 | Szarfman, Machado, O'Neill 2002, *Drug Saf* 25(6):381–92 | abstract |
| 10.2165/00002018-200831110-00008 | Hopstadius et al. 2008, *Drug Saf* 31(11):1035–48 | abstract |
| 10.1162/99608f92.147cc28e | Schuemie et al. 2020, *Harv Data Sci Rev* 2(1) | full text (PMC7755157) |

**Execution.** Host: x86_64 Linux workstation, Python 3.13 with numpy, no scipy, no R. The scripts, the input URLs and SHA-256 hashes, and the exact commands are in `support/README.md`. Outputs are in `support/outputs/`. `support/probes/rda_reader.py` is an independent R-serialization reader. Its counts are an execution of the data files' contents, not of R.

## Revalidation

1. **Clamp still present?** Diff `R/f_helpers.R` (`.reinInTheta`) and the `min_theta`/`max_theta` defaults in `R/f_posteriorCalcs.R` and `R/f_createObject.R` at the new revision. Then compare the new vignette04's printed `head(qn)`, `ebgm`, and suspicious count against `python3 support/probes/probe_openebgm.py caers.rda`. If the data or θ̂ changed, edit the θ̂ constant in the probe to match the new vignette.
2. **Truncation form.** Inspect `.negLL_logfstar` and `.negLLsquash_logfstar` in `R/f_likelihoodEqs.R`. If they divide by the mixture survival function instead, the §2 discrepancy is resolved. Rerun the probe's mixture-level fit to see whether it is still degenerate.
3. **Margins and units.** Check `R/as.PhViD.R` for `xtabs(n11 ~ .)` and `sum(n11)`, and `R/BCPNN.R` for `log(2)^(-1)` in the exact branch against `log(p11/(p1.* p.1))` in the Monte-Carlo branch. Check openEBGM `processRaw` for `.countUnique(id)`.
4. **Calibration defaults.** Check `legacy = FALSE` in `fitSystematicErrorModel` and the two `sd` formulas in `R/Likelihoods.R`. Rerun `probe_empirical_calibration.py`. Agreement with the vignette (`0.7922/0.2834/0.8389142`; `−0.0666/0.9333/0.1875/0.00298`) confirms that the ports still agree with the package.
5. **Tests.** Grep `tolerance = 1e03` in `test-EmpiricalCalibrationUsingAsymptotics.R`, the EASE-equals-mean assertion, `theta <- c(1.23, 2.34, 1.4, 2.6, .1)` in `testEBGM.R`, and the `TODO` in MethodEvaluation's `test-metrics.R`.
6. **Reference sets.** Rerun `probe_reference_sets.py` (row counts 399/93/200) and check the `@format` text in `R/MethodEvaluation.R`.
7. **Literature numbers** do not change. Revalidate only by re-reading the cited sections if a corrected version is published.
