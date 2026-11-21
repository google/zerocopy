# Thermal-process lethality for low-acid canned foods and predictive microbial growth: 21 CFR 113 process filing, general and formula methods, Weibull versus log-linear sterility, Baranyi growth, and what the open R packages bioinactivation and biogrowth actually compute

## Summary

- **The US regulation fixes inputs and accountability, not a numerical method.**
  - 21 CFR 108.35 requires a commercial processor to file each low-acid product and container size within 60 days of registration and before packing a new product. The filing covers processing method, retort type, minimum initial temperature, process time and temperature, "sterilizing value (Fo), or other equivalent scientific evidence", critical factors, and source and date. Filing "does not constitute approval".
  - 21 CFR 113.83 requires scheduled processes to be set by qualified persons using thermal-death-time data, heat-penetration calculations and inoculated packs as needed. "Calculation shall be performed according to procedures recognized by competent processing authorities."
  - Temperature-indicating devices must be accurate to 1 °F (0.5 °C) and checked against a NIST-traceable reference at least annually.

  Basis: normative.
- **That sensor tolerance alone moves F0 by about ±12%.** With z = 10 °C, a +0.5 °C bias multiplies every lethal rate by 10^0.05 = 1.122, and a −0.5 °C bias by 0.891 (−10.9%). A sampling interval of 5 min instead of ≤1 min changed F0 by +3% on a synthetic cold-spot history, and z = 8 or 12 °C changed it by −14% or +12%. Basis: derived + execution (toy history, not a real product).
- **Log-linear (first-order) inactivation is the exception in the evidence reviewed.**
  - van Boekel's 55 vegetative-cell case studies found Weibull shape β > 1 in 39 and β < 1 in 14, with β = 1 in only 2.
  - Mafart et al. found downward-concave spore curves for *B. cereus* and *B. pumilus* and upward concavity for *C. botulinum*, and showed that F values computed from a Weibull model "were no longer additive".
  - Anderson et al. found non-log-linear *C. botulinum* 213B survivor curves at every temperature between 101 and 121 °C.

  Basis: documentation (peer-reviewed abstracts).
- **Fitting a log-linear model to tailing data overstates lethality when extrapolated.** I generated synthetic Weibull data (p = 0.6) and fitted a Bigelow model with `bioinactivation`. Its 95% bands covered the true log reduction 0% of the time at short times, 84–91% inside the data, and 1.7% at twice the longest observed time. The fit predicted about 1.7 log *more* kill than truth there, which is the unsafe direction. A correctly specified Weibull fit covered 92–95%. Basis: execution (synthetic data through the real package).
- **`bioinactivation` 1.3.0 implements two incompatible dynamic Weibull semantics.**
  - Its Weibull–Mafart ODE uses elapsed clock time, `t^(p-1)`. Adding 30 minutes of 20 °C lead-in before an identical heat treatment changed the predicted reduction from 1.014 to 0.539 log when p = 0.5.
  - Its Peleg ODE is state-dependent and did not change.
  - For large reductions with p > 1, the Mafart prediction depends on the requested output times. Requesting only the endpoints returned **zero** inactivation for processes whose exact reduction is 9–77 log, and dense outputs still under-predicted beyond about 12 log.

  Basis: source + execution.
- **Growth models disagree under "the same" parameters, and units matter.**
  - With identical (logN0, logNmax, μ, λ), `biogrowth` 1.0.8 predicts 6.77 (Baranyi), 6.41 (modified Gompertz), 6.61 (logistic) and 6.80 (trilinear) log CFU at 20 h.
  - Reading μ = 0.4 as ln/h rather than the default log10/h gives 4.09 instead of 6.77.
  - A daily 7 ± 5 °C cycle grows to 4.29 log by 96 h against 2.67 at a constant 7 °C.
  - A misspecified Baranyi fit to Gompertz data covers the true time to a mid-curve level 95% of the time, but the true time to a near-asymptote level only 58% of the time.

  Basis: execution.

## Applicability

- **Regulation.** 21 CFR Part 113 (§§113.3, 113.40, 113.83, 113.87, 113.89) and 21 CFR 108.35, as rendered by the Legal Information Institute from the eCFR on 2026-11-21. eCFR.gov itself returned an automated-access challenge, which I did not attempt. Acidified foods (Part 114), aseptic-system specifics and other jurisdictions are out of scope.
- **Code.**
  - `albgarre/bioinactivation@3ca6bffa464897bebc233ef32f1bd79748ace674` (DESCRIPTION version 1.3.0) and `albgarre/biogrowth@63fabbdde5ccb76c94f60a4382d140f8cd5e1b69` (installed version 1.0.8), installed from those source trees.
  - Runtime: R 4.4.2 in the `rocker/r-ver:4.4.2` image, with CRAN deSolve 1.40, FME 1.3.6.3 and MASS 7.3-61.
  - Findings about ODE robustness depend on deSolve's default integrator settings as called by the package. I did not test them with other deSolve versions.
- **Relationship among subjects.** The regulation defines what must be filed and who decides. The papers supply the kinetic models and evidence. The two packages are open implementations of those models, examined as source and executed on package datasets and synthetic data. ComBase (Baranyi & Tamplin 2004) is described from its paper's abstract only; I did not query its database.
- **Toy models.** The general-method sensitivity probe uses an illustrative semi-logarithmic heating and cooling history. Its F0 value has no meaning for any product; only the relative changes are used.

## Findings

### 1. What a filed low-acid process must specify

Basis: normative (LII text of the CFR sections).

| Provision | Content |
|---|---|
| §113.3(n) low-acid food | Finished equilibrium pH > 4.6 and a_w > 0.85, other than alcoholic beverages. Tomatoes and tomato products with pH < 4.7 are excluded. |
| §113.3(e) commercial sterility | Heat renders the food free of microorganisms able to reproduce under normal non-refrigerated storage, and of viable microorganisms (including spores) of public-health significance. Alternatively, a_w control plus heat. |
| §113.3(r) scheduled process | "The process selected by the processor as adequate ... to achieve commercial sterility". It "shall be at least equivalent to the process established by a competent processing authority". |
| §113.3(f), (l), (c) | Critical factor (any parameter whose variation may affect the process); initial temperature (average of the coldest container at process start); come-up time. |
| §113.83 establishing | Qualified persons. Production variation must be "adequately provided for". Critical factors (e.g. minimum headspace, consistency, maximum fill-in or drained weight, a_w) must be specified. Methods include "microbial thermal death time data, process calculations based on product heat penetration data, and inoculated packs". Incubation tests should include containers from test trials and from "four or more actual commercial production runs". Records are retained permanently. |
| §113.40 instruments | Temperature-indicating device "accurate to 1 °F (0.5 °C)", tested against a NIST-traceable reference on installation and at least once a year. |
| §113.87(c) | Initial temperature determined and recorded often enough to ensure it is no lower than the scheduled minimum. |
| §113.89 deviations | Any process less than scheduled: fully reprocess, or set aside for evaluation by a competent processing authority. Destroy unless the evaluation shows freedom from microorganisms of public-health significance. Keep a deviation file. |
| §108.35(c) | Register on Form FDA 2541 within 10 days of starting. File each product and container size within 60 days of registration and before packing a new product, on Form 2541d (retorted), 2541f (water-activity or formulation control) or 2541g (aseptic). |

**Reading (derived).**
- The rule never names the general method, Ball's formula, z = 10 °C or a 12-log target.
- It delegates the algorithm to "procedures recognized by competent processing authorities" and requires F0 *or* "other equivalent scientific evidence".
- A software tool's output becomes regulatory evidence through a processing authority's judgement, not through any algorithm specified in the rule.

### 2. How lethality is computed

**Lethal rate and F value.** Basis: source, `bioinactivation/R/bigelow_model.R` lines 45–47 and `isothermal_models.R` lines 16–21.

- Bigelow's model is `D_T = D_R * 10^((temp_ref - temp)/z)` with `dN = -N*log(10)/D_T`.
- Under log-linearity, log10(N/N0) = −∫dt/D_T(T(t)) = −F_ref/D_ref, where F_ref = ∫10^((T − T_ref)/z) dt.
- With T_ref = 121.1 °C and z = 10 °C this is F0.
- Munir et al. 2023 state that the D121 °C for the most resistant *C. botulinum* spores "is 0.21 min in low-acid canned food and heating up to 3 min (botulinum cook) allows at least 12-log reductions". The derived figure 12 × 0.21 = 2.52 min is consistent with that. Basis: documentation (review article).

**General method.** This is numerical integration of the lethal rate over the measured cold-spot temperature history.
- Simpson, Almonacid & Teixeira 2003 extend it to compute process time or lethality "for process conditions different from those of the original heat-penetration tests".
- They tested the extension experimentally against Ball's formula method and finite-difference models. It "often safely predicted shorter process times than the Ball Formula Method by accurately accounting for slow come-up and cool-down phases".

Basis: documentation (abstract).

**Formula methods** (Ball and successors). These summarize the semi-log heating curve by a heating rate f_h, a lag factor j_h and the unaccomplished temperature difference g at steam-off. Lethality then comes from tables relating f_h/U to g.
- Smith & Tung 1982 compared five formula methods with a numerical general method on finite-difference conduction simulations.
- Deviations were "related to container dimensions and unaccomplished temperature difference (g), the largest errors occurring when g was large and the height-to-diameter ratio was close to unity".
- Errors were "mostly on the 'safe' side, but the energy use implications could be significant".

Basis: documentation (abstract). I did not compute the formula method itself.

**Numerical sensitivity of the general method.** Basis: execution of `support/probe_general_method_toy.py`, toy history with T_R = 121.1 °C, T_0 = 70 °C, j_h = 1.4, f_h = 40 min, 75 min of steam, cooling water at 20 °C. Basis for the bias and z rows: derived closed form, confirmed by the same execution.

| perturbation | ΔF0 |
|---|---|
| 0.5 min sampling, trapezoid | −0.03% |
| 1 min sampling | +0.03% |
| 2 min sampling | −0.42% |
| 5 min sampling | +2.96% |
| sensor +0.5 °C | +12.20% (= 10^0.05 − 1) |
| sensor −0.5 °C | −10.87% |
| z = 8 °C instead of 10 | −13.63% |
| z = 12 °C | +11.60% |
| share of F0 delivered after steam-off | 21.1% |

Left-rectangle and trapezoid rules coincide here because both ends of the history have near-zero lethal rate.

Reading:
- The tolerance §113.40 permits on the temperature sensor moves computed lethality more than any reasonable integration rule does.
- Cooling-phase lethality, which Simpson et al. account for and simple formula variants may not, is a fifth of the total in this toy.

### 3. Evidence against log-linear inactivation, and what changes

Basis: documentation (abstracts) unless marked.

- **Peleg & Cole 1998.**
  - "Some of the semilogarithmic survival curves, which have been considered linear are in fact slightly curved."
  - Curvature changes the thermal death time determined by extrapolation, "considerably smaller or larger depending on" concavity.
  - They reinterpret the survival curve as "the cumulative form of a temporal distribution of lethal events", with a Weibull distribution of resistances as a first approximation.
- **van Boekel 2002** (vegetative cells; spores excluded).
  - Across 55 case studies, log α (scale) depends linearly on temperature, and β (shape) depends on temperature in only 7.
  - β > 1 in 39, β < 1 in 14, β = 1 in 2: "the classical first-order kinetics approach is the exception rather than the rule".
  - "Large discrepancies can be found between the classical first-order approach and the Weibull model" in process calculations.
- **Mafart et al. 2002** (spores).
  - log10(N/N0) = −(t/δ)^p. The curves are downward-concave for *B. cereus* and *B. pumilus* and upward-concave for *C. botulinum*.
  - F values "were no longer additive", so "a heat treatment should be better characterized by the obtained decimal reduction".
  - They propose a modified Bigelow method.
- **Anderson et al. 1996.** *C. botulinum* 213B survivor curves between 101 and 121 °C "deviated from log-linearity" at all temperatures and were fitted with a log-logistic model. The implications for the "minimum botulinum cook" are discussed.
- **Smelt & Brul 2014** is a general review. The abstract states no model preference.

**Process consequence on real example data.** Basis: execution, `support/probe_bioinactivation.R` part B, dataset `isothermal_inactivation` shipped with the package.

- The package documents the dataset only as an "Example ... of a microorganism" with no source. Its `@format` line says 36 rows (`R/doc_examples.R` line 34), but the loaded data has 68 rows at 95–107 °C.
- Fits:

  | model | parameters (±SE) | RSS | AIC |
  |---|---|---|---|
  | Bigelow | z = 7.760 ± 0.244 °C; D(100 °C) = 2.980 ± 0.142 min | 15.22 | −97.81 |
  | Weibull–Mafart | δ = 2.759 ± 0.224 min; z = 7.629 ± 0.285; p = 0.930 ± 0.058 | 14.89 | −97.26 |

  AIC marginally prefers the log-linear model, and p is within about 1.2 SE of 1.
- Even so, the isothermal time at 100 °C for n log reductions differs between fits:

  | n | Weibull/Bigelow time ratio |
  |---|---|
  | 1 | 0.926 |
  | 3 | 1.006 |
  | 6 | 1.060 |
  | 12 | 1.117 |

  For a reference profile (80 → 100 °C in 5 min, 10 min hold, 100 → 80 °C in 5 min), the fits predict 3.919 vs 3.646 log reductions.
- Reading: model choice is statistically invisible inside the data but changes a 12-decade process time by about 12%.

**Misspecification coverage.** Basis: execution, `probe_bioinactivation.R` part C.

- Design: truth is Weibull–Mafart with δ = 2 min at 70 °C, z = 7, p = 0.6. Observations are 3 temperatures (66/70/74 °C) × 6 times (0.5–8 min) with N(0, 0.3²) noise on log10. There were 300 replicates. Each was fitted by `fit_isothermal_inactivation` (nls), with 95% bands from 2,000 draws of the nls covariance.
- Results:

  | t at 70 °C (min) | true log10 S | Bigelow-fit coverage | Bigelow mean bias (log) | Weibull-fit coverage |
  |---|---|---|---|---|
  | 0.25 | −0.287 | 0.000 | +0.207 | 0.940 |
  | 1 | −0.660 | 0.000 | +0.338 | 0.930 |
  | 4 | −1.516 | 0.913 | +0.228 | 0.923 |
  | 8 | −2.297 | 0.843 | −0.278 | 0.947 |
  | 16 (extrapolated) | −3.482 | 0.017 | −1.669 | 0.930 |

- A negative bias means more predicted kill than truth. **For upward-concave (tailing) data, the log-linear extrapolation is anti-conservative.** The reported uncertainty does not reveal this, because nls standard errors are conditional on the model being correct.

### 4. Dynamic-temperature semantics in `bioinactivation`

Basis: source.

| model | ODE right-hand side (file, lines) | state | depends on |
|---|---|---|---|
| Bigelow | `dN <- - N * log(10)/D_T` (`bigelow_model.R` 45–47) | N | T(t) |
| Weibull–Mafart | `dN <- - N * p * (1/delta)^p * t^(p-1) * log(10)`, `delta <- delta_ref * 10^( -(temp-temp_ref)/z)` (`weibull-mafart_model.R` 51–52) | N | T(t) **and clock time t** |
| Weibull–Peleg | `b <- log( 1 + exp( k_b*(temp - temp_crit) ) )`; `dlogS <- -b * n * ( - logS/b ) ^( (n-1)/n)` (`weibull-peleg_model.R` 53–55) | log S | T(t) and current log S |

`predict_inactivation` (`make_predictions.R`) proceeds as follows:
- replaces times below `tol0 = 1e-5` by `tol0` (line 109);
- starts N-state models at `N = parms[["N0"]]` (lines 118–120) and log S models at `logS = -1e-6` (lines 127–129);
- calls `ode(y = xstart, times = sort(times), func = model_data$ode, parms = parms, temp_profile = ..., ...)` (lines 144–147), passing the user's `...` to deSolve.

Parameter estimation uses `nls` for isothermal data (`isothermal_fit.R` lines 95–97), and `FME::modFit` for dynamic data after shifting t = 0 to `tol0` (`dynamic_fit.R` lines 107–111). Garre et al. 2017 report that their MCMC fitting "produces a better characterization of the biological uncertainty and variability than non-linear regression". Basis: documentation.

**Time-origin dependence.** Basis: execution, `probe_bioinactivation.R` part A, cross-checked by fine Riemann sums in `probe_mafart_dense_output.R`.

- The treatment is 20 → 70 °C in 10 min, 5 min at 70 °C, then cooling to 30 °C. It is applied either at t = 0 or after 30 min at 20 °C.

| model | no lead-in | with lead-in | Δ |
|---|---|---|---|
| Bigelow (D70 = 1 min, z = 7) | −5.9880 | −5.9880 | 0 |
| Mafart p = 1 | −5.9880 | −5.9880 | 0 |
| Mafart p = 0.5 | −1.0138 | −0.5389 | +0.4749 |
| Peleg n = 0.5 | −7.6417 | −7.6417 | 0 |

- The Riemann sums of the Mafart rate law give −1.0138 and −0.5389, so the difference is the formulation's, not a numerical error.
- The Mafart dynamic form treats elapsed time since t = 0 as the "age" of the population. Any lead-in, come-up or hold before heating reduces (p < 1) or increases (p > 1) the computed kill.
- The Peleg form is time-shift invariant. With n = 1.5 it differed by −0.061 out of −67.8 log; I did not establish whether this comes from the log-logistic b(T) being non-zero at 20 °C or from integrator tolerance.

**Sparse-output failure for large reductions.** Basis: execution, `support/probe_bioinactivation_numerics.R`, default deSolve settings.

| process (70 °C hold) | exact (Riemann) | endpoints only | 101 output times | endpoints + `hmax = 0.05` |
|---|---|---|---|---|
| Mafart p = 1.5, 1 min | −9.320 | **0.000** | −9.320 | −9.320 |
| 3 min | −19.925 | **0.000** | −15.769 | −19.097 |
| 6 min | −37.348 | **0.000** | −20.791 | −32.446 |
| 12 min | −77.055 | **0.000** | −29.930 | −62.058 |
| Bigelow, 12 min | −13.368 | −13.383 | −13.361 | −13.371 |

- With dense output, the Mafart log S became NaN (negative N) at 13–14 min and then *rose* to −14.1 at 20 min, against an exact −29.84 (`probe_mafart_dense_output.out`).
- Hypothesis, not established:
  - integrating N on a linear scale from N0 = 10⁶ leaves no relative accuracy once N falls below the solver's absolute tolerance;
  - when the initial derivative is ≈ 0 (t^(p−1) → 0 for p > 1 and cold start), the step-size controller can step over the heating window when only endpoints are requested.
- `hmax` passed through `...` mitigates but does not fix this.
- These are robustness limits for sterilization-scale reductions (≥ 12 log). They are not a claim that the package's equations are wrong.

### 5. Growth models, data and tools

- **Baranyi & Roberts 1994.** A single variable represents physiological state. "The product of the lag parameter and the maximum specific growth rate is a simple transformation of the initial physiological state". Assuming μ "follows the environmental changes instantaneously", the model extends to time-varying temperature, pH and a_w. Basis: documentation.
- **`biogrowth` implementation.** Basis: source.
  - Isothermal Baranyi (`predict_isothermal_growth.R` lines 28–30): `num <- 1 + exp(log(10)*mu*(times - lambda)) - exp(-log(10)*mu*lambda)`, `den <- exp(log(10)*mu*(times-lambda)) - exp(-log(10)*mu*lambda) + 10^(logNmax - logN0)`, `logN <- logNmax + log10(num/den)`.
  - μ is therefore in log10 units. The public functions default `logbase_mu = logbase_logN` = 10 (`top_predict.R` line 182; conversion at `predict_isothermal_growth.R` line 269).
  - The docstring of the non-exported function `iso_Baranyi` (line 11) still says "Maximum specific growth rate (in ln CFU/[t])". The exported path converts correctly, so this is a documentation inconsistency, not a computational error.
  - Dynamic Baranyi (`baranyi_model.R` lines 25–36): `alpha <- Q/(1+Q)`, `beta <- 1 - N/Nmax`, `mu <- mu_opt*prod(gamma)*log(10)`, `dN <- alpha*mu*beta*N`, `dQ <- mu*Q`. The stationary-phase curvature is fixed at the logistic form.
  - The secondary cardinal model `CPM_model` (`gamma_models.R` lines 14–24) sets γ = 0 outside [xmin, xmax].
  - Asymptotic covariance for isothermal fits is `solve(0.5*hessian) * ssr/df` (`FitIsoGrowth_class.R` lines 146–165).
- **Same inputs, different tools.** Basis: execution, `support/probe_biogrowth.R`. Parameters: logN0 = 2, logNmax = 8 (C = 6), μ = 0.4 log10/h, λ = 8 h.

  | t (h) | Baranyi | mod. Gompertz | Logistic | Trilinear |
  |---|---|---|---|---|
  | 0 | 2.000 | 2.000 | 2.095 | 2.0 |
  | 10 | 2.864 | 2.905 | 3.125 | 2.8 |
  | 20 | 6.773 | 6.405 | 6.611 | 6.8 |
  | 30 | 7.999 | 7.705 | 7.877 | 8.0 |

  - The time to reach 5 log is 15.50–15.54 h for all four, because the parameters are defined through the tangent at maximum slope.
  - They diverge near the asymptote.
  - The reparameterized logistic does not pass through logN0 at t = 0.
  - μ = 0.4 read as ln/h (`logbase_mu = exp(1)`) gives 4.088 instead of 6.773 at 20 h.
- **Dynamic vs mean temperature.** Basis: execution. Baranyi + CPM(T_min 2, T_opt 35, T_max 40 °C, n = 2), μ_opt = 1.2 log10/h, Q0 = 10⁻³, N0 = 10², 7 ± 5 °C daily sinusoid.

  | time (h) | sinusoid | constant 7 °C |
  |---|---|---|
  | 48 | 2.158 | 2.025 |
  | 96 | 4.285 | 2.665 |

  Because γ(T) is convex at low temperature, a mean-temperature shortcut under-predicts growth.
- **Misspecification.** Basis: execution. Truth is modified Gompertz (logN0 = 2, C = 6, μ = 0.4, λ = 8). There are 13 observations over 0–48 h with N(0, 0.25²) noise, and 150 replicates. Fits used `fit_growth(..., algorithm = "regression")`, with intervals from 1,000 draws of `vcov()`.

  | target | true t (h) | Baranyi fit: coverage, mean estimate | Gompertz fit: coverage, mean estimate |
  |---|---|---|---|
  | log10 N = 4 | 13.00 | 0.947, 13.06 | 0.907, 13.05 |
  | log10 N = 7.5 | 26.99 | 0.580, 24.57 | 0.887, 27.23 |

  - Here the misspecified model errs early, which is conservative for shelf life.
  - Even the correct model's asymptotic intervals under-cover the nominal 95% with 13 points.
- **Data and tools.**
  - ComBase collects "observations of bacterial responses to food environments", obtained "from cooperating research institutes and from the literature", and made "publicly available via the Internet" (Baranyi & Tamplin 2004).
  - Tenenhaus-Aziza & Ellouze 2015 compare 16 tools on modeling approach, modules (databases, predictors, fitting, risk assessment), environmental factors, media and organisms.
  - The biogrowth paper (Garre et al. 2023) emphasises static and dynamic environments with an arbitrary number of factors, and fixing parameters before fitting "to mitigate identifiability issues".
  - Zwietering et al. 1990 found the modified Gompertz "statistically sufficient" for *L. plantarum*.

  Basis: documentation.

### 6. Performance and resource footprint

| level | value | basis |
|---|---|---|
| L1 authoring velocity | not measured | — |
| L2 build | Installing both packages from source plus CRAN dependencies took about 73 s wall (single run on a 96-vCPU Xeon host, including binary downloads) | execution (task timestamps) |
| L3 latency | `probe_bioinactivation.R`: 4.4 s total, including 600 nls fits and 1.2 M covariance draws. `probe_biogrowth.R`: 130.6 s for 600 regression fits plus root-finding on 1,000 draws each. Single `predict_inactivation` calls: not separately timed | execution |
| L4 run time of computed processes | not measured | — |
| L5 checking | no certificate artefacts in this domain; not applicable | — |
| L6 memory | not measured (container RSS not recorded) | — |

### 7. Comprehensibility, simplicity and validation

- **C1 (human comprehension).** A process engineer juggles D, z, T_ref, F0, f_h, j_h, g and come-up time. A microbiologist adds δ and p (Mafart), b and n (Peleg), μ (in which log base?), λ, Q0, and the secondary-model cardinal values. Three hidden choices change answers without changing parameter names:
  1. time-dependent vs state-dependent dynamic Weibull (§4);
  2. ln vs log10 growth rate (§5);
  3. the geometric definition of λ and μ that makes primary models agree mid-curve but not at the asymptote.
- **C2 (simplicity).** The universal abstraction is an autonomous ODE on log count, d log N/dt = r(log N, T, environment). It covers first-order kill, state-dependent Weibull, Baranyi growth (with the extra Q state) and cardinal secondary models. It is time-shift invariant, so lead-ins, holds and dynamic profiles become ordinary cases. Under it, F0 additivity is a property of the first-order special case. Log reduction, as Mafart et al. recommend, is the quantity that composes. The time-dependent Mafart ODE is the exception that this abstraction rules out.
- **V1 (specification adequacy).**
  - The rule's end-to-end checks are inoculated packs and incubation of containers from four or more production runs (§113.83).
  - The misspecification probes (§§3, 5) show that within-model standard errors do not validate the model form.
- **V2 (differential testing).**
  - Comparing package ODE output with independent quadrature exposed the sparse-output failure (§4).
  - The literature cross-checks formula methods against numerical general methods and finite-difference models (Smith & Tung 1982; Simpson et al. 2003).
- **V3 (concurrency, crash, silicon).** Not applicable; not examined.
- **V4 (physical validation).**
  - The rule requires NIST-traceable temperature sensors, recorded initial temperatures and documented deviations (§§113.40, 113.87, 113.89).
  - Smelt & Brul highlight biological time–temperature indicators for process calculations.
  - None of these validate the kinetic model itself.

## Boundaries

- **Not examined:**
  - **Primary texts.**
    - The eCFR rendering, which was behind an automated-access challenge, and FDA guidance on Forms 2541d/f/g.
    - Ball's original papers and f_h/U–g tables, Stumbo's tables, and Stoforos et al. 1997 (bibliographic only, 10.1080/10408399709527782). The formula method was **not computed**.
    - Esty & Meyer 1922 (10.1093/infdis/31.6.650) and Bigelow 1921 (10.1093/infdis/29.5.528), whose full texts were not read. The 0.21 min D-value is taken from Munir et al. 2023.
  - **Data and tools not run.**
    - Published *C. botulinum* survival data. The fits in §3 use the package's own undocumented example dataset.
    - The ComBase database, DMFit, IPMP 2013 (Huang 2014, 10.1016/j.ijfoodmicro.2013.11.019), GInaFiT (Geeraerd et al. 2005, 10.1016/j.ijfoodmicro.2004.11.038) and Bioinactivation FE (10.1016/j.foodres.2018.06.057). None of these were executed, so "where tools disagree" is shown only within `biogrowth` and `bioinactivation`.
  - **Package features.**
    - MCMC fitting in either package (`fit_inactivation_MCMC`, `fit_growth(algorithm = "MCMC")`), and therefore how MCMC intervals behave under misspecification.
    - The Geeraerd, Metselaar and Arrhenius models in `bioinactivation`.
    - deSolve versions other than 1.40, and non-default `ode` methods.
- **Unknown:**
  - The mechanism of the sparse-output failure (§4 gives a hypothesis).
  - The cause of the −0.061 log Peleg n = 1.5 lead-in difference.
  - The provenance of `isothermal_inactivation`.
- **Known not to apply:**
  - F-value additivity does not hold for Weibull kinetics (Mafart et al.).
  - Time-shift invariance does not hold for the `bioinactivation` Mafart dynamic model.
  - The general-method toy numbers are not properties of any real container or product.
- **Unsupported:** `bioinactivation` offers no log-scale state for the Bigelow, Mafart or Metselaar ODEs at this revision; they integrate N.
- **Attractive but unestablished conclusions:**
  - "Weibull always requires longer processes." Direction depends on p and on the extrapolation range: the ratio was 0.926 at 1 log and 1.117 at 12 log.
  - "Regulators require F0 = 3 min." The rule requires F0 *or* equivalent evidence from a competent authority. The 3-minute botulinum cook is a convention reported in the literature, not a rule text.

## Evidence

All evidence was acquired on 2026-11-21 (UTC).

- **Regulation.** LII pages for 21 CFR 113.3, 113.40, 113.83 (amended 76 FR 11922, 3 March 2011), 113.87, 113.89 and 108.35.
- **Source** at `albgarre/bioinactivation@3ca6bffa464897bebc233ef32f1bd79748ace674`:
  - `R/bigelow_model.R` 39–53;
  - `R/isothermal_models.R` 16–44, 61–67;
  - `R/weibull-mafart_model.R` 46–58;
  - `R/weibull-peleg_model.R` 53–55;
  - `R/make_predictions.R` 89–175;
  - `R/isothermal_fit.R` 95–97;
  - `R/dynamic_fit.R` 107–111;
  - `R/doc_examples.R` 19–35;
  - `R/function_mapping.R` 43–105.
- **Source** at `albgarre/biogrowth@63fabbdde5ccb76c94f60a4382d140f8cd5e1b69`:
  - `R/predict_isothermal_growth.R` 1–31, 103–110, 125–150, 252–275;
  - `R/baranyi_model.R` 25–36;
  - `R/gamma_models.R` 14–24;
  - `R/top_predict.R` 175–184;
  - `R/top_fit.R` 354–367;
  - `R/FitIsoGrowth_class.R` 142–166.
- **Execution.** All scripts and raw outputs are in `support/`.
  - `install_r_packages.R` (environment);
  - `probe_bioinactivation.R` → `.out` (§§3, 4);
  - `probe_bioinactivation_numerics.R` → `.out` and `probe_mafart_dense_output.R` → `.out` (§4);
  - `probe_biogrowth.R` → `.out` (§5);
  - `probe_general_method_toy.py` → `.out` (§2; Python 3.13, NumPy 2.5.4).
  - Random seeds are fixed in each script.
- **Literature** (DOIs verified against Crossref metadata; abstracts read via PubMed or the publisher):
  - Mafart et al. 2002, 10.1016/S0168-1605(01)00624-9;
  - van Boekel 2002, 10.1016/S0168-1605(01)00742-5;
  - Peleg & Cole 1998, 10.1080/10408699891274246;
  - Anderson et al. 1996, 10.1111/j.1365-2672.1996.tb03221.x;
  - Smelt & Brul 2014, 10.1080/10408398.2011.637645;
  - Simpson et al. 2003, 10.1111/j.1365-2621.2003.tb09646.x;
  - Smith & Tung 1982, 10.1111/j.1365-2621.1982.tb10137.x;
  - Baranyi & Roberts 1994, 10.1016/0168-1605(94)90157-0;
  - Baranyi & Tamplin 2004, 10.4315/0362-028X-67.9.1967;
  - Zwietering et al. 1990, 10.1128/aem.56.6.1875-1881.1990;
  - Tenenhaus-Aziza & Ellouze 2015, 10.1016/j.fm.2014.06.026;
  - Garre et al. 2017, 10.1016/j.foodres.2017.01.012;
  - Garre et al. 2023, 10.18637/jss.v107.i01 (journal page abstract);
  - Munir et al. 2023, 10.3390/foods12081580 (full text, PMC).
  - Holdsworth & Simpson, *Thermal Processing of Packaged Foods*, 10.1007/978-3-319-24904-9: bibliographic only.

## Revalidation

1. **Regulation.** Re-read §§113.3(r), 113.40 accuracy, 113.83 and 108.35(c)(2) on the current eCFR, through its API or a browser. Check for amendments after 76 FR 11922.
2. **Dynamic-Weibull semantics.** Grep `R/weibull-mafart_model.R` for `t^(p-1)`. If it is replaced by a state-dependent form, rerun `probe_bioinactivation.R` part A: Mafart p = 0.5 should then give Δ = 0.
3. **Sparse-output failure.** Rerun `probe_bioinactivation_numerics.R` with the new package and deSolve versions. The discriminating cell is "Mafart p = 1.5, 1 min, endpoints only": `0.000` reproduces the failure, and `−9.320` means it is fixed. Also check `make_predictions.R` for a change of state variable to log N.
4. **Units and model disagreement.** Rerun `probe_biogrowth.R` part A/B. The four-model table and the ln-versus-log10 row should match `probe_biogrowth.out` unless the primary-model equations at `predict_isothermal_growth.R` lines 28–30, 107–109 and 148 change.
5. **Misspecification.** The coverage figures are Monte Carlo estimates (300 and 150 replicates). Expect ±0.03–0.04 sampling variation on rerun with a different seed. The qualitative pattern (≈0 coverage at extrapolated or early points for the log-linear fit; ≈0.58 near the growth asymptote) is the discriminating result.
