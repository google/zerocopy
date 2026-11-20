# Benchmark-dose estimation, model averaging and reference-dose derivation: U.S. EPA BMDS 25.2, EFSA 2022 Bayesian averaging and PROAST, probabilistic uncertainty factors, and httk steady-state reverse dosimetry

## Summary

- **Benchmark dose (BMD) = the dose producing a predefined benchmark response (BMR); the point of departure is a one-sided lower bound (BMDL).** Crump (1984) introduced it as "a statistical lower confidence limit to a dose producing some predetermined increase in response rate such as 0.01 or 0.1". Both U.S. EPA (2012) and EFSA (2022) use a one-sided 95% lower bound; EFSA 2022 moves from frequentist confidence bounds to Bayesian credible bounds and reports the BMDU/BMDL ratio as the precision measure. Basis: normative + documentation.
- **Where the regimes diverge on the same data (derived from guidance and source):** (1) continuous BMR — BMDS defaults to a 1 SD change (`bmr_type = StandardDeviation`, `bmr = 1.0`), EPA (2012) recommends 1 SD for cross-chemical comparison, EFSA (2022) uses a tiered, biologically-relevant BMR and its worked examples use PROAST's 5% default; (2) model set — BMDS continuous Linear/Polynomial/Power/Hill/Exponential M3/M5 versus EFSA's single set of eight four-parameter models (Exponential, Inverse Exponential, Hill, Log-Normal, Gamma, LMS two-stage, Probit, Logistic) for both quantal and continuous data; (3) selection versus averaging — the BMDS recommender picks one model (lowest AIC if viable BMDLs are within a factor of 3, else lowest BMDL), EFSA prefers Bayesian model averaging with Laplace-approximated weights; (4) shape constraints — BMDS "restricted" bounds (e.g., power ≥ 1) versus EFSA priors. Basis: source + normative.
- **Apparent defect in BMDS 25.2 model averaging (source-level, not executed in BMDS):** the Laplace log-evidence term is written `res->models[i]->nparms / 2 * log(2 * M_PI)` with `int nparms` (`src/bmdscore/dichotomous_entry_code.cpp:612`, `bmdStruct.h:109`). Integer division drops 0.5·ln(2π) ≈ 0.9189 from every odd-parameter model, multiplying its unnormalized posterior weight by (2π)^−½ ≈ 0.3989. Five of the nine default dichotomous Bayesian models have three parameters; if the intended weights were all 1/9, the computed weights put 0.333 instead of 0.556 of the mass on three-parameter models. The same codebase writes the term with `/ 2.0` in its single-model `BIC_equiv` (`bmds_helper.cpp:1148`). Basis: source + execution (expression-semantics probe) + derived.
- **Reference dose = POD ÷ product of uncertainty factors.** Treating each 10-fold factor as an upper percentile and multiplying them compounds conservatism: in a toy where each of two independent lognormal factors has median 1 and 95th percentile 10, the 95th percentile of the product is 25.95, not 100. Probabilistic frameworks (Chiu & Slob 2015; Chiu et al. 2018) replace the RfD with a target human dose HD^I_M; across 1,464 RfDs for 608 chemicals, traditional RfDs were "generally within an order of magnitude" of the HD^I_M lower bound for I = 1%, and exposure at the RfD "frequently implies an upper 95% confidence bound of several percent of the population affected." Basis: execution (toy) + documentation.
- **httk reverse dosimetry is a closed-form steady-state ratio.** The default `calc_mc_css` model (`3compartmentss`) computes `Css = dose_rate × Fabsgut × Fhep / (Qgfr × Fup + CLh)` with well-stirred `CLh = Qliver·Fup·Clint/(Qliver + Fup·Clint)`, takes the 95th percentile over 1,000 Monte Carlo draws (NHANES-resampled physiology plus in-vitro measurement uncertainty), and returns oral equivalent dose = concentration ÷ Css95. In-vivo evaluations report weak chemical-to-chemical agreement (R² ≈ 0.34 for Css; about 65% of chemicals within ≈3.2-fold, the rest mostly overestimated) and ineffective bioavailability prediction for non-pharmaceuticals. Basis: source + documentation.

## Applicability

**Subjects and relationships.** `USEPA/BMDS` at `0018abea713f61b0bcc9dd30821af18b61a77e77` (default-branch HEAD on 2026-11-20; tags `25.2` and `25.2p1` point here; tags `26.1`, `26.1a3`–`26.1a5` exist on other commits and were not examined) is the U.S. reference implementation; the EPA 2012 guidance is the U.S. normative text it implements in part. EFSA (2022) is the European normative text; PROAST (RIVM) and the EFSA web application implement it, but PROAST is distributed as an R package archive (`proast71.1.zip` on the access date), not from a public version-control repository, so it was examined only through EFSA's descriptions and worked examples. `USEPA/CompTox-ExpoCast-httk` at `f6605eebc6eb5a483a8824dce6cbddb36c8fb091` (`httk` 2.7.4) is examined against Wetmore et al. (2012), Pearce et al. (2017) and the in-vivo evaluations of Wambaugh et al. (2015, 2018, 2019). Chiu & Slob (2015) and Chiu et al. (2018) represent probabilistic RfD replacement; the National Research Council (2009) recommendation is known here only through Chiu et al.'s characterization.

**Configuration scope.** BMDS findings concern pybmds sessions built with `Session.add_default_models` (frequentist) or `add_default_bayesian_models` (Bayesian, which adds model averaging only for dichotomous datasets) and the bmdscore Laplace routines they call. The integer-division finding applies to `estimate_ma_laplace` (dichotomous, reached from pybmds), the dichotomous MCMC averaging routine (line 472), and two continuous averaging routines in `continuous_entry_code.cpp` (lines 1254, 1893); pybmds 25.2 exposes no continuous model averaging, so only the dichotomous path was traced end to end. httk findings concern the `3compartmentss` steady-state path and the default Monte Carlo settings; PBTK ODE solutions (`solve_pbtk.R`) were read only for orientation.

**What was not run.** BMDS was not built or executed (Eigen and GSL headers were absent and no Python package installer was available on the observation host), PROAST was not run, and httk was not run (no R). Numeric claims about those systems come from source reading, published results, or explicitly labelled toy arithmetic.

## Findings

### 1. Definitions and defaults

| Item | EPA 2012 guidance | BMDS 25.2 (pybmds) | EFSA 2022 |
|---|---|---|---|
| Quantal BMR | 10% extra risk "for standard reporting… Note that this is not a default BMR" | `bmr = 0.1`, `bmr_type = ExtraRisk`, `alpha = 0.05` (`types/dichotomous.py` 36–38) | extra risk preferred; BMDL10 "might in many cases be appropriate"; deviations documented |
| Continuous BMR | 1 SD change recommended for comparisons across BMDs; biologically significant change preferred when known | `bmr_type = StandardDeviation`, `bmr = 1.0` (`types/continuous.py` 47–49); also Absolute, Relative, Point, Hybrid-Extra, Hybrid-Added | tiered: established BMR → biologically relevant BMR (EKE, effect-size theory, 1 SD, hybrid…); otherwise the endpoint "should not be used to establish a HBGV" |
| Bound | one-sided 95% lower confidence limit (BMDL); profile likelihood in worked examples | Bayesian/averaged: `alpha` quantile of the BMD posterior or mixture (`bmds_helper.cpp` 199–201); profile-likelihood routines exist (`bmd_calculate.h` 340, 628) but the frequentist call path was not traced | BMDL/BMDU = 5th/95th percentiles of the posterior (two-sided 90% credible interval) |
| Model use | single model; lowest AIC when BMDLs "sufficiently close (given the needs of the assessment)", else lowest BMDL; model averaging "being considered" | recommender: lowest AIC if max/min viable BMDL ≤ `sufficiently_close_bmdl = 3`, else lowest BMDL (`recommender.py` 180–188; `default.json`) | Bayesian model averaging "recommended as the preferred method"; uniform prior over models by default |
| Goodness of fit | α = 0.1 for the global test | `gof` threshold 0.1 → "questionable" bin | fit judged against full and null models |

Basis: normative (EPA, EFSA) + source (BMDS). The factor 3 in BMDS is an implementation default; the 2012 guidance text leaves "sufficiently close" to the assessment (string "factor of 3" does not occur in the extracted guidance text). Basis: source + derived.

**Model sets and constraints.** pybmds default dichotomous models (`session.py` 50–60): Logistic, LogLogistic, Probit, LogProbit, QuantalLinear, Multistage, Gamma, Weibull, DichotomousHill; continuous: Linear, Polynomial, Power, Hill, ExponentialM3, ExponentialM5. Default frequentist prior class is *restricted* except Logistic, Probit, LogProbit and QuantalLinear, which default to *unrestricted* (`models/dichotomous.py` 76–77, 120–121, 142–143, 155–156, 177–178). Restricted bounds in `types/priors.csv` (prior_class 1) include LogLogistic slope b ∈ [1, 18], Gamma shape a ∈ [1, 18], Weibull power a ∈ [1, 18], Hill b ∈ [1, 18] and Multistage coefficients ≥ 0. Bayesian priors (prior_class 2; type 1 = normal, 2 = lognormal) include LogLogistic b ~ lognormal(ln 2 = 0.693147, 0.5) on [0, 20], Weibull a ~ lognormal(0.424264, 0.5) on [0, 40], Gamma a ~ lognormal(0.693147, 0.424264) on [0.2, 20]. EFSA's eight models are all four-parameter, monotone, positive and asymptotic (properties P1–P4); for quantal data each has three parameters and "all models are non-nested"; latent-variable models were dropped as unnecessary. Basis: source + normative.

**Why restrictions exist.** EPA (2012) warns that unrestricted power parameters can give models "improbably steep in the low-dose region", while noting that excluding powers < 1 may not fit supralinear data. Restricted bounds (BMDS frequentist) and informative lognormal priors centred above 1 (BMDS Bayesian; EFSA) are two mechanisms for the same invariant — bounded low-dose slope. Basis: normative + derived.

### 2. Model averaging in BMDS 25.2: call chain, algorithm, defect

Call chain (Basis: source): pybmds `DichotomousModelAverage.execute` (`types/ma.py` 57–58) → `pythonBMDSDichoMA` (`bmds_helper.cpp` 2422; calls `runBMDSDichoMA` at 2464) → `runBMDSDichoMA` (1242–1256; calls `estimate_ma_laplace_dicho` at 1250) → `estimate_ma_laplace_dicho` (`dichotomous_entry_code.cpp` 803–807) → `estimate_ma_laplace` (582–719).

Algorithm of `estimate_ma_laplace`:
1. Fit each model by MAP on doses scaled to `[0, 1]` (`D = (1/max_dose) * D`, line 300), in an OpenMP loop over models (585–602).
2. Log-evidence per model (612–613), then subtract the maximum and add `log(MA->modelPriors[i])` (653), exponentiate and normalize (650–660).
3. Zero the weight of any model whose BMD CDF contains NaN, renormalize (658–676).
4. Build the averaged BMD CDF on a uniform 200-point grid from 0 to `range[1]` (`dist_numE = 200`, `types/ma.py` 48; grid 703–716), where `range[0] = 0` ("assume the minimum BMD for the MA is always 0", line 40) and `range[1]` is the largest finite value among each model's upper-tail grid entries (39–59).
5. BMD_MA = median, BMDL_MA = `alpha` quantile, BMDU_MA = `1 − alpha` quantile of the mixture (`bmds_helper.cpp` 199–201). Default model prior weights are uniform (`session.py` 135–140).

**The integer-division term.** Quoted lines at the pinned revision:

```text
src/bmdscore/dichotomous_entry_code.cpp:612    temp = res->models[i]->nparms / 2 * log(2 * M_PI) - res->models[i]->max +
src/bmdscore/dichotomous_entry_code.cpp:613           0.5 * log(max(0.0, cov.determinant()));
src/bmdscore/bmdStruct.h:109                     int nparms;                    // number of parameters in the model
src/bmdscore/bmdStruct.h:112                     double max;                    // Value of the Likelihood/Posterior at the maximum
src/bmdscore/bmds_helper.cpp:1148                res->nparms / 2.0 * log(2.0 * M_PI) + res->max + 0.5 * log(max(0.0, cov.determinant()));
```

`max` is filled from `a.MAP` (`dichotomous_entry_code.cpp` 159), which is the optimizer's minimized negative penalized log-likelihood (`bmd_calculate.h` 388: `rVal.MAP = OptRes.functionV;`; `statmod.h` 85–95: `negPenLike` returns negative log-likelihood plus negative log-prior). Hence line 612 implements the Laplace approximation log p(y) ≈ log p(y, θ̂) + (k/2)·ln 2π + ½·ln|Σ| — except that in C++ `nparms / 2` with an `int` left operand is integer division, evaluated before the multiplication. For k = 3 the term is ln 2π instead of 1.5·ln 2π. Basis: source + derived.

Execution of the expression shapes (`support/laplace_int_div.cpp`, g++ 15.2.0, `-O0 -std=c++17`; does not build BMDS):

| k | `k / 2 * log(2*M_PI)` | `k / 2.0 * log(2.0*M_PI)` | deficit | weight factor |
|---|---|---|---|---|
| 1 | 0.000000 | 0.918939 | 0.918939 | 0.398942 |
| 2 | 1.837877 | 1.837877 | 0 | 1 |
| 3 | 1.837877 | 2.756816 | 0.918939 | 0.398942 |
| 4 | 3.675754 | 3.675754 | 0 | 1 |

Basis: execution (expression semantics only).

Parameter counts in the default Bayesian set (`types/priors.csv`, prior_class 2; Multistage degree 2 from `session.py` 107–108): Hill 4; Gamma, LogLogistic, LogProbit, Multistage(2), Weibull 3; Logistic, Probit, QuantalLinear 2. `support/ma_weight_derived.py` maps any intended weight vector to the computed one: with intended weights 1/9 each, computed weights are 0.1668 for each even-k model and 0.0665 for each three-parameter model (total on three-parameter models 0.3327 vs 0.5556); with an intended 50/50 split between Logistic and LogLogistic, the computed split is 0.7148/0.2852. Basis: derived.

What this does and does not establish. It establishes, from source, that BMDS 25.2 dichotomous Laplace model averaging systematically down-weights odd-parameter models by a data-independent factor of 0.3989 relative to the standard Laplace formula, and that the same pattern appears at `dichotomous_entry_code.cpp:472` (MCMC averaging path) and `continuous_entry_code.cpp:1254` and `:1893` (`b[i].MAP_ESTIMATE.rows() / 2 * log(2 * M_PI)`, `rows()` being an integer index type). It does **not** establish the size of the resulting BMDL_MA shift on any real dataset (not measured; requires running BMDS with and without the fix), nor whether a newer BMDS release changed the line (later tags not examined). Whether the authors intended the term is unknown; the inconsistency with line 1148 and the standard formula is the evidence that it is unintended.

**Grid resolution (derived).** Because the averaged CDF lives on a 200-point uniform grid starting at 0 and extending to the widest model's upper-tail BMD, the grid step is `range[1]/200`. When one model's upper tail is long relative to the BMDL (common for shallow data), the BMDL_MA quantile is located with a step that can be a non-trivial fraction of its value. Magnitude: not measured.

### 3. EFSA 2022 averaging and PROAST

EFSA states that posterior model probabilities require marginal likelihoods approximated by "MCMC methods, Bridge sampling, Laplace approximation"; "In most cases the Laplace approximation provides reliable results, similar to the most accurate method of Bridge sampling (being more computationally demanding)", so Laplace "would be the default approach", with bridge sampling for apparent estimation failures. The default discrete prior over models is uniform. Priors on background, maximum response and BMD are translated to model parameters; a PERT prior example has minimum 0, mode 5, maximum 20 and shape 0/1/4. Alternatives to the BMDL as reference point are recommended when no model fits, BMD/BMDL > 20, the BMD is 10× below the lowest non-zero dose, or BMDU/BMDL > 50; EFSA notes these cut-offs were "inspired by those proposed by US EPA as 'default logic assumptions'… they lack a theoretical statistical basis and they have so far not been tested empirically." Basis: normative.

Cross-tool and cross-version differences reported in EFSA's own worked examples (Basis: documentation): quantal thyroid example (doses 0, 3, 12, 30 mg/kg-day; 6/50, 6/50, 34/50, 42/50): BMDL 1.5 mg/kg with PROAST 62.3 plus the MADr-BMD program (Wheeler & Bailer 2008) under the 2017 guidance, versus model-averaged BMDL 1.65 and BMDU 5.86 with the EFSA web app on PROAST 70.0. Continuous body-weight example (BMR 5%): BMDL 0.20, BMDU 0.41 mg/kg with PROAST 61.6 (Exponential and Hill), versus per-model results from PROAST 70.0 (e.g., Exponential BMD 0.297, BMDL 0.198, BMDU 0.41; Inverse Exponential 0.316, 0.219, 0.422). BMDS has the matching cut-offs as recommender rules: `bmd_bmdl_ratio_fail` 20, `low_bmd_fail` 10 (lowest-dose/BMD ratio), `high_bmd` 1 (BMD/highest dose), `roi_large` 2 (scaled residual), plus warn-level `bmd_bmdl_ratio_warn` 3 and `low_bmd_warn` 3 (`recommender/default.json`). Basis: source.

**Coverage evidence for averaged BMDLs.** Wheeler & Bailer (2007) found that averaging individual models' BMDLs "did not yield interval estimators that met nominal coverage levels in certain situations", whereas estimating the BMD from the averaged dose–response curve with a bootstrap BMDL "achieves nominal coverage in most cases, and is superior to picking the 'best fitting model'", while results remained sensitive to the model space. EPA (2012) similarly notes that an average of BMDLs "is not a 95% lower bound (on the average BMD)." BMDS 25.2 averages per-model BMD posterior CDFs (a mixture) rather than averaging BMDLs, so it avoids the construction both sources criticize; it is not the averaged-curve bootstrap construction Wheeler & Bailer simulated, so their coverage results do not transfer to it directly. Basis: documentation + source + derived.

### 4. From point of departure to reference dose

Deterministic recipe (Chiu et al. 2018 Introduction; Chiu & Slob 2015): POD (NOAEL or BMDL) ÷ a generic factor of 100 or a product of factors for interspecies (UF_A), intraspecies (UF_H), subchronic-to-chronic, LOAEL-to-NOAEL and database deficiencies; EPA recommends first applying body-weight^¾ allometric scaling followed by a smaller 3-fold UF_A. Chiu et al. note the unstated coverage: UF_A = 10 assumes humans are no more than 10-fold more sensitive "for most chemicals" without specifying "the actual proportion of cases (90%, 95%, 99%?)". EFSA (2022) holds that "the same uncertainty factors… are equally applicable to the BMDL and to the NOAEL." Basis: documentation + normative.

Probabilistic replacement (Basis: documentation): Chiu & Slob (2015) define a target human dose HD^I_M — the dose at which a fraction I of the population has an effect of magnitude ≥ M — with stated confidence; in their examples 90% confidence intervals for HD^I_M "span a 40- to 60-fold range" at I = 1% and M = 1–10%. Chiu et al. (2018) automated the WHO framework over 1,464 RfDs (608 chemicals), producing 1,522 HD^I_M values; lack of a BMD was the largest uncertainty contributor, followed by human variability; the approximate (APROBA-style) calculation agreed with 10⁷-sample Monte Carlo within 20–30%.

Toy composition (`support/rfd_css_toy.py`, numpy 2.3.5, seed 7): two independent lognormal factors with median 1 and P95 = 10 (σ = ln 10 / 1.6449 = 1.3999) give an analytic P95 of the product exp(1.6449·√2·σ) = 25.95, Monte Carlo 25.92 (2×10⁶ draws), and P(product > 100) = 0.00995. Applied to an illustrative POD of 1.65 mg/kg-day (the model-averaged BMDL of EFSA's quantal example), the deterministic RfD is 0.0165 and the "P95-of-product" value 0.0636 mg/kg-day. Basis: execution (toy model with author-chosen distributions; these are not WHO/IPCS or EPA default distributions and do not describe any chemical).

### 5. httk: model structure, Monte Carlo, reverse dosimetry, in-vivo evaluation

Source facts at the pinned revision (Basis: source):
- `calc_mc_css` defaults (`calc_mc_css.R` 453–480): `samples = 1000`, `which.quantile = 0.95`, `species = "Human"`, `daily.dose = 1`, `model = '3compartmentss'`, `httkpop = TRUE` with `httkpop.generate.arg.list = list(method = "direct resampling")`, `invitrouv = TRUE`, `output.units = "mg/L"`.
- Steady state (`calc_analytic_css_3compss.R` 192–229): hourly dose = daily dose / 24 / BW (with unit conversion; `calc_analytic_css.R` 390–393 first multiplies a per-kg dose by BW, so the net rate is per kg); `Qtotalliver = Qtotal.liverc/BW^0.25`; `Qgfr = Qgfrc/BW^0.25`; `Css = hourly.dose * Fabsgut * Fhep / (Qgfr * Fup + Clhep)`; the comment states this is "the same equation as Wetmore et al. (2012) page 160 or Pearce et al. (2017) equation section 2.2".
- Hepatic clearance (`calc_hep_clearance.R` 255–282): well-stirred `CLh = Q*fup*Clint/(Q + fup*Clint)` (optionally with a blood:plasma correction, line 271), parallel-tube and dispersion alternatives; non-restrictive clearance sets `fup = 1` (line 207).
- Reverse dosimetry (`calc_mc_oral_equiv.R` 367–399): `Css` at the requested quantile for 1 mg/kg/day, then `dose <- conc/Css`; using the 95th-percentile Css yields the dose protecting the more sensitive 5% of simulated individuals.
- Variability and uncertainty: physiology resampled from NHANES (`httkpop_generate.R` header: "sampled with replacement directly from NHANES data", weighted by sample weight); in-vitro measurement and population CVs `fup.meas.cv = 0.4`, `clint.meas.cv = 0.3`, `fup.pop.cv = 0.3`, `clint.pop.cv = 0.3`, `fup.lod = 0.01`, `clint.pvalue.threshold = 0.05` (`invitro_mc.R` 124–144); Clint fitted to a lognormal from median and 95% limits, and a fraction `round(Clint.pvalue*samples)` of draws forced to zero clearance (286–300); generic `monte_carlo` draws CV-specified parameters from a normal truncated at zero (`monte_carlo.R` 86–100).

Toy evaluation of the transcribed formula (`support/rfd_css_toy.py` Part B; hypothetical parameters, BW 70 kg, Fhep = Fabsgut = 1): Fup 0.5/Clint 1 → Css 0.0258 mg/L per 1 mg/kg/day (dose for 1 mg/L: 38.8 mg/kg/day); Fup 0.05/Clint 1 → 0.2568 (3.89); Fup 0.5/Clint 50 → 0.0028 (360); Fup 0.01/Clint 50 → 0.0810 (12.3). Low Fup raises Css when renal filtration and restrictive clearance dominate. Basis: execution (toy transcription; no httk chemical data used).

Published evaluation (Basis: documentation):
- Wetmore et al. (2012): Clint and plasma protein binding measured for 239 ToxCast chemicals; oral equivalent doses across > 500 assays; 18 chemicals (9.9% of those with exposure estimates) had oral equivalent doses at or below the highest estimated U.S. exposures; ranking by nominal assay concentration would have prioritized different chemicals.
- Pearce et al. (2017): four TK models; human in-vitro data for 553 chemicals (94 pharmaceuticals, 415 ToxCast chemicals); rat-specific in-vitro data for 67.
- Wambaugh et al. (2015): literature in-vivo data for 87 chemicals used to identify properties associated with poor predictions; Css comparison for 11 environmental chemicals and 74 pharmaceuticals; chemical-to-chemical variance explained in predicted Css R² ≈ 0.34 (as summarized in Wambaugh et al. 2018); ≈65% of chemicals within ≈3.2-fold (10^½), 28% ≈6-fold overestimated and 8% ≈120-fold overestimated on average; a seven-category TK triage.
- Wambaugh et al. (2018): new rat IV/oral studies for 26 non-pharmaceuticals plus 19 previously published chemicals; "predictions for bioavailability were not effective" for non-pharmaceuticals (as low as 0.3% bioavailable), clearance generally underestimated, but steady-state, peak and AUC concentrations "predicted with reasonable accuracy", improving when measured bioavailability was used.
- Wambaugh et al. (2019): new fup (418 chemicals) and Clint (467) measurements; a 10%/30%/100% plasma-protein fup protocol cut "too low to measure" from 44% to 9.1% and median fup CV from 0.4 to 0.1 — the same 0.4 that remains the code default `fup.meas.cv`.

### 6. Performance, footprint, comprehensibility and validation matrix

| Level | Evidence | Value |
|---|---|---|
| L1 authoring/maintenance | source sizes at pins (`wc -c`/`wc -l`) | `dichotomous_entry_code.cpp` 29,965 B (919 lines); `continuous_entry_code.cpp` 95,017 B (2,927 lines); `bmds_helper.cpp` 199,552 B (6,465 lines); `calc_mc_css.R` 27,525 B; `invitro_mc.R` 27,719 B. Person-time, repair cost: not measured |
| L2 build | bmdscore/pybmds and httk build time and memory | not measured (not built) |
| L3 fitting latency | per-model and MA fit time; Laplace vs bridge sampling vs MCMC | not measured; EFSA calls bridge sampling "more computationally demanding" (no figures); pybmds MCMC defaults `samples = 100`, `burnin = 20` (max 1000); MA CDF grid 200 points; httk default 1,000 Monte Carlo draws |
| L4 runtime of outputs | not applicable (outputs are numbers, not generated code) | known not to apply |
| L5 checking | automated plausibility rules | BMDS recommender rule set (thresholds above); runtime not measured |
| L6 footprint | memory, artifact sizes | not measured for BMDS/httk; toy probes: `ma_weight_derived.py` 0.01 s wall, 9.5 MB max RSS; `rfd_css_toy.py` 0.33 s, 66 MB (`/usr/bin/time`, Python 3.13.15, Intel Xeon 2.60 GHz VM) |

**C1 — human comprehensibility.** A risk assessor must reconcile at least eight independent choices to reproduce a POD: BMR family (extra/added; SD/relative/hybrid), BMR size, distribution (normal/lognormal), model set, constraints or priors, selection rule or averaging weights, bound construction (profile, bootstrap, credible) and acceptance cut-offs. Several are nonlocal: the BMDS "sufficiently close" factor lives in a JSON rule file, the model-weight formula in C++, and the BMR default in Python types. The integer-division defect is invisible in any output — weights still sum to one — which is the failure-legibility problem in its purest form. Basis: derived.

**C2 — simplification.** EFSA's single eight-model set for quantal and continuous data, and Chiu & Slob's recasting of all endpoints as an underlying continuous individual response, are both moves that turn the quantal/continuous split into one case. In BMDS, restriction bounds and Bayesian priors are two mechanisms enforcing one invariant (bounded low-dose slope); expressing restrictions as degenerate priors would make frequentist-restricted and Bayesian fits instances of one parameterization. The four copies of the Laplace term (lines 472, 612, 1254, 1893) plus the correct `BIC_equiv` copy (1148) are one formula duplicated five times; a single shared helper would have made the defect impossible to introduce in only some copies. On the RfD side, a product of upper-percentile factors is a special case of a probabilistic composition with an unstated coverage level; making the coverage explicit is the minimal generalization. Basis: derived.

**V1–V4 — validation.**
- V1 (specification adequacy, non-vacuity): Wheeler & Bailer (2007) Monte Carlo coverage studies for MA-BMDLs; EFSA's statement that its cut-offs are untested empirically; no spec-mutation or golden-reference test of the BMDS weight formula was found in the examined files.
- V2 (differential testing): EFSA's worked examples are an informal cross-version differential of PROAST (BMDL 1.5 vs 1.65 on the same quantal data). An independent Laplace implementation compared against BMDS on any dataset with mixed two- and three-parameter models would expose the 0.3989 factor; this was not run.
- V3 (concurrency, crash, silicon, leakage): the per-model OpenMP loop (585–602) writes disjoint `res->models[i]`, so no data race was apparent from reading; determinism across thread counts not measured. Silicon and physical-leakage validation are known not to apply.
- V4 (field validation): for httk, the in-vivo comparisons above are the field validation (R² ≈ 0.34; most errors are overestimates of Css, which make reverse-dosimetry doses conservative). For BMD/RfD, no ground-truth population-incidence validation exists; Chiu et al. (2018) compare against traditional RfDs, not observed human outcomes.

## Boundaries

- **Not examined:** PROAST source code (distributed as `proast71.1.zip`, not in a public repository); the EFSA web application source; BMDS tags `26.1`, `26.1a3`–`26.1a5` (so whether the integer division persists after 25.2 is unknown); BMDS continuous model internals beyond the averaging lines; `IDPriorMCMC.cpp` beyond its prior-density comments; httk PBTK ODE models and lifestage variants in detail; the National Research Council (2009) report text (only Chiu et al.'s characterization); WHO/IPCS APROBA default distributions (numeric values sit in a figure-table not extracted); Slob (2002) and Crump (1984) beyond their abstracts; Pearce et al. (2017) beyond the abstract.
- **Not measured:** the BMDL_MA shift caused by the integer-division term on any real dataset; BMDS, PROAST or httk run times, memory, or numerical outputs; the effect of the 200-point grid on BMDL_MA precision.
- **Unknown:** whether BMDS developers consider the `nparms / 2` term intentional; whether EPA assessments used BMDS dichotomous Bayesian model averaging with mixed parameter counts (would determine practical impact).
- **Known not to apply:** the toy lognormal uncertainty-factor composition to any regulatory distribution; the toy Css values to any chemical; L4 generated-code performance to these statistical tools.
- **Unsupported / not established:** that BMDS 25.2 model-averaged BMDLs are materially wrong for typical datasets (only the weight bias is established); that probabilistic HD^I_M values are more protective or less protective than RfDs in general (Chiu et al. report RfDs "generally within an order of magnitude" of the I = 1% lower bound, with chemical-specific variation); that httk Css predictions are accurate for individual chemicals (evaluations show category-dependent bias up to ≈120-fold).

## Evidence

All evidence acquired 2026-11-20 (UTC).

**Git sources.**
- `USEPA/BMDS@0018abea713f61b0bcc9dd30821af18b61a77e77` (commit date 2026-02-04; `src/pybmds/__init__.py`: `__version__ = "25.2"`): `src/bmdscore/dichotomous_entry_code.cpp` lines 39–59, 159, 287–330, 443–481, 582–719, 797–807; `src/bmdscore/bmdStruct.h` 107–116; `src/bmdscore/bmds_helper.cpp` 182–217, 1137–1149, 1242–1256, 2422–2464; `src/bmdscore/continuous_entry_code.cpp` 999–1003, 1250–1262, 1891–1895; `src/include/bmd_calculate.h` 388; `src/include/statmod.h` 85–95; `src/include/cmodeldefs.h` 21–31 (`d_hill = 1` … `d_weibull = 9`); `src/pybmds/session.py` 50–80, 102–150; `src/pybmds/types/ma.py` 17–58, 86–113; `src/pybmds/types/dichotomous.py` 23–42; `src/pybmds/types/continuous.py` 24–56; `src/pybmds/types/priors.csv`; `src/pybmds/models/dichotomous.py` 76–178; `src/pybmds/constants.py` 59–60, 204–213; `src/pybmds/recommender/recommender.py` 131–209; `src/pybmds/recommender/default.json`; `src/pybmds/recommender/checks.py` 134–247.
- `USEPA/CompTox-ExpoCast-httk@f6605eebc6eb5a483a8824dce6cbddb36c8fb091` (commit date 2026-04-28; `httk/DESCRIPTION` Version 2.7.4): `httk/R/calc_mc_css.R` 453–480; `httk/R/calc_analytic_css_3compss.R` 186–229; `httk/R/calc_analytic_css.R` 213–242, 390–398; `httk/R/calc_hep_clearance.R` 77–84, 204–207, 255–287; `httk/R/calc_mc_oral_equiv.R` 243–248, 360–430; `httk/R/invitro_mc.R` 124–144, 240–300; `httk/R/monte_carlo.R` 73–133; `httk/R/httkpop_generate.R` 1–17.

**Normative and literature sources (DOIs resolved through the DOI handle API; bibliographic details confirmed on PubMed, PubMed Central, Crossref or publisher pages).**
- U.S. EPA. Benchmark Dose Technical Guidance. EPA/100/R-12/001, June 2012 (PDF at the URL in REPORT.json; no DOI).
- EFSA Scientific Committee. EFSA J 2022;20(10):7584. doi:10.2903/j.efsa.2022.7584 (PMC9593753) — abstract, Sections 2.5–2.6, Table 2, worked examples.
- RIVM PROAST page, https://www.rivm.nl/en/proast (download `proast71.1.zip`; web apps at efsa.openanalytics.eu and proastweb.rivm.nl).
- Crump KS. Fundam Appl Toxicol 1984;4(5):854–871. doi:10.1016/0272-0590(84)90107-6 (PMID 6510615).
- Slob W. Toxicol Sci 2002;66(2):298–312. doi:10.1093/toxsci/66.2.298 (PMID 11896297).
- Wheeler MW, Bailer AJ. Risk Anal 2007;27(3):659–670. doi:10.1111/j.1539-6924.2007.00920.x (PMID 17640214).
- Chiu WA, Slob W. Environ Health Perspect 2015;123:1241–1254. doi:10.1289/ehp.1409385 (PMC4671238).
- Chiu WA, et al. Environ Health Perspect 2018;126(6):067009. doi:10.1289/EHP3368 (PMC6084844).
- Wetmore BA, et al. Toxicol Sci 2012;125(1):157–174. doi:10.1093/toxsci/kfr254 (PMID 21948869).
- Pearce RG, et al. J Stat Softw 2017;79(4):1–26. doi:10.18637/jss.v079.i04.
- Wambaugh JF, et al. Toxicol Sci 2015;147(1):55–67. doi:10.1093/toxsci/kfv118 (PMC4560038).
- Wambaugh JF, et al. Toxicol Sci 2018;163(1):152–169. doi:10.1093/toxsci/kfy020 (PMC5920326).
- Wambaugh JF, et al. Toxicol Sci 2019;172(2):235–251. doi:10.1093/toxsci/kfz205 (PMID 31532498).
- National Research Council. Science and Decisions: Advancing Risk Assessment. 2009. doi:10.17226/12209 (DOI resolved; text not examined).
- Wheeler MW, Bailer AJ. J Stat Softw 2008;26(5). doi:10.18637/jss.v026.i05 (DOI resolved; cited by EFSA as the MADr-BMD program; not examined).

**Executed probes (package `support/`).** `laplace_int_div.cpp` → `laplace_int_div.out.txt` (compile: `g++ -O0 -std=c++17 -o laplace_int_div laplace_int_div.cpp`); `ma_weight_derived.py` → `ma_weight_derived.out.txt`; `rfd_css_toy.py` → `rfd_css_toy.out.txt` (numpy). Host: x86-64 Linux VM, Intel Xeon 2.60 GHz, Python 3.13.15, g++ 15.2.0.

## Revalidation

1. **Integer-division term:** at any BMDS revision, run `git grep -n "nparms / 2 \|rows() / 2 " src/bmdscore` and inspect `estimate_ma_laplace` in `dichotomous_entry_code.cpp`. If the term reads `/ 2.0` (or the operand is cast to `double`), the defect is fixed; rerun `support/ma_weight_derived.py` only if the default model set or parameter counts (`types/priors.csv`, `session.py`) changed.
2. **Magnitude on real data (not yet done):** build pybmds at the pin, run a dichotomous Bayesian session with model averaging on EFSA's quantal example (0, 3, 12, 30 mg/kg-day; 6/50, 6/50, 34/50, 42/50), then patch line 612 to `/ 2.0` and rerun; compare `posteriors` and `bmdl`.
3. **Defaults drift:** re-read `types/dichotomous.py` 36–41, `types/continuous.py` 47–55, `recommender/default.json`, and `session.py` 50–60 / 102–140.
4. **EFSA/EPA rules:** a new EFSA or EPA guidance edition supersedes Section 1; check BMR, bound and model-set statements first.
5. **httk:** at a new httk revision, diff `calc_analytic_css_3compss.R` 192–229, `calc_mc_css.R` 453–480 and `invitro_mc.R` 124–144; rerun Part B of `support/rfd_css_toy.py` if the formula changes.
6. **What cannot be cheaply revalidated:** in-vivo predictive accuracy of httk and the population protectiveness of RfDs — both require new empirical comparisons.
