# Integrated fish stock assessment diagnostics: Stock Synthesis, Mohn's rho variants and retrospective patterns, hindcast MASE in r4ss and ss3diags, lessons from the northern cod collapse, and management strategy evaluation with SSMSE

## Summary

- **"Mohn's rho" names several different statistics, and the open tools return more than one.**
  - `r4ss::SSmohnsrho()` returns, for each quantity:
    - the **sum** over peels of terminal-year relative differences, labelled "as in Mohn (1999)";
    - their **mean**, labelled "AFSC / Hurtado-Ferro";
    - a "Woods Hole" variant that averages over all years within a peel and then sums over peels.
  - With P peels the sum is exactly P times the mean.
  - The widely used acceptance ranges (−0.15 to 0.20 for longer-lived species; −0.22 to 0.30 for shorter-lived species; Hurtado-Ferro et al. 2015) are 90 % simulation intervals **for the mean form**.
  - Measured on Stock Synthesis (SS3) v3.30.26 with five peels:
    - The `Simple` test model has SSB ρ = −0.168 (mean), −0.840 (sum) and −0.188 (Woods Hole).
    - The `Hake_2018` test model has SSB ρ = 0.121 (mean) and 0.603 (sum). The sum fails the threshold that the mean passes.
- **Retrospective patterns arise even in correctly specified models,** and the size of ρ says nothing about the sign or size of terminal-year bias (Hurtado-Ferro et al. 2015). Misspecified natural mortality gives the largest |ρ|. For biomass, a positive ρ (negative for F) is the most dangerous for conservation.
- **ss3diags `SSmase()` misaligns hindcast and naive residuals for indices with gaps** (both the legacy `jabbamodel` v1.10.3 and the current `nmfs-ost` v2.2.2 code).
  - When the earliest evaluation year has no observation, `pred.resid[-1]` drops the **most recent** prediction residual instead of the earliest one, and the table labels the survivor with the wrong year.
  - On the triennial `SURVEY1` of `Simple`, the code's logic yields MASE = 0.176 from the 1998 residual. Pairing the 2001 residual with the 2001 naive step instead gives 0.932.
- **SS3 sums lambda-weighted likelihood components** (`SS_objfunc.tpl` L1064–1110).
  - Its forecast control rule switches via logistic joins with a fixed slope of 100 per spawning-output unit. The 10–90 % width is therefore 0.044 units regardless of stock scale.
  - Survey error type −2 ("gamma") passes the data check but is unimplemented: the v3.30.26 binary exits with status 1 and no diagnostic.
- **The northern cod analyses that were examined** blame overexploitation, not the environment (Hutchings & Myers 1994). Walters & Maguire (1996) draw three lessons for assessment:
  1. optimistic assessments and forecasts drive TACs and overcapacity;
  2. commercial CPUE as an abundance index risks overestimating stock size, so invest in surveys;
  3. recruitment overfishing is possible even for fecund species.
- **SSMSE couples SS3 operating and estimation models** in a closed loop. It generates data with SS's parametric bootstrap, which contains measurement error only. Management strategies are an SS3 estimation model, no catch, last year's catch, an interim rule, or a custom function. It searches F (20 loops, tolerance 0.001) and applies a multiplicative implementation error, default 1. This covers most of Punt et al.'s (2016) MSE elements, but conditioning, the split into reference and robustness sets, and plausibility weighting are left to the user. Software self-tests with error-free data are not yet supported: setting `use_SS_boot = FALSE` stops.

## Applicability

The subjects are pinned GitHub revisions plus peer-reviewed papers by DOI:

- **SS3 source:** `nmfs-ost/ss3-source-code` at HEAD `94cea415b5861104289c6fa80e2737c94b090487` (2026-11-17). Source claims about `SS_objfunc.tpl`, `SS_benchfore.tpl`, `SS_readdata_330.tpl`, `SS_readcontrol_330.tpl` and `SS_expval.tpl` refer to this revision.
- **SS3 executable:** the released binary `ss3_linux`, v3.30.26, built from tag commit `25bab0242fe1ac044db2bd7eb08f7f3613016ad9`. All execution claims refer to this binary (SHA-256 `e186c269…401ba10b`). The safe and optimized builds were both measured.
- **Test models:** `Simple` and `Hake_2018` from `nmfs-ost/ss3-test-models` at `236171c9bc084a4e380731ca446fc9220f5c8a46`. `Hake_2018` is a test-suite derivative of the 2018 Pacific hake assessment. Results here describe that test model, not the official assessment.
- **r4ss** (`r4ss/r4ss` at `c5d7e20b484b91f3080eeb9d9cddc0127948b460`, DESCRIPTION version 1.56.0):
  - `R/SSmohnsrho.R` and `R/retro.R` were read.
  - **R was not available on the host, so no R code was executed.** Their arithmetic was transcribed into Python (`support/ss3_retro_probe.py`) and applied to SS3 output.
- **ss3diags, two repositories:**
  - the legacy `jabbamodel/ss3diags` at `e15da7a22f91141248286104bdfa3f9cf7895814` (v1.10.3, last pushed 2024-10-03). This is the repository cited by Carvalho et al. (2021).
  - the actively maintained `nmfs-ost/ss3diags` at `d8773e0ac9040e9f8771596a1db54945760f923f` (v2.2.2).
  - The `SSmase` logic discussed below is identical in both.
- **SSMSE:** `nmfs-ost/SSMSE` at `4d858d884a77bf34549ac5f19633f83be600eee8` (v0.4.0), source only, not executed.

Literature scope:

- Hutchings & Myers (1994), Mohn (1999), Brooks & Legault (2016) and Deroba (2014) were examined at abstract level only.
- Walters & Maguire (1996) was examined through its publisher abstract only.
- The other papers were read in full text, as listed under Evidence.

Northern cod conclusions are therefore limited to what those abstracts state.

## Findings

### 1. What analyses of the northern cod collapse concluded

Basis: documentation (abstracts).

| Source | Statement (quoted) | Concerns |
|---|---|---|
| Hutchings & Myers 1994 | "overexploitation precipitated the commercial extinction of northern cod … in 1992"; "A twofold decline in annual survival probabilities in the 1980s was concomitant with increased inshore and offshore fishing effort, declining catch rate, and spatial shifts in gillnetting effort"; "We reject hypotheses that attribute the collapse … to environmental change" | decision process (harvest), data (catch-rate signals) |
| Walters & Maguire 1996 | "(1) assessment errors can contribute to overfishing through optimistic long-term forecasts leading to the build-up of overcapacity or through optimistic assessments which lead to TACs being set higher than they should" | model structure → decision process |
| Walters & Maguire 1996 | "(2) stock size overestimation is a major risk when commercial catch per effort is used as an abundance trend index, so there is continued need to invest in survey indices of abundance trend no matter what assessment methodology is used" | data (index choice; hyperstable CPUE) |
| Walters & Maguire 1996 | "(3) the risk of recruitment overfishing exists and may be high even for very fecund species like cod. This implies that harvest rate targets should be lower than has often been assumed" | model assumptions (stock–recruit), decision process |
| Mohn 1999 (eastern Scotian Shelf cod, not northern cod) | "The retrospective problem is shown to be a result of the traditional analysis techniques and a non-stationarity in the data"; "failure to correct the retrospective problem … could lead to catch-level advice that would be twice or more the intended level" | model structure + data non-stationarity |

The sources link to the diagnostics below in two ways (derived):

- **CPUE hyperstability** is a time-varying catchability process. Hurtado-Ferro et al. (2015) show that unmodelled time-varying processes produce retrospective patterns.
- **Retrospective diagnostics** were designed to expose systematic revision of the kind seen in cod sequential population analysis.

### 2. The retrospective statistic: definitions and implementations

**Definitions** (Basis: papers + source):

- Hurtado-Ferro et al. (2015, Eq. 1) average over peels the relative difference between each peel's terminal-year estimate and the full-data estimate for that year. They add: "Note that this formulation is slightly different from that given by Mohn (1999), where instead of summing across peels, these are averaged (R. Mohn, pers. comm.)." The sentence is ambiguous. We read it as "Mohn summed; this paper averages", which is also how the r4ss code labels the two forms.
- Carvalho et al. (2021, Eq. 2) and Legault (2020) use the mean: `ρ = (1/P) Σ_p (X̂_{Y−p,Y−p} − X̂_{Y−p,Y}) / X̂_{Y−p,Y}`. Legault calls it "the commonly used version".
- Kell et al. (2021) use the same mean over the final times of the windows.

**What r4ss computes** (`R/SSmohnsrho.R` at `c5d7e20`; Basis: source):

```r
L79-83:   for (i in 1:(N - 1)) {
            ind <- which(summaryoutput[["SpawnBio"]][["Yr"]] == endyrvec[i + 1])
            mohnSSB[i] <- (summaryoutput[["SpawnBio"]][ind, i + 1] -
              summaryoutput[["SpawnBio"]][ind, 1]) /
              summaryoutput[["SpawnBio"]][ind, 1]
L161:     mohn.out[["SSB"]] <- sum(mohnSSB)
L166:     mohn.out[["WoodHole_SSB.all"]] <- sum(mohnSSB.all)
L174:     mohn.out[["AFSC_Hurtado_SSB"]] <- sum(mohnSSB) / length(mohnSSB)
```

Notes on the r4ss implementation:

- `mohnSSB.all[i]` (L111–116) is the mean of the relative differences from `startyr + 1` to the peel's end year. L166 then **sums** these over peels, so the "Woods Hole" value also scales with P.
- The same pattern holds for recruitment, Bratio and F. F's all-years window starts at `startyr` (L142–151).
- The default `endyrvec` (L61–64) is `rev((endyrs[N] − N + 1):endyrs[N])`. It relies on SS3 reporting the un-peeled end year for every retrospective run. In our runs, retrospective `Report.sso` files print `Retro_year: 1996` separately; we did not check how r4ss reads `endyrs`.

**What ss3diags `SShcbias()` computes** (`R/SShcbias.R` at `e15da7a` L95–104):

- `rho.i = (y[length(y)] − y.ref[length(y)]) / y.ref[length(y)]` and `rho = mean(rho.i)`. This is the AFSC / Hurtado-Ferro mean.
- It also computes a one-step-ahead "forecast rho" from the peel's estimate at `endyr + 1`.
- In our transcription it matches r4ss's `AFSC_Hurtado` value to all printed digits (−0.1679385 for `Simple` SSB).

**Retrospective runs in r4ss** (`R/retro.R` L428–588; Basis: source):

- The default `years = 0:-5` gives five peels.
- For each peel the code sets `retro_yr` and `init_values_src = 0` in `starter.ss`.
- The default `adjustments` shift:
  - `MainRdevYrLast`;
  - the bias-adjustment years (`last_yr_fullbias_adj`, `first_recent_yr_nobias_adj`);
  - time blocks that start after the peel's end year (removing them);
  - forecast years and benchmark years. Interval years before the mean model year move only their end year.
- The model is then run with `run(...)`, whose default `extras = ""` estimates the Hessian.

**Measured** (Basis: execution of SS3 v3.30.26 plus a Python transcription of the r4ss and ss3diags formulas; five peels; `support/*_retro_results.json`):

| Model, quantity | per-peel terminal relative differences (peels 1…5) | mean (AFSC / Hurtado; ss3diags) | sum ("Mohn 1999") | Woods Hole (r4ss) | Hurtado-Ferro longer-lived range |
|---|---|---|---|---|---|
| `Simple` SSB | −0.173, −0.241, −0.107, −0.135, −0.184 | **−0.168** | −0.840 | −0.188 | outside (< −0.15) |
| `Simple` F | 0.213, 0.348, 0.132, 0.179, 0.261 | 0.227 | 1.133 | 0.247 | n/a (SSB rule) |
| `Simple` Bratio | −0.196, −0.282, −0.110, −0.124, −0.258 | −0.194 | −0.969 | −0.350 | – |
| `Hake_2018` SSB | 0.203, 0.152, 0.062, 0.106, 0.079 | **0.121** | 0.603 | 0.009 | inside (mean) / outside (sum) |
| `Hake_2018` recruitment | −0.037, 13.40, −0.693, 3.99, 0.815 | 3.495 | 17.48 | 0.467 | – |

- **`Simple` forecast rho.** ss3diags' one-step forecast bias for `Simple` SSB is −0.196, against ρ = −0.168.
- **Recruitment ρ (derived).** It is dominated by single peels: a terminal recruitment estimated from little data moves by a factor of 14. Ranges calibrated on SSB do not transfer to it.
- **Rho adjustment** (Legault 2020, Northeast US practice): adjusted = estimate / (1 + ρ), applied when the adjusted terminal SSB or F falls outside the 90 % CI. Legault calls it "an ad hoc adjustment with not a lot of theoretical underpinning".

### 3. Causes of retrospective patterns and expected values

Basis: papers (Hurtado-Ferro et al. 2015).

**Design:**

- `ss3sim` on SS3, simulating 100 years with a fishery from year 25 and a biennial survey from year 60 (CV 0.2). Compositions use multinomial n = 100.
- Three life histories: cod, flatfish and sardine (M = 0.2, 0.2 and 0.4).
- Unmodelled time variation of growth (±25 %), selectivity (L50 ±25 %) or M (MSY ±25 %), applied recently or long ago, abruptly or gradually.
- Three F patterns.
- 216 factorial scenarios plus 9 base cases, with 50 replicates each. Each replicate was fitted six times: the full data plus five peels.
- Only gradients < 0.1 were accepted, and the Hessian was not inverted.

**Results:**

- Base (correctly specified) cases had median ρ of 0.01, −0.01 and −0.02 but non-zero spread: "pure random noise can produce what appear retrospective patterns".
- Faster growth, selection of larger fish or lower M give negative biomass ρ. The opposite changes give positive ρ. Changes in M give the largest |ρ|.
- Residual variance of ρ in the ANOVA was 91–97 %.
- "The value of Mohn's ρ was not related to bias in biomass in the terminal year".

**Rule of thumb** (90 % intervals of the base cases):

- [−0.15, 0.20] for longer-lived species (flatfish base);
- [−0.22, 0.30] for shorter-lived species (sardine base);
- false positives occur 10 % of the time, and 30 % at survey CV 0.8.
- Only one process changed at a time, and catches were exactly known. Catch misreporting, a classic cause, was not simulated.

### 4. Stock Synthesis formulation

**Structure** (Methot & Wetzel 2013; Basis: documentation):

- A population sub-model, a highly developed observation sub-model, and an overall weighted penalized log-likelihood estimated in ADMB. Variance comes from the inverse Hessian or MCMC.
- Data: catch, indices, discards, mean weight, length, age and size compositions, size-at-age, tags, morphs and environmental series.
- Indices are lognormal, normal or Student's t, and compositions are multinomial. The current source also has Dirichlet-multinomial variants (θ·n and β) and a multivariate Tweedie option (`SS_objfunc.tpl` L611–630).
- Selectivity has more than a dozen forms. Parameters vary in time through deviations, blocks, random walks, trends or environmental links.
- Benchmarks are F_SPR, F_Btarget and F_MSY. The forecast passes are OFL; then the harvest policy with caps and allocations; then stochastic recruitment and implementation error.
- About "20,000 lines of code" in one ADMB file (2013).

**Objective function** (`SS_objfunc.tpl` at `94cea41`; Basis: source):

- L1064–1110 sum phase-specific lambda-weighted components:
  - survey, discard, mean-weight, length, age and size-at-age likelihoods;
  - equilibrium catch and catch;
  - recruitment deviations and regime;
  - parameter priors and parameter deviations;
  - the F ballpark;
  - a crash penalty `CrashPen = square(1.0 + (1000.*CrashPen/(1000.+CrashPen))) - 1.0` (L1061);
  - forecast recruitment;
  - soft bounds;
  - size-frequency, morph and tag likelihoods.
- Survey likelihood options (L131–153):
  - `0` lognormal: `0.5·((log obs − est)/se)² + sd_offset·log(se)`;
  - `1` lognormal with `+0.5·se²` bias adjustment;
  - `>1` Student-t with df = errtype;
  - `−1` normal;
  - `−2`: `// gamma option will go here`, an empty branch.

**Measured** (Basis: execution; `Simple`, v3.30.26, default starter):

| `LIKELIHOOD` component | value |
|---|---|
| TOTAL | 1306.38 |
| Survey | −3.99044 |
| Length_comp | 650.96 |
| Age_comp | 586.657 |
| Size_at_age | 79.2224 |
| Recruitment | −7.52769 |
| Parm_priors | 1.05541 |
| Parm_softbounds | 0.00120332 |
| Catch | 3.67472e-11 |

**Error type −2 is accepted and then aborts** (Basis: source + execution):

- `SS_readdata_330.tpl` L701 rejects only `if (Svy_errtype(f) < -2 )`; the declaration comment at L676 reads `// -2=gamma(Cole); -1=normal; 0=lognormal …`. The same check (L701) and the empty likelihood branch (L149) are present at tag v3.30.26 (`25bab02`).
- The expected-value code (`SS_expval.tpl` L207: `//  gamma will go here`) and the likelihood (above) are placeholders.
- The parameter-label branch in `SS_readcontrol_330.tpl` L3120–3132 handles only `== -1` and `>= 0`.
- Changing only `SURVEY1`'s error type from 0 to −2 in `Simple/data.ss` made `ss3_linux` print "Data read successful 999" and then exit with status 1 during control-file reading. `warning.sso` held no message about it. Why the binary aborts is **unknown**; a missing parameter label is a hypothesis.

**Harvest control rule** (`SS_benchfore.tpl` L2784–2841; Basis: source + derived):

```cpp
L2784:  join1 = 1. / (1. + mfexp(100. * (SSB_current - H4010_bot * HCR_anchor)));
L2785:  join2 = 1. / (1. + mfexp(100. * (SSB_current - H4010_top * HCR_anchor)));
```

- Policies 1 and 3 ("west coast") scale catch by `(H4010_top·anchor/SSB)·(SSB − bot)/(top − bot)`. Policies 2 and 4 ("Alaska") scale F linearly. The buffer `H4010_scale` is applied to F (policies 1–2) or to catch (3–4).
- Because the slope 100 multiplies absolute spawning output, the 10–90 % width of each join is `2 ln 9 / 100 = 0.0439` units (`support/hcr_join_width.py`). That is 4 × 10⁻⁵ of an intercept of 1,000 t, but 44 % of an intercept of 0.1 units. The ramp's corners are effectively sharp for stocks in tonnes, and visibly smoothed for spawning output reported in small units.
- **Implementation error in the forecast** (L2479) is `Fcast_Catch_Store(t, f) *= mfexp(Fcast_impl_error(y)); //  should this be bias adjusted?`. The developers flag the lack of a lognormal mean correction themselves.

### 5. Recommended diagnostics and where implementation differs from guidance

The cookbook (Carvalho et al. 2021; Basis: papers) recommends this order:

1. **Convergence:**
   - no parameters on bounds;
   - final gradient ≤ 1.00E-04 (not absolute);
   - positive-definite Hessian ("not, in itself, an indication of model convergence");
   - correlations > 0.95 and CVs > 100 % flagged.
2. **Goodness of fit:**
   - runs test, which fails at p < 0.05;
   - the three-sigma limit;
   - RMSE ≤ 0.3 counts as "reasonably precise", but RMSE should not be used for model selection in isolation.
3. **Consistency:**
   - R0 likelihood profile by component;
   - age-structured production model (ASPM), with and without recruitment deviations;
   - retrospective ρ within the Hurtado-Ferro ranges, with peels and forecasts inside the 95 % CI of the reference run.
4. **Prediction skill:** hindcast cross-validation with MASE. A score above 1 is worse than a random walk, and 0.5 is "twice as accurately as a naïve baseline".
5. **Jitter,** last, because of its run time.

Retrospective analysis is "often the key diagnostic for accepting or rejecting a model" in ICES (Carvalho et al.; Kell et al. 2021).

| Diagnostic | Guidance | Open implementation | Difference |
|---|---|---|---|
| Mohn's ρ | Mean over peels (Carvalho Eq. 2) | r4ss returns sum, mean and Woods Hole sum; ss3diags returns mean | Choosing the r4ss `SSB` element applies thresholds to a P-times-larger number |
| Forecast bias ρ_F | Mean relative error of one-step SSB forecasts | `SShcbias` `fcrho` | – |
| MASE | Carvalho Eq. 3: one-step forecasts, naive `ŷ_t = y_{t−1}` over the same h years. Kell 2021 Eq. 5: horizon h, naive `y_{t−h}`, denominator over n+1+h points | `SSmase`: log residuals from each peel's prediction at `endyr+1`; naive = log difference between consecutive *observed* evaluation years; `MASE.adj` floors the denominator at 0.1 | The two papers define the denominator differently. `SSmase` follows neither exactly for gappy indices, and has the alignment defect below |

**`SSmase` residual alignment** (Basis: source + execution; not executed in R).

In both pinned ss3diags revisions, `SSmase` has this logic (nmfs-ost `R/SSmase.R` line numbers; legacy file L152–156, L171–192):

```r
L177:  pe.eval <- which(yr.eval %in% yr)
L179:  if (length(which(yr.eval %in% yr)) - length(pe.eval) < 1) {
L180:    pe.eval <- pe.eval[-1]
L211:  for (iline in (2:nlines)) {
L216:    if (endyrvec[iline - 1] %in% yr) {
L220:      pred.resid <- c(pred.resid, log(y[length(x)]) - log(yobs[length(x)]))
L226:  if (length(pred.resid) > length(pe.eval)) pred.resid <- pred.resid[-1]
L231:  naive.eval <- log(obs.eval[pe.eval]) - log(obs.eval[is.na(obs.eval) == F][-(npe + 1)])
L238:  res.i <- data.frame(..., Year = yr.eval[pe.eval], Pred.Res = pred.resid, Naive.Res = naive.eval, ...)
```

How the misalignment arises:

- The condition at L179 is always true (x − x < 1), so the earliest observed evaluation year is always dropped from `pe.eval`. That year has no in-window predecessor for the naive step.
- Prediction residuals are appended newest first (`endyrvec` is descending). A residual exists for every observed year among `endyrvec[1..n−1]`.
- If the earliest evaluation year `min(endyrvec)` is observed, the two vectors have equal length and line up.
- If it is not observed (gappy or multi-year surveys), `pred.resid` has one extra element. L226 removes element 1, which is the **newest** residual. The residual that should go is the oldest one.

On `Simple` (`SURVEY1` observed in 1977, 1980, …, 1998, 2001; evaluation years 1996–2001):

- The prediction residuals are 2001: log(28068.9/37338.3) = −0.285 (peel ending 2000), and 1998: log(29011.2/27492.6) = +0.054 (peel ending 1997).
- The naive step is log(37338.3/27492.6) = 0.306.
- The code keeps +0.054 and labels it 2001, giving **MASE = 0.176**. Using the 2001 residual gives 0.932.
- With n = 1 either value is fragile, but the defect changes which forecast is scored.
- For annual `SURVEY2` (n = 5, MASE 0.711) and the biennial `Hake_2018` acoustic index (evaluation years 2013, 2015 and 2017 observed, 2012 observed; MASE 1.106), the lengths match and no misalignment occurs.

### 6. Management strategy evaluation: guidance and the SSMSE implementation

**Best practice** (Punt et al. 2016; Basis: papers):

- Steps:
  1. objectives and performance statistics;
  2. a broad set of uncertainties;
  3. operating models (OMs), "more than a single operating model is nearly always required";
  4. conditioning and parameter uncertainty, ideally Bayesian posteriors;
  5. candidate strategies;
  6. closed-loop simulation;
  7. summary.
- The minimum uncertainty set is process (recruitment), parameter (productivity and size) and observation error. Divide trials into reference and robustness sets.
- Test the software with "perfect" data. Simulate the actual assessment: ICES found only 4 of 18 MSEs did.
- Include Exceptional Circumstances.
- Compute cost example: "100 simulations of 45 years … took over 3 weeks on a fast desktop computer".

**SSMSE implementation** (`nmfs-ost/SSMSE@4d858d8`; Basis: source + JOSS paper):

- `run_SSMSE()` (`R/runSSMSE.R` L71–94) defaults to `MS_vec = c("EM", "no_catch", "Interim")`, `use_SS_boot_vec = TRUE`, `n_F_search_loops = 20`, `tolerance_F_search = 0.001` and `run_parallel = FALSE`. The iteration default is `nyrs_assess = 3` (L499).
- `run_SSMSE_iter()` (L489–796):
  - creates the OM from a conditioned SS3 model (`create_OM`);
  - samples data by SS3 parametric bootstrap (`use_SS_boot`; Methot & Wetzel: "contain measurement error only and do not randomize any of the process … error");
  - runs the management strategy (`parse_MS`);
  - loops `for (yr in assess_yrs)` with `assess_yrs <- seq(styr_MSE, styr_MSE + nyrs, nyrs_assess)` (L656–667). Each pass extends the OM with catch (`update_OM`) and re-samples.
- The **EM strategy** fits an SS3 estimation model and takes catch from its forecast file. Assessment error therefore comes out of the estimation itself.
- **Implementation error** defaults to `data.frame(year, "error" = rep(1, nyrs))` (`R/initOM.R` L308–311). `update_OM` applies it multiplicatively only when `temp_impl_error >= 0` (`R/extendOM.R` L259–264). A negative value is silently ignored, not rejected.
- Process change in the projection is set through `future_om_list` (`R/future_om.R`). `pattern` is `"model_change"` (default distribution `"normal"`) or `"custom"`, and `scen` is `"randomize"` or `"replicate"`. `pars` names SS parameters, `"rec_devs"` or `"impl_error"`.
- `R/example_perf_metrics.R` provides total, average, SD and CV of catch and average absolute or relative SSB.

| Punt et al. element | SSMSE support (source) |
|---|---|
| Multiple OMs / reference and robustness sets | Multiple scenarios via `OM_name_vec`; the split into sets and the plausibility ranking are not implemented (user organizes them) |
| Conditioning OMs to data | Not performed; the OM is an existing fitted SS3 model |
| Parameter uncertainty (posterior draws) | Not built in; process deviations via `future_om_list` |
| Observation error | SS3 bootstrap data (measurement error only) |
| Simulating the actual assessment | Yes (`EM` strategy) |
| Implementation error | Yes, multiplicative, default 1 |
| Perfect-data software test | Not available: `use_SS_boot = FALSE` stops with "Currently, only sampling can be done using the bootstrapping capabilities within SS3" (`R/runSSMSE.R` L608–613, L713) |
| Performance statistics | Example functions; user-defined |
| Exceptional Circumstances | Not represented |

### 7. Performance and resource footprint across six levels

| Level | SS3 assessment / retrospective | r4ss / ss3diags diagnostics | SSMSE |
|---|---|---|---|
| L1 authoring / maintenance | ≈ 20,000 ADMB lines in 2013 (cited); current LoC not measured | not measured | not measured |
| L2 toolchain build | not measured (used the released static binaries: `ss3_linux` 6,978,600 B, `ss3_opt_linux` 6,770,304 B) | not applicable (R not installed; not measured) | not measured |
| L3 model fit latency | `Simple`, with Hessian: 32.4–36.2 s per fit (safe build, 6 runs), 29.43 s (optimized build, 1 run). Without Hessian (`-nohess`): 6.57 s. `Hake_2018`: 24.5–37.9 s. Five-peel retrospective = 6 fits ≈ 3.4 min serial (measured) | transcribed formulas run in < 1 s on parsed output (measured, Python) | "may take hours or days" (cited); not measured |
| L4 executable throughput | same as L3; the Hessian accounts for ≈ 81 % of a `Simple` fit (derived: (34.78 − 6.57)/34.78) | – | – |
| L5 diagnostic checking cost | retrospective + hindcast reuse the same peels, so HCxval adds no fits (Carvalho et al.) | – | per-iteration EM fits; not measured |
| L6 memory / disk | peak RSS 350–354 MB per `Simple` fit with Hessian, 177 MB without; 162–167 MB for `Hake_2018` (measured); `Report.sso` ≈ 1.1 MB (test-model copy, cited size from the repository tree) | not measured | not measured |

### 8. Comprehensibility and simplicity

**C1 (comprehensibility):**

- **One name, three numbers.** One label, "Mohn's rho", is attached to three numbers that differ by a factor of P. A reviewer checking "ρ = −0.84" against a [−0.15, 0.20] rule cannot tell which variant produced it without reading the code. The r4ss documentation states the difference, but the list element named `SSB` is the summed form.
- **Mislabelled residual years.** The `SSmase` residual table labels years incorrectly in the gappy case. This breaks the diagnostic's own explanation of itself: the "Year" column is the reader's audit trail.
- **The control rule cannot be read off the inputs.** SS3's `H4010` rule uses one ramp formula and four policy variants. Whether a buffer applies to F or to catch is encoded in a single integer, and the logistic smoothing is not visible in the inputs.

**C2 (simplicity):**

- **One estimand, many conventions.** The core estimand is the relative revision of a terminal-year estimate. A single per-peel vector with an explicit aggregator (mean, sum, all-years) would make every variant an ordinary case and expose P. The current set of named scalars hides it.
- **One table instead of positional arrays.** Similarly, MASE needs a single table of (evaluation year, prediction residual, naive residual) built by joining on year. Two independently trimmed positional vectors create the misalignment.
- **Smoothing in physical units.** The HCR join would be scale-free if its slope were expressed per unit of `HCR_anchor`. At present the smoothing width carries a hidden dependence on spawning-output units.

### 9. How implementations and claims are validated

- **V1 (specification adequacy and non-vacuity):**
  - Retrospective ρ has a known false-positive rate (10 %) and is non-diagnostic of bias (Hurtado-Ferro). Kell et al. warn that "the best way to remove a retrospective pattern is to ignore the data". Prediction skill (MASE) is the cookbook's falsifiable test.
  - The `SSmase` defect shows that the diagnostic code itself needs a golden test with a gappy index, which neither pinned ss3diags revision applies to this case (not examined beyond `SSmase.R`).
  - The SS3 error-type −2 path is a specification gap: documented, accepted at read time, unimplemented.
- **V2 (implementation cross-checks):**
  - Our Python transcriptions of `SSmohnsrho` and `SShcbias` agree with each other (mean form).
  - They were not checked against R output, because R was not run.
  - SS3's parametric bootstrap supports self-test simulations (Punt et al. test 2), but SSMSE cannot yet run them with error-free expected values. The ss3sim framework used by Hurtado-Ferro et al. is the canonical simulation harness.
- **V3 (concurrency, crash, silicon): known not to apply** to single-process ADMB fits. Parallel retrospectives (`furrr::future_walk` in `retro.R`) and SSMSE `run_parallel` write separate directories. We did not test them.
- **V4 (falsification against reality, human comprehension):**
  - Hindcast MASE against reserved observations is the only reality-facing check in the cookbook.
  - The northern cod record is the archetypal failure, in which commercial CPUE stayed high while abundance fell.
  - MSE's Exceptional Circumstances provisions are the runtime monitor that triggers when future data leave the simulated envelope (Punt et al.). SSMSE does not implement them.

## Boundaries

- **Not examined:**
  - full texts of Hutchings & Myers 1994, Walters & Maguire 1996, Mohn 1999, Kell et al. 2016, Brooks & Legault 2016 and Deroba 2014. Claims about DFO averaging commercial and survey indices, or about F exceeding F0.1 two- to threefold, circulate in secondary sources and are **not** asserted here;
  - Harris (1990) and other review panels;
  - r4ss `SS_output.R`;
  - ss3diags runs test and ASPM code;
  - SS3 Dirichlet-multinomial, tag and other likelihood code beyond the lines cited;
  - SSMSE execution.
- **Unknown:**
  - why SS3 exits for survey error type −2;
  - whether r4ss's default `endyrvec` matches SS3's reported `endyrs` for retrospective runs;
  - whether R's `SSmase` yields exactly our transcribed values (high confidence from the code, but not executed);
  - whether ss3diags' plotting function `SSplotHCxval` shares the `SSmase` trimming.
- **Known not to apply:**
  - Our ρ values are for test models with fixed configurations, not official assessments.
  - Hurtado-Ferro ranges are calibrated on SSB in simulated cod, flatfish and sardine and do not transfer to recruitment ρ.
- **Not measured:**
  - L1 authoring effort;
  - SS3 build time from source;
  - R-package run times and memory;
  - SSMSE cost;
  - energy use.
- **Unsupported by the evidence:**
  - "ρ inside the range means the assessment is unbiased" (Hurtado-Ferro: unrelated to bias);
  - "MASE < 1 from one evaluation point demonstrates skill";
  - "SSMSE implements Punt et al. best practice end-to-end";
  - "the northern cod collapse was caused by the retrospective problem" (Mohn's analysis concerns eastern Scotian Shelf cod).

## Evidence

Observation date for all evidence: 2026-11-21 (UTC). On that date the GitHub pins were resolved and source read; the SS3 runs were executed; and every DOI below was checked against Crossref for title, authors, journal, volume and pages.

**Source** (path:line at the pinned commit):

- `nmfs-ost/ss3-source-code@94cea415b5861104289c6fa80e2737c94b090487`:
  - `SS_objfunc.tpl` L15–25, L120–160, L611–630, L745–809, L1059–1110;
  - `SS_benchfore.tpl` L2125–2160, L2282–2313, L2470–2479, L2776–2845;
  - `SS_readdata_330.tpl` L676, L686–707;
  - `SS_readcontrol_330.tpl` L3110–3132;
  - `SS_expval.tpl` L207.
- `nmfs-ost/ss3-source-code@25bab0242fe1ac044db2bd7eb08f7f3613016ad9` (tag v3.30.26): release assets `ss3_linux` (SHA-256 `e186c2691a645e340d644127cade04df53e10d77219608ad00665513401ba10b`) and `ss3_opt_linux` (SHA-256 `72277f7b405825fca6a73ce652c0e306d4d9918e93a8dddfa89ce222dce14c31`); both are statically linked x86-64 ELF.
- `nmfs-ost/ss3-test-models@236171c9bc084a4e380731ca446fc9220f5c8a46`: `models/Simple/*`, `models/Hake_2018/*`.
- `r4ss/r4ss@c5d7e20b484b91f3080eeb9d9cddc0127948b460`:
  - `R/SSmohnsrho.R` L53–180;
  - `R/retro.R` L111–123, L428–596;
  - `R/run.R` L42–45;
  - `R/SSsummarize.R` L440–513.
- `jabbamodel/ss3diags@e15da7a22f91141248286104bdfa3f9cf7895814`: `R/SShcbias.R` L16–118; `R/SSmase.R` L25–237.
- `nmfs-ost/ss3diags@d8773e0ac9040e9f8771596a1db54945760f923f`: `R/SSmase.R` L170–240; `DESCRIPTION` (Version 2.2.2).
- `nmfs-ost/SSMSE@4d858d884a77bf34549ac5f19633f83be600eee8`:
  - `R/runSSMSE.R` L71–94, L265–289, L489–796 (L608–613 bootstrap-only stop);
  - `R/future_om.R` L18–101;
  - `R/initOM.R` L300–316;
  - `R/extendOM.R` L245–280;
  - `R/MS_functions.R` L20–141;
  - `R/example_perf_metrics.R`.

**Execution:**

- Environment: x86-64 Linux, Intel Xeon @ 2.60 GHz, 96 logical CPUs; times from `/usr/bin/time -v`.
- Command: `python3 support/ss3_retro_probe.py <ss3_linux> <model_dir> <work_dir> 5`.
- Outputs: `support/simple_retro_results.json` and `support/hake2018_retro_results.json`.
- The error-type −2 probe edited `Simple/data.ss` line `2 1 0 1 # SURVEY1` to `2 1 -2 1 # SURVEY1` and ran `ss3_linux -nohess`.
- The speed comparisons were single runs.

**Papers:**

- Hutchings & Myers 1994, CJFAS 51(9):2126–2146, `10.1139/f94-214` (abstract).
- Walters & Maguire 1996, Rev. Fish Biol. Fish. 6:125–137, `10.1007/BF00182340` (publisher abstract; Crossref has no pages).
- Mohn 1999, ICES JMS 56(4):473–488, `10.1006/jmsc.1999.0481` (abstract).
- Methot & Wetzel 2013, Fish. Res. 142:86–99, `10.1016/j.fishres.2012.10.012` (Sects. 2–4, Table 1).
- Hurtado-Ferro et al. 2015, ICES JMS 72(1):99–110, `10.1093/icesjms/fsu198` (Methods, Results, Discussion, Table 3).
- Punt et al. 2016, Fish Fish. 17(2):303–334, `10.1111/faf.12104` (read in the 2014 Early View version; Table 1).
- Kell, Kimoto & Kitakado 2016, Fish. Res. 183:119–127, `10.1016/j.fishres.2016.05.017` (abstract).
- Kell et al. 2021, ICES JMS 78(6):2244–2255, `10.1093/icesjms/fsab104` (Eqs. 1–5).
- Carvalho et al. 2021, Fish. Res. 240:105959, `10.1016/j.fishres.2021.105959` (Sects. 2–3, Table 1).
- Legault 2020, ICES JMS 77(7–8):3016–3030, `10.1093/icesjms/fsaa184`.
- Doering et al. 2023 (SSMSE), JOSS 8(90):4937, `10.21105/joss.04937` (read in the repository copy of `paper.md`).
- Brooks & Legault 2016, CJFAS 73(6):935–950, `10.1139/cjfas-2015-0163` (abstract).
- Deroba 2014, NAJFM 34(2):380–390, `10.1080/02755947.2014.882452` (abstract).

## Revalidation

- **ρ variants:** Re-read `R/SSmohnsrho.R` L160–177. If `mohn.out[["SSB"]] <- sum(mohnSSB)` persists, the scale caveat holds. In R, `SSmohnsrho(SSsummarize(SSgetoutput(dirvec = retro dirs)))` on the `Simple` peels should reproduce `SSB` = −0.840 and `AFSC_Hurtado_SSB` = −0.168, provided the peels are re-run with v3.30.26.
- **`SSmase` defect:** In the current ss3diags, check whether L226 still reads `pred.resid[-1]`. Then run `SSmase(retroSummary, quants = "cpue", indexselect = <SURVEY1>, residuals = TRUE)` on the `Simple` peels. A `Residuals` row with Year = 2001 and Pred.Res ≈ +0.054 confirms it; ≈ −0.285 means it is fixed.
- **SS3 objective function and HCR:** Diff `SS_objfunc.tpl` L120–160 and L1059–1110, and `SS_benchfore.tpl` L2776–2845. To test error type −2, rerun the one-line `data.ss` edit with the new binary.
- **SSMSE:** Diff `R/runSSMSE.R` signatures and `R/extendOM.R` L254–264.
- **Retrospective numbers:** Rerun `support/ss3_retro_probe.py` against a new SS3 release. Fits are deterministic for fixed inputs, so ρ should match to printed precision unless the estimation changed.
