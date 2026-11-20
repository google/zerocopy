# Bulletin 17C flood frequency: the expected moments algorithm, the multiple Grubbs–Beck low-outlier test, open implementations (MGBT, Cohn's EMA source, lmomco, lmom, lmoments3) on the same gauge records, and nonstationary return period and risk

## Summary

- **What Bulletin 17C prescribes** (England et al. 2018, v1.1 2019).
  - The distribution is log-Pearson Type III (LP3) on base-10 logarithms of annual peaks. It is fitted by the expected moments algorithm (EMA), a generalized method of moments that iterates expected moments of interval, censored and historical observations until convergence.
  - Potentially influential low floods (PILFs) are identified by the multiple Grubbs–Beck test (MGBT). Zeros are always PILFs, and each PILF is recoded as an interval "< T_PILF".
  - Skew is a weighted average of station and regional skew, weighted by mean square error (MSE). Regional skew comes from Bayesian WLS/GLS regression and replaces the Bulletin 17B skew map.
  - Confidence intervals follow Cohn et al. (2001) and include skew uncertainty.
  - The guideline applies to AEP < 0.10 and records of at least 10 years. It states that "Time invariance was assumed" and excludes watersheds with "hydrologic nonstationarities".

  *Basis: normative.*
- **MGBT as implemented in R package MGBT 1.1.8.** The user-level `MGBT()` dispatches to `MGBT17c()`. In execution it reproduced the USGS-PeakFQ v7.1 thresholds quoted in its own documentation: 284 cfs (p = 0.0119 versus PeakFQ's 0.0123), 185 cfs, and 16 PILFs at 1110 cfs.
  - The single-loop rule used by T. A. Cohn's R versions (`MGBTcohn2016`, `MGBTcohn2013`, and the `MGBT()` inside the shipped EMA source `P3_089(R).txt`) keeps extending the PILF count at α = 0.10 past the last α_out = 0.005 hit. It returned 24 or 35 PILFs where PeakFQ reports 16. On the 10 gauge records examined, it disagreed with `MGBT17c` on 2: 35 versus 32 for 05405000 and 23 versus 20 for 08190000. Feeding EMA the `MGBT17c` threshold instead of its own changed Q(AEP 0.01) by −3.9% and −27.2%.

  *Basis: source + execution.*
- **Defects in MGBT 1.1.8 `R/MGBT.R`, demonstrated by execution.**
  1. `mgbt.sweeper` line 437 reads `for(i in j1+1:n2)`. Because `:` binds tighter than `+`, this iterates `j1+1, …, j1+n2`. With the default `alphain = 0` the loop exits on its first pass. With `alphain > 0` it indexes past the p-value vector and fails with `missing value where TRUE/FALSE needed`.
  2. The inward sweep's `j3` stays 0 when no tested p-value reaches `alphazeroin`. For p = (0.001, 0.002, 0.008, 0.009) the sweeper returns 2 where the single-loop rule returns 4. This was shown on synthetic p-value vectors only, and it is a defect only under the reading noted in §3.
  3. `MGBT17c.verb` returns 0 PILFs where `MGBT17c` returns 5 on the 11-value record quoted in the source (j1 becomes −1).

  *Basis: source + execution.*
- **L-moment GEV fits agree to machine precision across three implementations.** lmomco, lmom and lmoments3 agree to ≤ 7.2×10⁻¹⁵ relative in Q(AEP 0.01) on all 10 records. The real-space GEV fit is nearly insensitive to the smallest flood: dividing it by 10 moved Q(AEP 0.01) by 0.0–2.6%. The same perturbation moved a plain method-of-moments LP3 by −20% to −52%, an L-moment LP3 on logs by −9% to −16%, and EMA+MGBT by 0 to −1.5% whenever its PILF test completed (it failed on 2 of the 10 perturbed records). Choosing `MGBT17c` instead of Cohn's single-loop MGBT changed the EMA Q(AEP 0.01) by −3.9% on 05405000 and −27.2% on 08190000. *Basis: execution.*
- **Robustness evidence.** Lamontagne et al. (2016) report Monte Carlo evidence that MGBT censoring improves EMA's extreme-quantile efficiency for negatively skewed LP3, has little effect for zero or positive skew, and protects against lower-tail misspecification. Cohn et al. (1997) found EMA more efficient than Bulletin 17B's historical weighting and "nearly as efficient as" maximum likelihood. England et al. (2003) found EMA better than the Bulletin 17B historical procedure "in nearly all cases". *Basis: documentation.*
- **Nonstationarity.** Milly et al. (2008) argue that stationarity can no longer be assumed. Olsen et al. (1998), Salas and Obeysekera (2014), Rootzén and Katz (2013) and Read and Vogel (2015) redefine return period and risk using year-specific exceedance probabilities `p_t`. In a toy model in which all flows grow 0.5% per year (not fitted to any river), the stationary 100-year flood has an expected waiting time of 59.7 years and a 50-year risk of 0.482 instead of 0.395. Keeping the stationary risk needs a 14.1% larger design flood. *Basis: documentation + execution (toy model).*

## Applicability

- **R packages**, installed with `R CMD INSTALL` from the GitHub tarballs of the pinned revisions into R 4.5.3 (conda-forge build) on Linux x86-64:
  - **MGBT** at `cran/MGBT` `0994615648a373bd7beb3cf7ebecb19e9edd948c`, version 1.1.8 (CRAN mirror; DESCRIPTION Date 2026-10-04). Tarball sha256 `b5e1930e…6925`.
  - **lmomco** at `wasquith/lmomco` `9d49f0a2e6fe1d687af82efe63d4a73caca82b04`, version 2.5.8. Tarball sha256 `bae9c5ce…b6e6`.
  - **lmom** at `cran/lmom` `252d9635c3acaf452d4d497fab2da01fa1edfcd8`, version 3.3. Tarball sha256 `d5a75771…cb54`.

  `statmod`, `numDeriv`, `goftest`, `Lmoments` and `MASS` came from conda-forge.
- **lmoments3** at `OpenHydrology/lmoments3` `7e19f97c23019ca68cbd526b8bd417c412438f1c` (last commit 2021-05-04) ran from source under CPython 3.13.15 with numpy 2.5.4 and scipy 1.18.1.
- **EMA.** `inst/sources/P3_089(R).txt` in the MGBT revision is T. A. Cohn's last R implementation of EMA, LP3 and MGBT (edited "as late as the summer of 2016"; `MGBT-package.Rd` line 19). The package states that "any code related to B17C herein must not be considered canonical in any way". It was sourced verbatim into a fresh R session. EMA results here are those of this archived source, **not** of USGS-PeakFQ or HEC-SSP, neither of which was examined.
- **Bulletin 17C** v1.1 (May 2019) was read as text extracted from `https://pubs.usgs.gov/tm/04/b05/tm4b5.pdf`. The extraction stops in the References (printed p. 40). Appendixes 6 (MGBT computational details), 7 (EMA equations, confidence intervals) and 10 (worked examples) were **not examined** directly. Statements about them come from the MGBT package's quotations, labelled as such.
- **Gauge records.** All are systematic annual peaks only, with historical peaks (NWIS code 7) and missing values dropped:
  - two records quoted verbatim in `MGBT.Rd` (USGS 08066300, n = 51; 08385600, n = 58, which includes one zero);
  - the record labelled 08165300 in `MGBT-package.Rd` (n = 49). Its URL comment points to site 08385600, apparently a copy error in that documentation;
  - eight datasets bundled in lmomco: 01515000, 02366500, 05405000, 08151500, 08167000, 08190000, 09442000 and 14321000.

  Station names were not verified and are not used. No regional skew was applied, so results are *station-skew* fits and are not Bulletin 17C final estimates for those sites.

## Findings

### 1. The Bulletin 17C procedure

| Step | Bulletin 17C requirement (main text) | Where implemented in the examined code |
|---|---|---|
| Data model | Each year is an interval `[Q_Y,lower, Q_Y,upper]` with perception thresholds `[T_Y,lower, T_Y,upper]`. The thresholds are needed for confidence intervals, not for the moments | `P3_089` `makeFLOODdata(ql, qu, …)`, `makeQTL` |
| Distribution | LP3 on log10 Q (Bulletin 15 onward). EMA reverts to ordinary moments "for the simple data situation" | `P3_089` `qP3`/`pP3` (cubic-spline smoothing in skew) |
| Fitting | EMA steps 1–5 (eqs 14–20): initial moments from above-threshold values, P-III parameters `α = 4/γ²`, `β = σγ/2`, `τ = μ − αβ`, expected moments of censored years, iterate to convergence | `P3_089` `.p3mombin` loop (`while(((mo-m)%*%(mo-m))>1e-11)`), `.emoms`, `.momsadj`, `.momsp3` |
| Low outliers | MGBT on systematic peaks. PILFs and zeros recoded as `< T_PILF` and treated as interval data. "For the case of a single low outlier, the MGBT is identical to the Grubbs-Beck test". The analyst may override with hydrologic judgment if documented | MGBT `MGBT17c`. `P3_089` `MGBTest` (its own single-loop `MGBT`) |
| Skew | weighted `G̃` from station skew and regional G by their MSEs, assuming G is unbiased and independent of station skew. Examine data if they differ by > 0.5 | `P3_089` `.momsp3`: `m[3] <- (asmse*rskew + rmse*m[3])/(asmse+rmse)` with `asmse` from `.mseg` |
| Regional skew | B-WLS/B-GLS regression (Reis et al. 2005; Veilleux et al.), replacing the Bulletin 17B plate 1 map | not in examined code |
| Confidence intervals | Cohn et al. (2001), including skew uncertainty | `P3_089` `.ci_ema_03`: "the 'adjusted' CI formula in Cohn, Lane and Stedinger [WRR, 2001]". Default `eps = 0.90` |
| Record extension | MOVE (Hirsch 1982) when the short record is < 20 years, with ≥ 10 years overlap | not examined |
| Scope | at least 10 years of record. AEP < 0.10 (for more common floods, partial-duration series). Not for "reservoir regulation, watershed changes, or hydrologic nonstationarities" | — |

*Basis: normative + source.*

Two source observations on `P3_089`:

- `.mseg` (lines 939–943) is the Bulletin 17B station-skew MSE approximation `10^(A − B·log10(n/10))`. Bulletin 17C says "The MSE of the station skew is computed directly by EMA". With `RegionalSkew = -99` (no regional skew) `ema()` sets `rmse <- 1e20`, so `asmse` has no effect, and none of the runs below depend on it.
- `makeEMAresult(o, LowOutlierTest = "none")` fails with `'LowOutlierTest' is not a slot in class "FLOODdata"`. Lines 462–465 assign `o@LowOutlierTest` to the uncoerced `FLOODdata` input when neither `"GBT"` nor `"MGBT"` is chosen. The probe coerces to `EMAresult` first.

*Basis: source + execution.*

### 2. The multiple Grubbs–Beck test: definition and implementations

With sorted log10 peaks `X[1:n] ≤ … ≤ X[n:n]` and `n2 = floor(n/2)`, the statistic for the r-th smallest is

```text
ω_r = (X[r:n] − mean(X[r+1:n … n:n])) / sd(X[r+1:n … n:n]),      r = 1..n2
p_r = P(ω_r ≤ observed | n iid normal)    # RthOrderPValueOrthoT: integrate(peta, ...) over the r-th order statistic,
                                           # noncentral-t approximation; Monte Carlo fallback if integrate() fails
```

The sweep rule follows `MGBT-package.Rd` and the quotation of Bulletin 17C at `MGBT.R` lines 105–107: "the number of low outliers identified by [MGBT] is the larger of k and m-1". The outward sweep starts at `r = n2` and moves toward `r = 1`. It stops at the first `p_r < α_out = 0.005`, giving k. The inward sweep starts at `r = 1` and stops at the first `p_r ≥ α_in = 0.10` (called `alphazeroin` in the package), at position m. The PILF threshold is `X[(K+1):n]`, where K = max(k, m−1). Zeros become `1e-8` before taking logs (`log10(pmax(1e-8, x))`), and the code assumes they will always be flagged. *Basis: normative (as quoted) + source.*

| Function in `R/MGBT.R` | Rule | Status per package docs |
|---|---|---|
| `MGBT()` → `MGBT17c()` (lines 1, 379–426) | all `ω`, `p` computed. `mgbt.sweeper` (429–446) gives `max(j1, j2, j3)` | "THE function for end users" |
| `MGBT17c.verb()` (317–373) | literal two-loop sweeps "as per 17C" | backstop |
| `MGBTcohn2016()` (25–115), `MGBTcohn2013()` (145–206) | single loop: `if(p<αout){j1<-i;j2<-i}; if(p<αzeroin & j2==i-1) j2<-i`. 2013 adds recursion with `n2=n-5, αout=0.01` when `j2 == n2` | "retained for historical reference and are not intended for deployment" (lines 463–464) |
| `MGBTnb()` (259–308) | sweep-out only, plus a test of `p[1]` | historical |
| `P3_089` `MGBT()` (lines 627–639) | same single loop as `MGBTcohn2016`, without NA handling | used by `P3_089`'s `MGBTest` |

**Measured PILF counts** (`support/flood_probe_lmom_mgbt.R` and `support/mgbt_defects.R`):

| Record | n | min | `MGBT17c` K / threshold | `.verb` | `cohn2016` | `cohn2013` | `nb` | PeakFQ v7.1 (quoted in MGBT docs) |
|---|---|---|---|---|---|---|---|---|
| 08066300 | 51 | 55 | 1 / 284 | 1 | 1 | 1 | 1 | 1 / 284 (p 0.0123) |
| 08385600 | 58 | 0 | 2 / 185 | 2 | 2 | 2 | 2 | threshold 185 |
| "08165300" | 49 | 21 | 16 / 1110 | 16 | **24 / 3200** | **35 / 16600** | 16 | 16 / 1110 |
| 05405000 | 73 | 710 | 32 / 2500 | 32 | **35** | **35** | 32 | not available |
| 08190000 | 84 | 78 | 20 / 2220 | 20 | **23** | **23** | 20 | not available |
| 14321000 | 100 | 13100 | 9 / 51000 | 9 | 9 | 9 | **3** | not available |
| 02366500 | 75 | 6810 | 1 / 12400 | 1 | 1 | 1 | 1 | not available |
| 01515000, 08151500, 08167000, 09442000 | 71, 67, 69, 85 | — | 0 | 0 | 0 | 0 | 0 | not available |

The 08066300 p-value for 55 cfs was 0.01192, against PeakFQ's 0.0123. The package attributes such gaps to numerical integration. The single-loop over-count happens when the p-values just above the last `α_out` hit stay below 0.10. For "08165300", p₁₇…p₂₄ are 0.012–0.048 (listed in `MGBT-package.Rd` lines 71–74). *Basis: execution + documentation.*

### 3. Three defects in `R/MGBT.R` (MGBT 1.1.8)

Quoted source lines:

```r
434:   for(i in seq(n2,1,-1)) if(pvs[i] <    alphaout) { j1 <- i;  break }
435:   if(j1 < n2) { # Late addition station 08020500 causes j1 to be n2 [A WHA fix to TAC.]
437:      for(i in j1+1:n2) if(pvs[i] >=     alphain) { j2 <- i-1; break }
443:   for(i in         1:n2) if(pvs[i] >= alphazeroin) { j3 <- i-1; break }
...
347:   for(i in seq(n2,1,by=-1)) { # NOTE LITERALLY SWEEP OUT as per 17C
352:      if( pv >= alphaout) { j1 <- i; next } # effect of sweep out, NOTE GREATER THAN EQUAL
353:      break
356:   j1 <- j1 - 1 # this is critical!
```

1. **Operator precedence (line 437).** R evaluates `j1+1:n2` as `j1 + (1:n2)`. The probe printed `3 4 5 6` for `j1 = 2, n2 = 4`, where `(j1+1):n2` would give `3 4`. With the default `alphain = 0` the first test `pvs[j1+1] >= 0` is always true, so this is latent. For `pvs = c(0.001, 0.002, 0.008, 0.009)`, `MGBT:::mgbt.sweeper(pvs, alphaout=0.005, alphain=0.01, alphazeroin=0.10)` stopped with `missing value where TRUE/FALSE needed` instead of returning `j2 = 4`. `MGBT17c` forwards `alphain` to the sweeper (line 417).
2. **Inward sweep never sets `j3` when every p-value is below `alphazeroin` (line 443).** `j3` keeps its initial 0. For p = (0.001, 0.002, 0.008, 0.009) and (0.001, 0.002, 0.030, 0.050), the sweeper returned `index = 2` (sweeps 2, 2, 0). The single-loop rule gives 4. The quoted "larger of k and m−1" also gives 4 if m−1 is read as n2 when every tested p-value is below α_in, a case the quotation does not state. This is demonstrated on synthetic p-value vectors. No examined gauge record triggered it.
3. **`MGBT17c.verb` when `p[n2] < α_out` (lines 347–356).** The loop breaks before setting `j1`, so `j1 − 1 = −1`. On the 11-value record quoted in the comment at line 436 (p = 0.2862, 0.215, 0.1069, 0.08494, 0.004018), `MGBT17c` returned K = 5 with threshold 15200, while `MGBT17c.verb` returned K = 0 (sweeps `-1 NA 0`). The user-level function has the fix ("A WHA fix to TAC") and the backstop does not.

*Basis: source + execution.* None of the three affects `MGBT()` with default arguments on the examined records.

### 4. Same records, different estimators

All Q(AEP 0.01) values are in cfs. Station skew only. GEV fits are by L-moments (`pargev`/`pelgev`/`gev.lmom_fit`). L-moment LP3 means `parpe3(lmoms(log10 Q))`. MOM-LP3 is a plain method-of-moments LP3 with Bulletin-17B-style bias-corrected skew and no low-outlier treatment.

| Record | MOM-LP3 | lmomco GEV | lmom GEV | lmoments3 GEV | L-moment LP3 |
|---|---|---|---|---|---|
| 08066300 | 16,121 | 20,077 | 20,077 | 20,077.5 | 17,763 |
| 08385600 | 14,775 (zero excluded) | 19,241 | 19,241 | 19,240.5 | 18,184 (zero excluded) |
| 01515000 | 146,710 | 150,480 | 150,480 | 150,483 | 155,700 |
| 02366500 | 116,080 | 126,270 | 126,270 | 126,272 | 113,010 |
| 05405000 | 8,530.1 | 8,426.3 | 8,426.3 | 8,426.27 | 8,573.2 |
| 08151500 | 355,630 | 315,500 | 315,500 | 315,504 | 329,510 |
| 08167000 | 262,100 | 212,490 | 212,490 | 212,487 | 251,770 |
| 08190000 | 433,000 | 303,160 | 303,160 | 303,161 | 338,790 |
| 09442000 | 49,670 | 54,963 | 54,963 | 54,963.3 | 53,884 |
| 14321000 | 215,410 | 260,860 | 260,860 | 260,855 | 240,720 |

The largest relative difference between lmomco and lmom GEV was 4.7×10⁻¹⁴, and between lmoments3 and lmomco 7.2×10⁻¹⁵. All three implement Hosking's rational approximation for the GEV shape from τ₃ (lmoments3 `distr.py` lines 1055–1125). *Basis: execution.*

Sourcing `P3_089` runs its embedded "Big Sandy Test Dataset". This is 77 water years (1897–1973) with historical years coded as intervals below 18,500 cfs, a regional skew of −0.5 and a regional-skew MSE of 0.3025. Every run printed the same table: weighted skew −0.1124 and Q(AEP 0.01) = 23,600 cfs [18,500, 35,000]. This works as a golden specimen for EMA with historical data, but no independent published answer for it was located.

EMA with MGBT, from Cohn's `P3_089` (station skew; 90% interval from `makeEMAresult`'s default `eps = 0.90`):

| Record | PILFs from `P3_089`'s own MGBT / threshold | station skew (log space) | Q(AEP 0.01) | 90% interval | Q(AEP 0.002) | EMA with no PILF test |
|---|---|---|---|---|---|---|
| 01515000 | 0 | +0.070 | 146,715 | 127,734 – 187,847 | 178,893 | 146,715 |
| 02366500 | 1 / 12,400 | +0.408 | 122,773 | 96,383 – 196,207 | 179,845 | 116,082 |
| 05405000 | **35 / 2,810** | −0.588 | 7,917 | 6,593 – 10,063 | 9,336 | 8,530 |
| 08066300 | 1 / 284 | −0.392 | 19,546 | 13,190 – 37,756 | 29,010 | 16,121 |
| 08151500 | 0 | −0.532 | 355,627 | 224,959 – 676,420 | 548,691 | 355,627 |
| 08167000 | 0 | −0.309 | 262,097 | 155,369 – 596,390 | 485,694 | 262,097 |
| 08190000 | **23 / 4,130** | −0.290 | 377,241 | 217,722 – 862,938 | 763,980 | 433,000 |
| 08385600 | error: "the integral is probably divergent" | — | — | — | — | 5.51×10⁹ (zero entered as 1e-20) |
| 09442000 | 0 | +0.106 | 49,670 | 35,206 – 89,848 | 84,694 | 49,670 |
| 14321000 | 9 / 51,000 | −0.031 | 263,412 | 225,826 – 336,686 | 335,741 | 215,413 |

**The MGBT variant changes the design flood.** Re-running EMA with `P3_089`'s exact censoring edits (`MGBTest`), but at the threshold returned by `MGBT17c`, gave the following (`support/flood_probe_ema_fixed_threshold.R`):

- 05405000: 32 PILFs below 2,500 cfs give Q(AEP 0.01) = 7,607 [5,868, 9,727]. This is −3.9% against the 35-PILF value.
- 08190000: 20 PILFs below 2,220 cfs give 274,539 [130,589, 557,278]. This is **−27.2%** against the 23-PILF value of 377,241.
- 08066300, 02366500 and 14321000, where the two rules agree, reproduce the table values exactly. This checks that the re-run is faithful.

Other observations from the same runs:

- **Simple case.** With no PILFs and a systematic-only record, EMA equals the method-of-moments LP3 to the printed precision on all nine records with positive minima. This confirms Bulletin 17C's statement that EMA "returns the standard method of moments estimates" in the simple case.
- **Unpatched p-value integration.** `P3_089`'s MGBT stops with `integrate()` "the integral is probably divergent" on 08385600 (as `MGBT.Rd` documents for these data) and on the perturbed 08151500 and 08167000 records. `MGBT17c` evaluated the same data through its Monte Carlo fallback.
- **Zeros.** Without censoring, a zero flow entered as 1e-20 drives the log-space moments to 5.5×10⁹ cfs. This is why Bulletin 17C defines zeros as PILFs.

*Basis: execution.*

**Sensitivity to one low flood.** Each column shows the change in Q(AEP 0.01) when the smallest observation is divided by 10. For 08385600 the minimum is 0 and stays 0, so all methods show 0.0%.

| Record | EMA + MGBT (`P3_089`), PILFs before → after | EMA, no PILF test | MOM-LP3 | L-moment LP3 | L-moment GEV |
|---|---|---|---|---|---|
| 08066300 | 0.0% (1 → 1) | +23.5% | −49.8% | −16.4% | −0.1% |
| 08385600 | error (both) | 0.0% | 0.0% | 0.0% | 0.0% |
| 01515000 | −0.8% (0 → 1) | −17.4% | −42.3% | −14.0% | −2.6% |
| 02366500 | 0.0% (1 → 1) | −35.4% | −52.2% | −13.5% | −0.9% |
| 05405000 | 0.0% (35 → 35) | −25.2% | −43.3% | −12.5% | −1.1% |
| 08151500 | error | −39.5% | −39.5% | −12.8% | −0.0% |
| 08167000 | error | −33.9% | −33.9% | −13.5% | −0.0% |
| 08190000 | 0.0% (23 → 23) | −20.4% | −20.4% | −10.4% | −0.0% |
| 09442000 | −1.5% (0 → 1) | −40.0% | −40.7% | −12.7% | −0.1% |
| 14321000 | 0.0% (9 → 9) | −3.6% | −36.0% | −8.8% | −0.5% |

EMA without a PILF test differs from MOM-LP3 exactly on the perturbed records whose sample skew falls below −1.41 or whose fitted LP3 upper bound `exp(μ − 2σ/γ)` falls below the largest observed flood: 01515000, 02366500, 05405000, 08066300 and 14321000 (both conditions), and 09442000 (bound only). `P3_089`'s `.momsadj` (lines 913–919) applies `m[3] <- max(s1, -1.41, 2/sqrt(m[2])/(m[1]-xmax))`, a lower bound on skew attributed to Griffis, Stedinger and Cohn (2004). A plain moments fit there yields an LP3 whose upper bound is *below* the largest flood on record, which is physically inconsistent. The skew and bound diagnostics are reproduced by `support/lp3_bound_check.py`. *Basis: source + execution + derived.*

The pattern is structural. In log space a tenfold drop in one value moves the sample mean, variance and skew, and through the skew the upper tail. MGBT censoring absorbs the change when the perturbed value is flagged. GEV fitted in real space is dominated by the large values. *Basis: execution + derived.*

### 5. Evidence that motivated the update, and robustness studies

- **Stedinger and Griffis (2008).** Bulletin 17C states that its methods are "based on research summarized by Stedinger and Griffis (2008)". The full text was **not examined**. OpenAlex returns an unrelated abstract for this DOI. Secondary summaries attribute to it the recommendations later adopted: EMA, a generalized low-outlier test, GLS regional skew and better confidence intervals. *Basis: documentation (secondary; weak).*
- **Cohn, Lane and Baier (1997).** In Monte Carlo comparisons EMA "is more efficient than the Bulletin 17B method, and … nearly as efficient as maximum likelihood estimation (MLE)". EMA estimates "appear" always to exist and be unique, "although neither result has been proven".
- **Cohn, Lane and Stedinger (2001).** Asymptotic variance and confidence intervals for EMA quantiles. With 25–100 years of gauge record plus 50–150 years of historical information, the intervals are "though not exact … acceptable for most purposes".
- **England, Salas and Jarrett (2003).** EMA versus Bulletin 17B historical weighting: "EMA performed significantly better than B17H in nearly all cases considered". B17H did not fully use historical information beyond 200 years.
- **Cohn et al. (2013).** The generalized Grubbs–Beck statistic, "similar to the Rosner (1983) test", with PILFs then handled "using censored-data statistical techniques, such as the Expected Moments Algorithm".
- **Lamontagne et al. (2016).** Reports MGBT PILF identification rates (Type-I-like) for LN and LP3 at several skews. MGBT identification "generally matched subjective identification from a recent California flood frequency study". Censoring "improves the extreme quantile estimator efficiency of the expected moments algorithm (EMA) for negatively skewed LP3 distributions and has little effect for zero or positive skews" and "protects against deviations from the LP3 in the lower tail".
- **Griffis and Stedinger (2007).** LP3 is reasonable for log-space |skew| ≤ 1.414, with |skew| ≤ 1 more realistic.
- **Asquith, Kiang and Cohn (2017).** For AEP < 10⁻³, "distribution choice uncertainty is larger than sampling uncertainty".

*Basis: documentation.* The numeric rates, efficiency ratios and the California study's site counts in Lamontagne et al. (2016) were **not examined**: only the abstract was read.

### 6. Nonstationary return period and risk

With year-specific exceedance probabilities `p_t` for a fixed design flood `q`, the definitions are

```text
P(first exceedance in year x) = p_x · Π_{t<x} (1 − p_t)
expected waiting time T(q)    = Σ_{x≥1} x · p_x Π_{t<x}(1 − p_t) = 1 + Σ_{x≥1} Π_{t≤x}(1 − p_t)
risk over n years R_n(q)      = 1 − Π_{t=1..n} (1 − p_t)          # stationary: T = 1/p, R_n = 1 − (1 − p)^n
design-life level (Rootzén–Katz): z such that Π_{t∈life} F_t(z) = 1 − R_target
```

Salas and Obeysekera (2014) extend the geometric distribution to changing `p_t` in this way. Olsen et al. (1998) frame return period as expected waiting time and show that "alternative definitions of the return period imply different risk under nonstationary conditions". Read and Vogel (2015) recommend replacing average return period with reliability over a planning horizon. Serinaldi (2015) argues for "dismissing return periods". Serinaldi and Kilsby (2015) argue that, when trend model structure cannot be deduced, stationary models with honest uncertainty "should be retained". Milly et al. (2015) respond to critiques of the 2008 paper. *Basis: documentation + derived.*

Toy model (`support/nonstationary_toy.py`). It uses a GEV with Hosking-approximation parameters from the 08167000 L-moments (ξ = 9483.6, α = 13327.2, k = −0.4466, so Q₁₀₀ = 212,467 cfs) and scales all flows by `(1+g)^t`. The approximation gives Q₁₀₀ = 212,467 cfs, against 212,487 from the exact lmomco fit, a 0.01% difference. **This illustrates the definitions. It is not a model of that river.**

| g per year | p in year 1 → year 50 | expected waiting time for Q₁₀₀ | 50-yr risk of exceeding Q₁₀₀ | 50-yr design-life level at the stationary risk 0.395 |
|---|---|---|---|---|
| 0 | 0.01000 → 0.01000 | 100.0 yr | 0.3950 | 212,467 (0%) |
| 0.002 | 0.01004 → 0.01224 | 75.8 yr | 0.4279 | 223,754 (+5.3%) |
| 0.005 | 0.01010 → 0.01649 | 59.7 yr | 0.4817 | 242,505 (+14.1%) |
| 0.010 | 0.01020 → 0.02672 | 46.5 yr | 0.5817 | 279,366 (+31.5%) |

Drifting only the GEV location, with scale fixed (`nonstationary_toy.py --loc-only`), gives an expected waiting time of 84.2 years at g = 0.01, against 46.5 here. For this heavy-tailed fit the result depends strongly on which parameter drifts. *Basis: execution (toy model).*

**Stationarity assumptions in Bulletin 17C**, derived from the main text:

1. LP3 fitted to iid annual peaks.
2. Historical and paleoflood perception thresholds pooled with the systematic record as one population over centuries.
3. Regional skew regressions pooling long records.
4. The MGBT null hypothesis of iid normal logs.
5. Confidence intervals for iid samples.
6. Reporting AEP p as "1/p-year" flood.

Bulletin 17C states that time invariance was assumed. Where evidence permits, it calls for "time-varying parameters or other appropriate techniques" and cites Salas and Obeysekera (2014). It lists "examination and redefinition of risk, reliability, and return periods under nonstationary conditions" as future study item 8. It calls multidecadal trends unexplained by land use or climate change "a seriously unresolved problem". *Basis: normative + derived.*

### 7. Performance and resource footprint (L1–L6)

The host is Linux on 96 vCPUs (Intel Xeon @ 2.60 GHz) with 236 GB RAM.

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | person-effort for a Bulletin 17C implementation | not measured | — |
| L2 toolchain | environment and package footprint | R 4.5.3 environment via micromamba: 8.4 s, 1.4 GB on disk. Installed package sizes: MGBT 2.5 MB, lmomco 4.0 MB, lmom 792 KB. Source tarballs: 1,738,979 / 1,017,638 / 342,342 B | measured |
| L3 compile | compile or JIT latency | none at run time for R or Python. lmom's compiled code was built during `R CMD INSTALL`, but its build time was not measured | not measured |
| L4 execution | MGBT (5 variants) + 4 fits per record | 12.5–33.2 s wall per record, 178 s for 10 records. Dominated by `integrate()` of `peta` per order statistic | measured |
| L4 execution | lmoments3 GEV fit + quantile | 0.33–0.75 ms per record | measured |
| L4 execution | EMA (`P3_089`) per record: 4 fits including 2 MGBT runs | 15.2–35.8 s (wall, by record). 294 s for 10 records | measured |
| L5 checking | cross-implementation agreement check | trivial (`≤ 7.2e-15`) | measured |
| L6 memory | peak RSS | R MGBT/L-moment probe: 114 MB. EMA probe: 107 MB (`/usr/bin/time`) | measured |

### 8. Comprehensibility and conceptual simplicity (C1–C2)

- **C1.** The procedure carries several interacting concepts: intervals, perception thresholds, PILF threshold, three alphas, station/regional skew MSEs, a confidence-interval formula, and the AEP < 0.10 scope. The MGBT sweep rule is the least legible. The original R ports encoded both sweeps in one loop with an extra continuity condition (`j2 == i-1`). That single loop computes a different K from the written rule, and this was recognized around June 2017, when the R ports were compared with PeakFQ output (`MGBT-package.Rd` §"Notes on Bugs in Sources by TAC"). A reader cannot check the rule locally without the p-value vector, so implementations should return it, as `MGBT17c` does with `$pvalues` and `$index`.
- **C2.** EMA unifies the special cases that Bulletin 17B handled separately: historical weighting, the conditional probability adjustment for low outliers, and zero flows. They all become intervals. This is a clear simplification: one estimator, one data type. The remaining non-uniformity is that PILFs are censored by a *test* outside the estimator. A model in which every observation carries an interval would subsume zeros and PILFs, and only the choice of threshold would stay external. The return-period redefinitions show the same pattern. "T-year flood" is meaningful only when `p_t` is constant. A minimal universal quantity is risk or reliability over a stated design life (`R_n`, design-life level), which reduces to `1 − (1 − p)^n` in the stationary case.

*Basis: derived.*

### 9. How implementations are validated (V1–V4)

- **V1, specification adequacy.** The MGBT sweep rule is specified in prose (Bulletin 17C Appendix 6, quoted). MGBT 1.1.8 keeps a literal port (`MGBT17c.verb`) as an oracle against its fast version. That oracle has its own edge-case defect (§3). There is no published formal or executable reference for the rule except PeakFQ, a Fortran program that was not examined.
- **V2, differential testing.** The MGBT documentation records batch runs over more than 1,400 Texas peak-flow series that exposed numerical failures in the R ports (`integrate()` divergence, `pt()` precision, square roots of negatives). Its examples use quoted PeakFQ v7.1 output as the reference. The present probe found three L-moment implementations in exact agreement and Cohn's single-loop MGBT disagreeing with `MGBT17c` on 3 of 11 real records.
- **V3, concurrency and crash testing.** Not applicable.
- **V4, field falsification.** Robustness is established by Monte Carlo with misspecified lower tails (Lamontagne et al. 2016). It cannot be established against observed future floods within record lengths. Nonstationary models face the extra model-structure uncertainty stressed by Serinaldi and Kilsby (2015).

## Boundaries

- **Not examined.**
  - USGS-PeakFQ (Fortran) and HEC-SSP. These are the production Bulletin 17C implementations, and their MGBT and EMA outputs were known only where MGBT's documentation quotes PeakFQ v7.1.
  - Bulletin 17C Appendixes 6–10.
  - Bayesian GLS regional skew (no regional skew was applied).
  - Historical and paleoflood intervals, and crest-stage-gage thresholds (only systematic records were run).
  - EMA confidence-interval coverage.
  - Full texts of Stedinger–Griffis (2008), Lamontagne et al. (2016) and Cohn et al. (2013).
  - MOVE record extension.
- **Unknown.**
  - Whether PeakFQ agrees with `MGBT17c` on 05405000 and 08190000, where the single-loop rule differs.
  - Whether any production record triggers defect 2 (the `j3` initialisation) or defect 3 (`.verb`).
  - Whether `P3_089`'s use of the Bulletin 17B skew-MSE approximation matches PeakFQ.
- **Known not to apply.**
  - The EMA quantiles here are station-skew, systematic-only fits from an archived research source. They are not Bulletin 17C flood quantiles for those stations.
  - The nonstationary table is a toy illustration.
  - The 08385600 perturbation result (0%) reflects a zero minimum, not robustness.
- **Unsupported stronger conclusions.**
  - That GEV-by-L-moments is "better" than EMA/LP3. Its insensitivity to low floods comes with different upper-tail behavior, and the records examined cannot rank estimators.
  - That MGBT 1.1.8's defects change Bulletin 17C results in practice. None of them is triggered by `MGBT()` with default arguments on the examined records.

## Evidence

Evidence was gathered on 2026-11-20 (UTC). Revisions were resolved with `gh api repos/<owner>/<repo>/commits/HEAD`. Sources were read from `raw.githubusercontent.com` at the pinned SHAs.

- **`cran/MGBT@0994615648a373bd7beb3cf7ebecb19e9edd948c`.**
  - Package code: `R/MGBT.R` (lines 1, 25–115, 145–206, 259–308, 317–373, 379–426, 429–446, 452–469), `R/RthOrderPValueOrthoT.R` (54–72) and `R/peta.R` (19–42).
  - Documentation: `man/MGBT.Rd` (12–25, 40–60, 62–138, 158–200) and `man/MGBT-package.Rd` (15–32, 58–125). `DESCRIPTION` (version 1.1.8).
  - Cohn's EMA source `inst/sources/P3_089(R).txt` (`makeFLOODdata` 138–186, `makeEMAresult` 453–505, `MGBTest` 598–620, `MGBT` 627–639, `ema` 814–850, `.p3mombin` 867–873, `.momsp3` 899–902, `.momsadj` 913–919, `.mseg` 939–943, `.ci_ema_03` 1151–1158, Big Sandy example 1780–1800).
- **`wasquith/lmomco@9d49f0a2e6fe1d687af82efe63d4a73caca82b04`.** `R/lmoms.R`, `R/pargev.R`, `R/quagev.R`, `R/parpe3.R`, `R/quape3.R`, `R/vec2par.R` (executed) and the bundled `data/USGSsta*peaks.RData`.
- **`cran/lmom@252d9635c3acaf452d4d497fab2da01fa1edfcd8`.** `R/lmom.r` (`samlmu`, `pelgev`, `quagev`; executed).
- **`OpenHydrology/lmoments3@7e19f97c23019ca68cbd526b8bd417c412438f1c`.** `lmoments3/__init__.py` (`lmom_ratios` 69–84) and `lmoments3/distr.py` (`GenextremeGen._lmom_fit` 1055–1125). Under CPython 3.13 the docstrings at `distr.py` lines 152, 267 and 423 raise `SyntaxWarning: invalid escape sequence`.
- **Bulletin 17C v1.1.** Foreword and Introduction (printed pp. 1–4). Data Assumptions and Specific Concerns, including "Climate Variability and Change" (p. 23). Determination of the Flood Flow Frequency Curve: "Weighted Skew Coefficient Estimator" (p. 25), "Zero Flows and Identifying Potentially Influential Low Floods" (p. 26), "Expected Moments Algorithm" (p. 27), "Confidence Intervals for Quantiles" and "Estimating Regional Skew" (p. 30). Software and Examples, Future Studies (p. 35), and Applicability of These Guidelines. Page numbers are from the table of contents.
- **Literature.** All DOIs in `REPORT.json`, plus 10.1002/wrcr.20425, 10.1002/2015WR017089, 10.1007/s00477-014-0916-1, 10.1111/j.1539-6924.1998.tb00364.x, 10.1061/(ASCE)1084-0699(2007)12:5(482), 10.1029/2004WR003445, 10.3133/fs20133108, 10.1002/2015WR017408, 10.1016/j.advwatres.2014.12.013, 10.1017/CBO9780511529443, 10.1080/00401706.1985.10488049, 10.1080/00401706.1972.10488981, 10.1007/978-94-007-4479-0_4, 10.1111/j.1752-1688.2011.00541.x, 10.1029/2002WR001791 and 10.3133/sir20175038. Each was resolved through the doi.org handle API (`responseCode 1`) and matched for title, year, venue and pages against OpenAlex. The 10.5066/P9CW9EF0 software release was checked against DataCite. Crossref was unreachable from the fetcher used.
- **Execution (support/).**
  - `flood_probe_lmom_mgbt.R` with `.out` and `flood_probe_results.csv`.
  - `flood_probe_ema.R` with `.out` and `flood_probe_ema_results.csv`.
  - `mgbt_defects.R` with `.out`.
  - `flood_probe_ema_fixed_threshold.R` with `.out`.
  - `lp3_bound_check.py` with `.out`.
  - `lmoments3_probe.py` with `.out`.
  - `nonstationary_toy.py` with `.out`.
  - `peaks_<site>.csv`, the exact inputs.

## Revalidation

1. **MGBT.** Diff `R/MGBT.R` lines 429–446 and 347–356 at a new revision, then rerun `support/mgbt_defects.R`. Defect 1 is fixed if the `alphain = 0.01` call returns `index 4`. Defect 2 is fixed if the sweeper returns 4 for the first two vectors. Defect 3 is fixed if `.verb` gives K = 5.
2. **PeakFQ agreement.** Rerun `support/flood_probe_lmom_mgbt.R` and `support/mgbt_defects.R`. `MGBT17c` should still give 284, 185 and 1110. Running PeakFQ on `peaks_05405000.csv` and `peaks_08190000.csv` would settle whether 32 or 35, and 20 or 23, is the Bulletin 17C answer.
3. **L-moment agreement.** Rerun `support/lmoments3_probe.py`. Any relative difference above about 1e-12 signals a changed approximation.
4. **EMA.** Rerun `support/flood_probe_ema.R`. The embedded Big Sandy example (1897–1973 with historical thresholds, regional skew −0.5, MSE 0.3025) must print Q₁₀₀ = 23,600 [18,500, 35,000]. Rerun `support/flood_probe_ema_fixed_threshold.R` to recheck the −3.9% and −27.2% threshold effects.
5. **Guideline.** Check for a Bulletin 17C revision after v1.1 (May 2019), especially any change to the nonstationarity language or Appendix 6.
