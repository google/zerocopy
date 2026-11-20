# EuroForMix gamma peak-height model, STRmix/TrueAllele validation evidence, PG validation standards, and NYC Forensic Statistical Tool source behaviors

## Summary

- **EuroForMix 4.2.6 likelihood (source).** For every allele position `a` in a marker, the peak height is `Y_a ~ Gamma(shape_a, scale)` with `shape0 = 1/omega^2`, `scale = mu/shape0 = mu*omega^2`, and `shape_a = shape0 * sum_k Mx_k * n_ka * beta^((bp_a-125)/100)`. Stutter moves mass between neighbouring alleles: `(1-xiB-xiF)` stays on the parent allele, `xiB` goes one repeat down and `xiF` one repeat up. Drop-out is not a separate parameter. A peak below the analytical threshold (AT) contributes `P(Y_a < AT)`, i.e. `pgamma(AT, shape_a, scale)`. Drop-in per replicate is `1-pC` when no peak is unexplained, and otherwise `prod pC * f_a * lambda*exp(-lambda*(y_a-AT))` over the unexplained peaks. Genotype priors use the Balding–Nichols sampling formula with typed-allele counts.
- **EuroForMix reports three LR estimators.** (1) The MLE plug-in ratio, which needs no sampling. (2) Adaptive cubature over the box `MLE ± 4·SE` with documented relative tolerance 1 (100%) by default. (3) Random-walk Metropolis sampling, which yields a "conservative" LR (the 5% quantile of log-likelihood differences between paired, independent Hp and Hd chains) and a Gelfand–Dey Bayes factor. All three run on a genotype set pruned at `resttol = 1e-6`. Its fit diagnostic `validMLEmodel` is a leave-one-peak-out probability-integral-transform (PIT) PP-plot with a Bonferroni envelope. The envelope uses `Beta(i-0.5, N-i+1.5)` rather than the exact order-statistic law `Beta(i, N-i+1)`.
- **NYC FST (source at the pinned commit) is a table-driven semi-continuous model.** Drop-out comes from per-locus tables (`PHET1`, `PHET2`, `PHOM1`), linearly interpolated over the template grid {6.25, 12.5, 25, 50, 100, 101, 150, 250, 500} pg. The table is chosen by the number of persons in each hypothesis, a "Deducible" flag and the lab kit. Drop-in is a count-based rate (`Pc0`/`Pc1`/`Pc2` for 0, 1 or ≥2 unexplained alleles) with **no allele-frequency factor**. Theta is applied **only to homozygote genotype frequencies** (`p*(p+θ(1−p))`); heterozygotes use plain `2pq`. Four race-specific LRs (Asian, Black, Caucasian, Hispanic) are accumulated in `double` from `float` rates and frequencies, then returned as single-precision `float`.
- **FST silently removes some loci.** `CheckFrequencyForRemoval` drops a locus from **every** race's LR whenever the evidence alleles' frequencies sum to `>= 0.97` in **any** race. The other silent behaviours are: loci whose denominator is 0 are skipped; a replicate recorded as `NEG` is treated as an allele label called "NEG"; and a degradation-specific drop-out reader exists but is never called. In toy ports, locus removal multiplied the total LR by 0.48 (removing an LR-raising locus) up to 306.6 (removing an exculpatory locus). These are toy numbers, not FST measurements.
- **Standards (normative text examined).** SWGDAM 2015 asks for sensitivity, specificity and precision studies. Its §3.2.3 asks for "the variation in Likelihood Ratios calculated from repeated software analyses of the same input data". ANSI/ASB 018 (2020) makes accuracy, sensitivity, specificity and precision mandatory ("shall"). It also requires evaluation after software modifications (§4.4). PCAST 2016 found that studies had established the foundational validity of some objective (probabilistic genotyping) methods for complex mixtures only "under limited circumstances (specifically, a three-person mixture in which the minor contributor constitutes at least 20 percent of the intact DNA in the mixture)".

## Applicability

**Subjects and their relationship.** The report compares three probabilistic-genotyping (PG) implementations. Their requirements come from one normative recommendation (ISFG 2012) and two validation standards (SWGDAM 2015, ANSI/ASB 018-2020), and are placed in context by one advisory report (PCAST 2016):

- EuroForMix (`oyvble/euroformix` @ `800c314c91235e2b9a67270437226d4dada325b4`, `DESCRIPTION` Version 4.2.6, Date 2026-09-18). Statements about EuroForMix are exact for this commit only. The core engine was rewritten in 2022–2023 (`src/EFMfastengine.cpp` header: "WRITTEN BY OYVIND BLEKA (2022)… updated in June 2023 to enable restricted calculations"), so the findings must not be assumed for releases that predate this engine.
- NYC Forensic Statistical Tool (`propublica/nyc-dna-software` @ `5b3500de6f0b879350dd1b487218e590eeacc138`). This is the source as released in October 2017. Public reporting (ProPublica, 2017) says portions of FST were re-coded in 2011. Which casework period this exact snapshot corresponds to is **unknown**.
- STRmix and TrueAllele are closed-source. They are characterized only through peer-reviewed abstracts and clearly labeled secondary descriptions. No STRmix or TrueAllele code or executable was examined.

**Observation mode.** All upstream findings come from static reading of the pinned sources, plus published or normative text. **No upstream program was executed**: R, .NET and SQL Server are not available on the host. Executed probes are Python toy models of formulas reconstructed from source (`support/probe_efm_formulas.py`) and a Python port of FST per-locus arithmetic with invented rates (`support/probe_fst_port.py`). Every probe result is labeled `toy model`.

**Line numbers** are counts of LF-delimited lines as printed by `grep -n`/`sed -n` on the raw files at the pinned commit. Several EuroForMix R files use `\r\r\n` endings and FST files use CRLF, but LF counting is unaffected.

**Scope limits.** The FST drop-out, drop-in and allele-frequency **values** live in `Database/FST_DB.bak`. That file is a compressed Microsoft SQL Server backup (magic bytes `MSSQLBAK`). Its stored procedures and tables were not decoded. Every FST statement therefore concerns the code that consumes the tables, not the table values.

## Findings

### 1. EuroForMix 4.2.6: peak-height, stutter, degradation, drop-out and drop-in model

Basis: source (`src/EFMfastengine.cpp`, `src/genoProbFuns.cpp`, `R/prepareC.R`, `R/calcMLE.R`).

**Parameter vector.** `theta = (Mx_1..Mx_C, mu, omega, beta, xiB, xiF)`. The number of free parameters is `np = (nC+1) + DEG + BWS + FWS` (`R/calcMLE.R` L86). The engine maps it to gamma parameters in `calcEvidWeights` (`src/EFMfastengine.cpp` L529–537):

```cpp
double mu = theta[m_NOC]; //obtain PHexp param
double omega = theta[m_NOC+1]; //obtain PHvar param
double loggedBeta = log(theta[m_NOC+2]); //obtain slope param (take log to easy further calculations)
double shape0 = 1/(omega*omega); //get shape param
double scale0 = mu/shape0;// get scale param
```

**Degradation** (L545–546): `Row<double> degScale = shape0 * exp(m_basepairLong * loggedBeta);` and `m_contrMatPerAllele = contrWithMx * degScale;`. Fragment lengths are first rescaled with `basepairLong = (basepairLong-125)/100` (`R/prepareC.R` L381). The expected-height multiplier is therefore `beta^((bp-125)/100)`, i.e. `beta` per 100 bp relative to a 125 bp fragment. The Q-allele, which stands for all unobserved alleles, gets the longest kit fragment by default: `QalleleFraglength = max(kittab$Size)` (L243).

**Moments (derived from gamma moments).** For an allele with summed weight `W = sum_k Mx_k n_ka beta^((bp-125)/100)`:

- `E[Y] = shape*scale = mu*W`
- `Var[Y] = shape*scale^2 = mu^2*omega^2*W`
- coefficient of variation `= omega/sqrt(W)`

So `omega` is the CV of a full-weight, single-copy allele (`W = 1`). Smaller contributions are relatively noisier.

**Stutter** (L566–581). For every allele position, including "potential stutter" positions where no peak was observed:

```cpp
if( m_BWtoLong[cumAlleleIdx] > -1 ) { //If giving away stutter (better check than using Q-allele index)
    contrVEC *= (1-xiB-xiF); //then loose stutter products (scaling)
...
contrVEC += xiB*colVEC( m_lookUpMat.col(1) ); //modify based on stutter products
...
contrVEC += xiF*colVEC( m_lookUpMat.col(2) ); //modify based on stutter products
```

The resulting shape is `(1−xiB−xiF)·s_a + xiB·s_parent(a+1) + xiF·s_parent(a−1)`. The parent's degradation factor travels with the stutter product. Alleles that donate no stutter, such as the Q-allele, keep their full shape.

**Peak likelihood and drop-out** (L589–599):

```cpp
if( cumAlleleIdx < 0) { //Assuming dropout for all replicates
    weight+= NumReps *(R::pgamma(AT, shape1,scale0, 1, 1)); //calculate for all replicates (identical)
...
        if(peak < AT) {
            weight += R::pgamma(AT, shape1,scale0, 1, 1); //calculate for certain replicates
        } else {
            weight += shapeConst + (shape1-1)*log(peak) - peak * const1;
```

Drop-out probability is thus `P(Y<AT) = F_Gamma(AT; shape_a, scale)` for each replicate. It is a function of the parameters, not a lookup table. Peaks below AT are zeroed at input: `indUse = locDat$hdata>=ATv[markerIdx]` (`R/prepareC.R` L185).

**Drop-in.** The per-allele weight is `dropinWeight = log(freqs2) + log(pCv[markerIdx]) + dexp(yv-ATv[markerIdx],rate=lambdav[markerIdx],log=TRUE)` (`R/prepareC.R` L212). The engine applies it per replicate (`src/EFMfastengine.cpp` L252–258):

```cpp
uvec dropinInd = intersect(hasPosY_list[r],noContribution); //obtain drop-in allele positions (assume nRep=1)
int nDropIn = dropinInd.n_elem; //get number of dropin elems
if( nDropIn>0 ) {
    m_pGvec[gind] +=  sum(dropinweight(dropinInd));
} else {
    m_pGvec[gind] +=  log(1-m_pC);
}
```

Defaults in `calcMLE` are `AT=50, pC=0.05, lambda=0.01` (`R/calcMLE.R` L54).

**Genotype prior with coancestry** (`src/genoProbFuns.cpp` L4–6, L22–27):

```cpp
double prob_a(double Pa, double mm, double nn, double fst) {
	return( (mm*(fst) + (1-(fst))*Pa)/(1+(nn-1)*(fst)) );
```

The homozygote is `prob_a(p_a, m_a, n) * prob_a(p_a, m_a+1, n+1)`. The heterozygote is `2 * prob_a(p_a, m_a, n) * prob_a(p_b, m_b, n+1)`. Counts are updated after each unknown (`src/EFMfastengine.cpp` L236–238), so the joint prior of all unknowns is the sequential Balding–Nichols product. That product is conditioned on the typed references, which include the "known non-contributors" (e.g. the person of interest, POI, under Hd).

**Frequencies.** An allele absent from the database receives `minF = min(unlist(popFreq))` by default (`R/prepareC.R` L30). With `normalize` (signature default `TRUE`) frequencies are renormalized: `if(normalize) freqAll = freqAll/sum(freqAll)` (L197). The Q-allele frequency is `Qfreq = 1-sum(freqs)` (L203).

### 2. EuroForMix numerical machinery and LR estimators

Basis: source.

| Step | Mechanism (pinned source) | Reproducibility consequence |
|---|---|---|
| Genotype enumeration | `m_nJointCombFULL = (size_t) pow(m_NumGenos1p,m_NOU)` with `m_NumGenos1p = NumAlleles*(NumAlleles+1)/2` (L130, L189) | Exact sum over `(A(A+1)/2)^NOU` combinations per marker before restriction (derived) |
| Restriction | `.preSearch` grid over Mx, then `restprop = obj$restrictGenos(as.numeric(resttolReps))` with `resttolReps = resttol^c$nReps` (`R/helpfunctions.R` L153–154); C++ keeps combinations with `m_genoWeightsHighest - log_pGvecMax >= log(restGenoThresh)` (L268) | Likelihoods are approximate (default `resttol=1e-6`, `R/calcMLE.R` L55). A warning fires if the restricted and unrestricted values differ by more than `difftol` (L172) |
| MLE | Up to `nDone` presearch starts (L155), `nlm(...)`; covariance `MASS::ginv(numDeriv::hessian(...))` (L252–255) | Start points come from a presearch over Mx; `set.seed(seed)` (L58) affects `fitgammamodel`'s `rnorm` start search (`R/fitgammamodel.R` L88) |
| LR (MLE) | `lr_logged = (mlefitHp$fit$loglik-mlefitHd$fit$loglik)` (`R/calcLRmle.R` L8) | Deterministic given the optimum. Also reports a Laplace approximation `logmargL <- 0.5*(np*log(2*pi)+detSIGMA) + maxL` (`R/calcMLE.R` L323), `+lfactorial(nUnknown)` (L328), and `LRadj_logged = lr_logged + lgamma(nUpDiffMx+1) - lgamma(nUdDiffMx+1)` (`R/calcLRmle.R` L26) |
| LR (INT) | Box `lower = th0 - dev*2*SE`, `upper = th0 + dev*2*SE` (`R/getParamLimits.R` L15–16); `calcINT(..., reltol=1, scale=0, maxEval=1000, ...)` (`R/calcINT.R` L17); inner Mx integrals use `cubature::adaptIntegrate(fun,L,U, tol=2,...)` (L74) | With `calcLRint` default `dev=2` the box is MLE ± 4 SE (derived: 2·2). `reltol` is documented as "Required relative tolerance error" (L7), so the default asks for 100% relative error and the inner integrals for 200%. The LR error interval is returned as `log10LRerror` |
| LR (MCMC) | Random-walk Metropolis: proposals `X <- matrix(rnorm(np*niter),ncol=np,nrow=niter)%*%C` with `C <- chol(delta*Sigma0)` (`R/contLikMCMC.R` L95, L47); accept if `U[m] <= exp(postlogL[m]- postlogL[m-1])` (L126–133); parameters with `thetaSE < 1e-3` are fixed (L39); if the Cholesky factorization fails, `Sigma0 <- Sigma0 + 0.01` (L53) | Flat prior inside the domain (L78: `if(any(param<0) || any(param[-(nC+1:2)]>1)) return(-Inf)`). The run depends on the RNG seed |
| Conservative LR | `log10LRdistr <- (hpmcmc$postlogL - hdmcmc$postlogL)/log(10)`; `gfun = function(x) quantile(x,quantile)` with default `quantile=0.05`, `niter=2000` (`R/calcLRmcmc.R` L23, L47, L63) | Pairs the i-th Hp draw with the i-th Hd draw from **independent** chains. The Hd RNG seed is `seed + diffSeed` with `diffSeed=999` (L56) |
| Precision report | Bootstrap of the quantile with effective sample size `size = round( length(x)/(1+2*sum(acfobj$acf[-1])) )` from `acf(x,lag.max=100)` (L76–77), `nrep=10000` (L82) | Reported as `log10LRconsCI` |
| Bayes factor | Gelfand–Dey: `logmargL <- log(length(logVals)) - offset - log(sum(exp(logVals-offset)))` with `logVals = logpX - postlogL` and `h = N(MLE, delta*Sigma)` (`R/contLikMCMC.R` L148–160) | Returned as `LRbayes`. Set to `NaN` if infinite (`R/calcLRmcmc.R` L69) |
| Thread-level parallelism | `#pragma omp parallel for reduction(+:likEvidMarker)` (L276, L295) | The order of floating-point summation depends on the thread count. Last-bit log-likelihood differences across `maxThreads` settings are expected (derived; not measured) |

**Interpretation of the conservative LR (derived).** `log10LRdistr` holds draws of `log L(θp|Hp) − log L(θd|Hd)` with `θp` and `θd` drawn independently from their two posteriors. Its 5% quantile describes the spread of plug-in likelihood ratios across posterior parameter draws. It is not a credible bound on the integrated (Bayes-factor) LR, which the code estimates separately as `LRbayes`.

### 3. EuroForMix model-fit diagnostic (`validMLEmodel`)

Basis: source. `calcValidMLEmarker` (`src/EFMfastengine.cpp` L348–459) computes one value per observed peak. Each value is a leave-one-out PIT under the MLE: the peak's own density term is removed from each genotype weight before averaging the gamma CDF over genotypes:

```cpp
double peakMaxModel = R::qgamma(0.99999, 2*shape0,scale0, 1,0); //max observation in theory (used only for model validation)
...
double lowerIntegral = R::pgamma(m_AT-1, shape1,scale0, 1, 0); //common for both terms
double maxIntegral = R::pgamma(peakMaxModel, shape1,scale0, 1, 0); //common for any replicates
...
log_genoWeightCopy -= weightReps[outerRep]; //subtract weight of particular replicate
logLikVal_OBS = log_genoWeightCopy + log(obsIntegral - lowerIntegral);
logLikVal_MAX = log_genoWeightCopy + log(maxIntegral - lowerIntegral);
```

The R layer forms `cumprobi = UaPH/UaMAX` (`R/calcMLE.R` L284), i.e. `ProbObs = Σ_g w_g^(−a)[F(y)−F(AT−1)] / Σ_g w_g^(−a)[F(Ymax)−F(AT−1)]`. Peaks explained by drop-in use the exponential CDF `1-exp(-m_lambda*( peak - m_AT))` (L390). The test itself is in `R/validMLEmodel.R` L29–45:

```r
N <- nrow(tab) #length(cumprobi) #number of peak heights
alpha2 <- alpha/N #0.05 significanse level with bonferroni correction
cumunif <- ((1:N)-0.5)/N #=punif((1:N)-0.5,0,N)
...
pval <- 1-pbeta(cumprobi[ord],N*cumunif,N-N*cumunif+1) #one sided p-value
...
outside <- pval[ord2] < (alpha2/2) #criterion outside region (divide by 2 to get two-sided)
```

Default `alpha=0.01` (L17). The comment says "0.05".

**Discrepancy with the exact order-statistic law (derived + toy execution).** The i-th order statistic of N i.i.d. U(0,1) values is `Beta(i, N−i+1)`. The code uses `Beta(N*u_i, N−N*u_i+1)` with `u_i=(i−0.5)/N`, i.e. `Beta(i−0.5, N−i+1.5)`. For N=50, the per-point two-sided Bonferroni level is `(0.01/50)/2 = 1e-4`. Resulting acceptance intervals, from `support/probe_efm_formulas.py`; Basis: execution (toy model of the EuroForMix envelope formula, not EuroForMix itself):

| N | rank i | code interval | exact interval |
|---|---|---|---|
| 50 | 1 | [1.563e-10, 0.139811] | [2.000e-06, 0.168236] |
| 50 | 25 | [0.2390, 0.728007] | [0.2471, 0.736401] |
| 50 | 50 | [0.8088, 0.999948] | [0.8318, 0.999998] |
| 200 | 1 | [2.451e-12, 0.043386] | [1.250e-07, 0.051604] |

The code envelope is shifted toward 0. It flags unexpectedly **high** PIT values at low ranks more readily and unexpectedly **low** PIT values less readily. The effect shrinks as N grows.

### 4. STRmix and TrueAllele (closed source; literature level)

**STRmix — what was verified.** Basis: documentation (peer-reviewed abstracts). Bright et al. 2016 describe STRmix as "probabilistic genotyping software that employs a continuous model of DNA profile interpretation". Its developmental validation "follow[s] the SWGDAM guidelines" and addresses "sensitivity, specificity and precision and results of interpretation of casework type samples". The paper concludes that STRmix "is suitable for its intended use for the interpretation of single source and mixed DNA profiles". Bright et al. 2018 compiled internal validations: "Thirty one laboratories contributed data resulting in 2825 mixtures comprising three to six donors". They confirmed "less discriminatory LRs occurring both for donors and non-donors at low template (for the donor in question) and at high contributor number" and "were unable to isolate an effect of allelic sharing".

**STRmix — secondary description, not verified against the Taylor et al. 2013 full text.** Basis: documentation (web-search summary of vendor and secondary material). STRmix is described as follows:

- `log10(O/E)` is modelled as log-normal, with allele variance scaling with `c^2/E` (stutter variance `k^2`).
- Expected heights are built from per-contributor template mass, locus-specific amplification efficiencies, exponential degradation by fragment size, and stutter ratios.
- Drop-in peak heights follow a gamma distribution.
- MCMC (Metropolis–Hastings) is run with burn-in and a Gelman–Rubin convergence diagnostic.
- A one-sided 99% lower highest-posterior-density (HPD) LR is reported.

These are **not** established findings of this report; they are listed under Boundaries.

**TrueAllele.** Basis: documentation (Perlin et al. 2011 abstract). The validation compared "quantitative computer interpretation" with "qualitative human review" on adjudicated two-person mixtures:

- On "eight mixtures having two unknown contributors", the average information gain was 6.24 log10 units (min 2.32, max 10.49).
- On "eight other mixtures with a known victim reference and one unknown contributor", the gain was 4.67 (min 1.00, max 11.31).

The abstract also states that "Validation methods are introduced that can assess the efficacy and reproducibility of any DNA interpretation method". The internal TrueAllele model (peak variance, stutter and degradation priors, sampler) was **not examined**.

### 5. Mapping modelling choices to ISFG 2012

Basis: normative (Gill et al. 2012, full text) + source (EuroForMix, FST) + documentation (STRmix, TrueAllele). The ISFG text says:

- Drop-out "Pr(D) can be estimated by logistic analysis… or by using an empirical approach".
- "Estimates of drop-out and drop-in probabilities should be based on validation studies that are representative of the method used".
- Drop-in: "If n negative controls are analysed and there are x spurious alleles observed… Pr(C) is estimated as x/n… we multiply together the probability of drop-in with the probability of the specific allele a… Pr(C)pa".
- Homozygote drop-out: "Pr(D2) = αPr(D)2… α = 0.5", or "Pr(D2) can be empirically estimated".
- Population structure is deferred to Curran et al. 1999.
- "Open-source is strongly encouraged… We do not advocate a 'black-box' approach."

| ISFG element | EuroForMix 4.2.6 (source) | FST snapshot (source) | STRmix (lit.) | TrueAllele (lit.) |
|---|---|---|---|---|
| Model class | Continuous (gamma peaks); drop-out implied by `P(Y<AT)` | Semi-continuous: allele presence/absence with tabulated rates | Continuous (abstract) | Quantitative/continuous (abstract) |
| Pr(D) source | Fitted per case from peak heights via `mu, omega, Mx, beta` | Empirical tables by locus, template bracket, persons, Deducible flag and kit, linearly interpolated | Not verified | Not verified |
| Homozygote drop-out | Gamma with doubled shape (`n_ka=2`). Toy: `P=0.3738` vs heterozygote `0.6742` at `mu=1000, omega=0.3, Mx=0.05` (toy model) | Separate `PHOM1` table (`PHOM0 = 1-PHOM1`) | Not verified | Not verified |
| Drop-in | `pC·f_a·Exp(λ)` density per unexplained peak, `1-pC` otherwise — ISFG form plus a height model | `Pc0/Pc1/Pc2` by **count** only; **no `p_a` factor** — departs from ISFG `Pr(C)p_a` | Gamma drop-in heights (secondary) | Not verified |
| Population structure | Balding–Nichols sequential conditional (Curran-style) | Unconditional `p^2+p(1-p)θ` for homozygotes only; heterozygotes `2pq` | Not verified | Not verified |
| Unobserved alleles | Q-allele `1-sum(freqs)` | `w` allele `1-sum` (locus skipped if `w<0` or `w>=1`) | Not verified | Not verified |
| Open source | GPL-3 (`DESCRIPTION`) | Proprietary; released by court order | Closed | Closed |

### 6. Validation designs, standards and how run-to-run variability is reported

Basis: normative (SWGDAM 2015 and ANSI/ASB 018 text, both as embedded verbatim in a vendor conformance document; PCAST 2016 executive summary) + documentation (abstracts).

| Source | Contributors | Template / ratio coverage | Non-contributor (Hd-true) testing | Variability / precision requirement or report |
|---|---|---|---|---|
| SWGDAM 2015 | §4.1.6.3 "Various numbers of contributors"; §4.1.6.4 "Over- and under- estimating of number of contributors input" | §4.1.6.1 "Various contributor ratios"; §4.1.6.2 "Various total DNA template quantities"; §4.1.7 partial profiles, degradation, inhibition; §4.1.8 drop-in | §3.2.2 Specificity: "reliable results for non-contributors"; §3.2.2.1 "Type II errors (False inclusions)" | §3.2.3 Precision: "variation in Likelihood Ratios calculated from repeated software analyses of the same input data"; §3.2.3.1 "demonstrate the range of LR values that can be expected from multiple analyses"; §3.2.3.2 "increasing the number of MCMC iterations can reduce variation" |
| ANSI/ASB 018 (2020) | §4.1.2/§4.1.3 "number of contributors, mixture ratios, and total DNA template quantities"; §4.1.5 "effect of overestimating and underestimating the number of contributors" | "shall also include compromised DNA samples (e.g., low template, degraded, and inhibited samples)" | §4.1.2: "accuracy, sensitivity, specificity, and precision" (shall) | §4.1.4 "user input parameters that vary run to run… run time parameters"; §4.4 software modifications "shall require a validation or performance check" |
| PCAST 2016 | Foundational validity for "a three-person mixture in which the minor contributor constitutes at least 20 percent of the intact DNA" | as left | not examined | not examined |
| Bright et al. 2016 (STRmix developmental) | single-source and mixtures | not extracted | "specificity" (abstract) | "precision" (abstract); numeric results not extracted |
| Bright et al. 2018 (STRmix, 31 labs) | 3–6 donors, 2825 mixtures | "wide range of multiplex, equipment, mixture proportions and templates" | non-donor LRs reported (trend statement) | not extracted |
| Perlin et al. 2011 (TrueAllele) | two-person (8 + 8 mixtures) | not extracted | not extracted | "reproducibility" methods introduced (abstract) |
| Mitchell et al. 2012 (FST) | single source, 2- and 3-person mixtures (abstract as relayed) | "over 2000 amplifications of more than 700 mixtures and single source samples" used for rate estimation (abstract as relayed) | non-contributor database reported (abstract as relayed) | n/a: FST is deterministic given tables (source) |
| EuroForMix 4.2.6 (software) | n/a | n/a | `R/calcTippet.R` simulates random non-contributors (source; not executed) | MCMC: bootstrap CI of the 5% quantile; INT: error interval; MLE: deterministic |

### 7. NYC FST source review

**Layout** (measured with `find`/`wc -l` at the pin). The computation lives in `FST.Common/` (10 `.cs` files, 6,058 lines; `Comparison.cs` 1,633 lines; `Database.cs` 1,908 lines). `FST.Web/` is an ASP.NET front end with an `Admin/` area (e.g. `frmEditFrequency`, `frmEditLabKits`, `frmViewDropoutRates`, `frmDegradedDropOutRate`). `FST_WindowsService/` and `FSTServiceConsoleHost/` host batch comparisons (`ComparisonCase.cs`). `Database/` holds two `.bak` files: `FST_DB.bak` (1,096,192 bytes; byte entropy 7.957 bits/byte) and `FST_Membership.bak` (1,071,104 bytes). Compiled `bin/` and `obj/` artifacts are checked in.

**LR pipeline** (Basis: source, `FST.Common/Comparison.cs`). For each race `r` and kept locus `l`:

```text
P(E_l | H) = Σ_rows [ Π_{unknown u} G_r(g_u) ] × Π_{replicates t with non-empty text} [ Π_{contributors c} D(g_c, E_lt) × C(#evidence alleles of E_lt not in any g_c) ]
LR_r = Π_{l kept, Pd≠0} P(E_l|Hp) / P(E_l|Hd)
```

- Unknown genotypes range over all unordered pairs from the union of evidence alleles plus `w` (`union.Append(",w");` L1068; `permutationCount = (alleles.Length * (alleles.Length + 1)) / 2` L693). Rows are skipped when their product is exactly 1 (`if (Pa != 1)` L970).
- `D`: homozygote `PHOM0` if the allele is present, else `PHOM1`; heterozygote `PHET0`/`PHET1`/`PHET2` by the number of missing alleles (L1026–1039). The zero-drop-out rates are complements: `curDrouputRate.Add("PHOM0", 1 - curDrouputRate["PHOM1"]);`, `curDrouputRate.Add("PHET0", 1 - curDrouputRate["PHET1"] - curDrouputRate["PHET2"]);` (L1377–1378). Each contributor is scored independently against the replicate. An allele seen in the evidence counts as "not dropped" for every contributor carrying it, so masking by a co-contributor is not modelled (derived).
- `C`: `float eachCo = GetGenotypeDropInRate(extras);` (L948); `case 0: Pxy = Pc0`, `case 1: Pxy = Pc1`, `case 2: default: Pxy = Pc2` (L1244–1253).
- `G`: `freq = Convert.ToSingle(freq * (freq + (Theta * (1 - freq))));//added by Dhruba` (L1300) for homozygotes; `freq = 2 * a * b;` (L1345) for heterozygotes.
- Result: `if (Pd != 0) P = P * (Pn / Pd);` (L509–510), then `DNAComparsionResult.Add(raceName, (float)P);` (L513). Race keys are hard-coded: `comparisonData.AsianLR = DNAComparsionResult["Asian"];` (L538–541). No minimum across races is taken in the examined C# (no `Math.Min`/`.Min(` match).

**Drop-out tables** (L1396–1487). Amounts are capped (`if (tempDropout > 500m)` L1405) and `(100,101)` is mapped to `101m` (L1409). Exact grid points use the stored rates. Otherwise the code interpolates linearly between bracketing points: `rate_lo + (rate_hi − rate_lo)/(opt_hi − opt_lo) · (x − lo)` (L1475–1477; the comment calls this "linear regression"). Tables are chosen separately for numerator and denominator by number of persons and Deducible flag: `numeratorDropOutRateTable = ReadDropoutRate(dropoutOption, numPersonsInvolved, numPersonsInvolved > 1 ? strDeducible : "Yes", labKitID);` (L168–169). The UI rejects amounts below 6.25 pg ("DNA Template Amount cannot be less than 6.25", `FST.Web/frmUpload.aspx.cs` L699).

**Drop-in rates** (L1604–1630) depend only on lab kit and `strType` = "Less Than Equal To 100 pg" or "Greater Than 100 pg" (`if (tempDropout > 100m)` L1611).

**Frequencies.** Alleles missing from the race table get the database's allele-"0" frequency (`Database.cs` L179: `float defaultFrequency = Convert.ToSingle(myDT.Select("AlleleNo='0'")[0]["freq"]);`). The cache path falls back to `float defaultFrequency = 0.02f;` (`Comparison.cs` L1118, L1187). Omega is `w = 1 − Σ` and the locus is skipped when `if (w < 0 || w >= 1)` returns `null` (L1220; consumer `if (tblfreq == null) continue;` L388–389). Theta comes from a database-populated drop-down with `SelectedIndex = 2` (`FST.Web/frmDefault.aspx.cs` L40). The admin test centre hard-codes `theta = 0.03f` (`FST.Web/Admin/frmTestCenter.aspx.cs` L692).

**Locus inclusion/exclusion.** A locus is excluded if:

- any comparison or known profile is empty there (L189–197); or
- every evidence replicate is empty or `"NEG"` (`if (unknown[locus][i].Trim() != string.Empty && unknown[locus][i] != "NEG")` L202); or
- the frequency-sum rule fires (L243–315):

```csharp
/// This function checks for the total frequencies according to races and removes the allelles from calculation
/// if the sum of frequencies are greater than 0.97.
...
                    if (freqSum >= 0.97)
```

The sum covers the union of evidence alleles over all replicates, excluding `w`. It is checked for each race, and a hit in **any** race removes the locus for **all** races.

#### FST discrepancy table

Basis column: S = source, P = published or public description, N = normative (ISFG), T = toy port (`support/probe_fst_port.py`; invented rates `PHET1=0.20, PHET2=0.05, PHOM1=0.10, Pc=(0.97,0.02,0.01), θ=0.03`).

| # | Implemented behaviour (quoted above) | Published / normative description | LR effect |
|---|---|---|---|
| F1 | Locus removed for all races if Σ evidence-allele freq ≥ 0.97 in any race (L267) | Not in Mitchell 2012 abstract (as relayed). ProPublica (Sept 2017): the reviewer "found that the program dropped valuable data from its calculations, in ways that users wouldn't necessarily be aware of" (S, P) | Locus factor forced to 1: raises the LR when the kept-locus LR < 1, lowers it when > 1. T: two-person mixture at an invented low-diversity locus (Σ=0.98). Suspects (8,11), (10,12), (8,13) had kept-locus LRs 0.8102, 0.03833, 0.003262, so removal multiplied the total LR by 1.234, 26.09, 306.6. Single-source fully-included suspect: kept LR 2.083, multiplier 0.48 |
| F2 | Comment says "greater than 0.97"; code uses `>=` (L244 vs L267) | — (S) | Only for sums exactly at the boundary; negligible |
| F3 | Drop-in by count (`Pc0/1/2`), no allele frequency (L944–948, L1239–1256) | ISFG: `Pr(C)·p_a` (N) | Case-dependent. T: suspect (14,15), rare drop-in allele 16 (p=0.01) in one of three replicates: LR 49.97 (FST form) vs 50 (ISFG-style counterfactual) |
| F4 | θ only on homozygote genotype freq, unconditional (L1300, L1345) | EuroForMix and ISFG's cited Curran et al. use conditional (sampling-formula) probabilities (S, N) | T at p=0.1, θ=0.03: FST hom 0.01270 vs Balding–Nichols given suspect typed 0.02689 (×2.117); het 0.02000 vs 0.02955 (×1.477). For a single-source full profile, `LR = 1/P(G)`, so FST's per-locus LR is larger by that factor (derived) |
| F5 | XML doc comment says homozygote `F = p + T * p * (1 - p)` (L1261); code computes `p*(p+θ(1−p))` (L1300) | — (S) | Comment only; no numeric effect |
| F6 | A replicate whose text is `NEG` passes `IsNullOrEmpty` (L882, L1057), enters the allele union as allele "NEG" with default frequency, forces drop-out of all contributor alleles, and counts as one drop-in (L944–946). The manual-entry control sets `txt.value = 'NEG'` (`FST.Web/Controls/Evidence.ascx.cs` L172) | Not in any document examined (S) | T: replicates `14,15 / NEG / 14,15`, suspect (14,15): LR 49.77 as coded vs 49.93 with NEG treated as an inconclusive (empty) replicate; Pn and Pd each ≈1000× smaller |
| F7 | `ReadDegradedDropoutRate` (L1501–1597, caps interpolated rates at 0.5 via `if (dropOutRate > 0.5m)` L1586) has no caller in the repository | Degradation not modelled on the executed path (S) | Degraded samples get template-amount tables only (derived) |
| F8 | Loci with `Pd == 0` or invalid `w` are silently skipped (L388–389, L509–510) | — (S) | Factor 1; direction case-dependent |
| F9 | Per-race LR stored as `float` (L513) | — (S) | IEEE-754 single precision: values above 3.402823e38 become +Infinity (derived; constant printed by the probe) |
| F10 | Drop-out depends on amount bracket, persons, Deducible, kit; drop-in on kit and ≤/>100 pg | Mitchell 2012 abstract (as relayed): drop-out "a function of" locus, template, cycles, number of contributors, mixture ratio, hom/het; drop-in a function of cycles only (P) | Whether "Deducible" encodes the mixture-ratio category, and whether ≤/>100 pg encodes cycle number, is **unknown** |

Public context (Basis: documentation, ProPublica 2017): FST "was used to analyze crime-scene evidence in about 1,350 cases over about 5 1/2 years" and "was phased out at the beginning of this year". According to a laboratory technical leader's affidavit, after a math problem was found in 2011 "the FST program was taken offline and portions of the software were re-coded". The lab ran a "performance check" rather than another full validation. ANSI/ASB 018 §4.4, published in 2020 and so later than these events, now requires "a validation or performance check of the affected software component".

### 8. EuroForMix source-level discrepancies

| # | Location | Quote | Effect |
|---|---|---|---|
| E1 | `R/calcMLE.R` L15, L16, L21 vs L54 | "`@param pC … Default is 0.`", "`@param lambda … Default is 0.`", "`@param normalize … Default is FALSE.`" vs `AT=50,pC=0.05,lambda=0.01,…,normalize=TRUE` | API users trusting the docs get drop-in on and frequencies normalized |
| E2 | `R/contLikMLE.R` L39–40 vs `R/contLikINT.R` L43–45 | `} else if(!BWS) {` / `BWS = FALSE #Back stutter must be ON if switched off` vs `BWS = TRUE #Back stutter must be ON if switched off` | The legacy wrappers disagree; contLikMLE's assignment is a no-op that contradicts its comment |
| E3 | `R/calcMLE.R` L25–26 vs L58, L172 | "`difftol NOT IN USE`", "`seed NOT IN USE`" vs `if(!is.null(seed)) set.seed(seed)` and the `valdiff>difftol` warning | Both parameters are in fact used |
| E4 | `R/prepareC.R` L200 | `freqsNotObserved = freqAll[!freqAll%in%names(freqs)]` compares values with names | Dead variable (no other reference); no effect |
| E5 | `NEWS.md` L2 | "The relationship calculation possibly defined under Hd is slightly wrong when applying a theta-correction." | Upstream-acknowledged open issue for kinship-under-Hd with θ>0 |
| E6 | `R/validMLEmodel.R` L31, L38 | `Beta(i-0.5, N-i+1.5)` envelope | §3 |

### 9. Performance and resource footprint (L1–L6)

Host for measurements: x86-64 Linux workstation (96 logical CPUs reported by `nproc`), Python 3.13.

| Level | EuroForMix 4.2.6 | FST snapshot | Basis |
|---|---|---|---|
| L1 authoring size | `R/*.R` 10,074 lines; `src/*.cpp,*.h` 1,306; tests 2,628; the six core files 1,405; GUI `R/efm.R` 2,959 | `.cs` excluding `obj/`, `bin/`, designer files: 13,453 lines; `FST.Common` 6,058 | measured (`wc -l`) |
| L1 effort (person-months, LLM tokens) | not measured | not measured | — |
| L2 build time / memory | not measured (no R toolchain) | not measured (no .NET) | — |
| L3 LR computation latency | not measured; published runtimes not retrieved. Work per likelihood evaluation ∝ `(A(A+1)/2)^NOU` per marker before restriction | not measured; rows `((n+1)(n+2)/2)^U` per locus for `n` distinct evidence alleles plus `w` | derived from L130/L189 and L693/L704 |
| L3 example | A=7 (6 alleles + Q), 3 unknowns: `28^3 = 21,952` combinations per marker | n=6, 3 unknowns: `28^3 = 21,952` rows per locus | derived |
| L4 execution of toy probes | `probe_efm_formulas.py` 0.047 s real | `probe_fst_port.py` 0.028 s real | measured (toy models only) |
| L5 diagnostic cost | `validMLEmodel` = one pass over restricted genotypes × alleles × replicates | no diagnostic beyond the `DEBUGOUT` CSV dump (compile-time `#if DEBUGOUT`) | derived from source |
| L6 memory | Two `fvec` (4-byte float) arrays per marker of length `(A(A+1)/2)^NOU` (`m_pGvec`, `m_genoWeightsHighest`, L190, L194) = 8 bytes per combination; 21,952 combos → 175,616 B per marker; A=10, 4 unknowns → 55^4 = 9,150,625 combos → 73,205,000 B per marker | not measured | derived |
| L6 artifact size | tarball 453,605 B; extracted 2,322,657 B | tarball 4,294,105 B; extracted 11,030,809 B; DB backups 1,096,192 + 1,071,104 B | measured (`ls -l`, `du -sb`) |

### 10. Comprehensibility and simplicity (C1–C2)

**C1 — human comprehension (derived).**

- *EuroForMix.* The case model has a small working set: `C−1` mixture proportions, `mu`, `omega`, `beta`, `xiB` and `xiF`, plus fixed `AT`, `pC`, `lambda`, `θ` and frequencies. Each output is locally interpretable (expected heights, PP-plot outliers with per-peak p-values). The numerical layer adds non-local concepts that are needed to judge an LR's precision: presearch, genotype restriction, three LR estimators, Laplace and "adjusted" LRs, and the paired-chain conservative quantile.
- *FST.* The per-locus arithmetic is simple (table lookups and products), so its local reasoning burden is low. Its footguns are non-local and invisible in the output: whole-locus removal driven by another race's table, `NEG` string handling, silent skips, and a θ treatment that differs from the documented comment. None of these shows up in the reported number. An analyst cannot tell from the LR which loci contributed.

**C2 — simplicity and orthogonality (derived).**

- FST's tables are a discretized, case-independent estimate of `P(D)` per (locus, amount bracket, persons, Deducible, kit). EuroForMix's `F_Gamma(AT; shape, scale)` derives the same quantity from case peak heights. Under a continuous model, the FST special cases (separate hom/het tables, the 100 vs 101 pg sentinel that encodes protocol, count-capped `Pc2`) become ordinary parameter values rather than code branches.
- Three FST mechanisms enforce one invariant, "omega must be a valid probability mass": the 0.97 removal, the `w<0||w>=1` null path, and the `Pd != 0` skip. A single Q-allele with explicit renormalization (EuroForMix `R/prepareC.R` L197–205) handles the same edge cases without discarding loci.
- In EuroForMix, the separate `contLik*` wrappers duplicate `calc*` entry points and have drifted (E2). Legacy wrappers that delegate entirely to one implementation would remove that class of inconsistency.

### 11. Validation analysis mapped to this domain (V1–V4)

- **V1, specification adequacy and calibration.** In this domain, V1 means Hd-true and Hp-true LR distributions, as required by SWGDAM §3.2.1–3.2.2 and ASB 018 §4.1.2. EuroForMix ships a non-contributor simulator (`R/calcTippet.R`) and a regression test suite (`tests/testthat/`, e.g. `test_logLik1contr_noDropin.R` "Testing that the numerical calculation of loglik is correct"). Mutation testing or spec-mutation kill rates are not reported by any examined subject (unknown). Whether FST's validation set was evaluated with the 0.97 rule active is **unknown**.
- **V2, differential and cross-implementation checks.** EuroForMix contains a differential test against the independent Forensim package (`tests/testthat/donttest_QualWithForensim.R`: "CHECKING VALUES BETWEEN calcQual and Forensim"). It is excluded from routine runs by its `donttest_` prefix, and covers the qualitative model only (source; not executed). The FST Python port here is a toy re-implementation, not a validated oracle. Inter-laboratory, cross-software studies were not examined.
- **V3, concurrency and numerical reproducibility.** Mostly not applicable; there is no hardware or physical-leakage channel. The relevant analogue is numerical reproducibility. Examples: OpenMP reduction order in EuroForMix (§2), sampler RNG dependence (`seed`, `diffSeed`), FST single-precision storage and float frequency arithmetic. None was measured.
- **V4, human mental models.** No examined source studies analyst comprehension of PG output. PCAST's critique of earlier subjective mixture interpretation is the only related material examined (not measured).

## Boundaries

- **Not examined:**
  - Full texts of Taylor et al. 2013, Bleka et al. 2016, Bright et al. 2016/2018, Perlin et al. 2011, Mitchell et al. 2012 and Coble & Bright 2019. Only abstracts were examined (for Mitchell 2012, as relayed by a search summary), plus Crossref metadata.
  - Hence: STRmix's exact variance model, priors, LSAE treatment, stutter regressions, HPD procedure and published run-to-run spreads; TrueAllele's model; EuroForMix's published validation numbers; FST's published equations.
  - The STRmix specifics in §4 come from a secondary summary and are unverified.
- **Not examined:** inter-laboratory or cross-software comparisons (e.g. NIST or multi-software studies) and published runtimes for any tool.
- **Unknown:** FST table values (drop-out, drop-in, frequencies, theta list, race list contents). These sit in an undecoded SQL Server backup, so the real-world frequency and magnitude of F1, F3, F4 and F6 are unknown. The toy numbers show mechanism and direction only.
- **Unknown:** whether this snapshot is the pre- or post-2011 re-coded FST version. Also unknown: whether the 0.97 rule, `NEG` handling and float storage were active during the published validation.
- **Unknown:** the meaning of the FST "Deducible" flag relative to the published mixture-ratio categories (F10), and whether `NEG` values can arrive through the file-upload path. Only the manual-entry control was traced.
- **Not measured:** all L1 effort figures, all L2/L3/L5 timings, EuroForMix peak RSS, and FST memory.
- **Not examined:** EuroForMix releases that predate the 2022–2023 engine, and SNP/MPS-specific code paths (`isLUS`, `MPSsymbol` branches). The findings should not be carried to them without re-checking.
- **Known not to apply:** FST's degradation-specific drop-out reader (F7) to any LR the pinned code computes, because the reader has no caller.
- **Unsupported (by upstream):** `calcINT` returns `NULL` with "Cannot calculate integral for at least 6 contributors!" (`R/calcINT.R` L129–131); kinship with INT stops with "Cannot (yet) calculate INT based LR where kinship is specified!" (L44).
- **Attractive but unestablished conclusions:**
  - "FST systematically overstated LRs." Removal (F1) and θ handling (F4) can each push either way or upward in toy cases, but no casework-scale estimate exists.
  - "EuroForMix's conservative LR is a lower credible bound on the LR" (it is not; §2).
  - "The `validMLEmodel` envelope is wrong enough to change conclusions" (the toy shows modest shifts that shrink with N).

## Evidence

Evidence acquired on 2026-11-20 (UTC); all observations on that date.

**Pinned source.**

- `oyvble/euroformix` @ `800c314c91235e2b9a67270437226d4dada325b4` (HEAD on 2026-11-20; commit message "version 4.2.6"). The codeload tarball's sha256 was `1ae26b937440abb02df2e4a82b5b59e8cc731c867f3f0a29ebb556aaf72c301d`. Files:
  - `src/EFMfastengine.cpp` L130, 189–195, 204–260, 268, 276, 295, 348–459, 525–606
  - `src/genoProbFuns.cpp` L4–27
  - `R/prepareC.R` L30, 185, 197–223, 243, 381
  - `R/calcMLE.R` L15–26, 54–58, 86–89, 134–172, 252–258, 284, 323–328
  - `R/calcLRmle.R` L8–26
  - `R/getParamLimits.R` L15–16
  - `R/calcINT.R` L7, 17, 44, 74, 129–131, 182–184
  - `R/calcLRint.R` L14–48
  - `R/contLikMCMC.R` L39–160
  - `R/calcLRmcmc.R` L23–82
  - `R/helpfunctions.R` L83–155
  - `R/validMLEmodel.R` L17–45
  - `R/contLikMLE.R` L33–42
  - `R/contLikINT.R` L37–51
  - `NEWS.md` L2
  - `tests/testthat/*`
- `propublica/nyc-dna-software` @ `5b3500de6f0b879350dd1b487218e590eeacc138` (HEAD on 2026-11-20; last commit 2017-10-20). The tarball's sha256 was `43bfe2f3d776396020af10ef6e4a6df6ccfe8e2707c319ac80da723ccfd833d1`. Files:
  - `FST.Common/Comparison.cs` L127, 142–240, 243–315, 374–548, 682–728, 748–998, 1010–1042, 1049–1081, 1161–1232, 1239–1256, 1261, 1268–1353, 1363–1383, 1396–1487, 1501–1597, 1604–1630
  - `FST.Common/Database.cs` L157–218, L1266–1370
  - `FST.Web/frmDefault.aspx.cs` L40, L148
  - `FST.Web/frmUpload.aspx.cs` L692–699
  - `FST.Web/Controls/Evidence.ascx.cs` L113–134, L171–173
  - `FST.Web/Admin/frmTestCenter.aspx.cs` L692
  - `Database/FST_DB.bak` sha256 `a106406ddef4e710ad5582ea916e6d9beba33c93d9d4bd24785dae13a23f8dc0`

**Literature and standards.** Every DOI below was verified against Crossref on 2026-11-20.

- Gill P., Gusmão L., Haned H., Mayr W.R., Morling N., Parson W., Prieto L., Prinz M., Schneider H., Schneider P.M., Weir B.S. "DNA commission of the International Society of Forensic Genetics: Recommendations on the evaluation of STR typing results that may include drop-out and/or drop-in using probabilistic methods." *Forensic Sci. Int. Genet.* 6:679–688 (2012). doi:10.1016/j.fsigen.2012.06.002. Full text read from PubMed Central PMC4689582.
- Perlin M.W., Legler M.M., Spencer C.E., Smith J.L., Allan W.P., Belrose J.L., Duceman B.W. "Validating TrueAllele® DNA Mixture Interpretation." *J. Forensic Sci.* 56:1430–1447 (2011). doi:10.1111/j.1556-4029.2011.01859.x. Abstract read.
- Taylor D., Bright J.-A., Buckleton J. "The interpretation of single source and mixed DNA profiles." *Forensic Sci. Int. Genet.* 7:516–528 (2013). doi:10.1016/j.fsigen.2013.05.011. Metadata only.
- Bleka Ø., Storvik G., Gill P. "EuroForMix: An open source software based on a continuous model to evaluate STR DNA profiles from a mixture of contributors with artefacts." *Forensic Sci. Int. Genet.* 21:35–44 (2016). doi:10.1016/j.fsigen.2015.11.008. Metadata only.
- Bright J.-A., Taylor D., McGovern C., Cooper S., Russell L., Abarno D., Buckleton J. "Developmental validation of STRmix™, expert software for the interpretation of forensic DNA profiles." *Forensic Sci. Int. Genet.* 23:226–239 (2016). doi:10.1016/j.fsigen.2016.05.007. Abstract read.
- Bright J.-A., Richards R., Kruijver M., et al. (46 authors). "Internal validation of STRmix™ – A multi laboratory response to PCAST." *Forensic Sci. Int. Genet.* 34:11–24 (2018). doi:10.1016/j.fsigen.2018.01.003. Abstract read.
- Coble M.D., Bright J.-A. "Probabilistic genotyping software: An overview." *Forensic Sci. Int. Genet.* 38:219–224 (2019). doi:10.1016/j.fsigen.2018.11.009. Metadata only.
- Mitchell A.A., Tamariz J., O'Connell K., Ducasse N., Budimlija Z., Prinz M., Caragine T. "Validation of a DNA mixture statistics tool incorporating allelic drop-out and drop-in." *Forensic Sci. Int. Genet.* 6:749–761 (2012). doi:10.1016/j.fsigen.2012.08.007. The abstract quote "Drop-out and drop-in probabilities were estimated empirically through analysis of over 2000 amplifications of more than 700 mixtures and single source samples" and the variable lists come from a web-search summary of the PubMed record, not a direct read.
- President's Council of Advisors on Science and Technology. *Forensic Science in Criminal Courts: Ensuring Scientific Validity of Feature-Comparison Methods* (September 2016). https://obamawhitehouse.archives.gov/sites/default/files/microsites/ostp/PCAST/pcast_forensic_science_report_final.pdf. The first ~200,000 characters of the extracted text were read, including the executive-summary finding quoted.
- SWGDAM. *Guidelines for the Validation of Probabilistic Genotyping Systems* (2015). Clause text (§3.2.1–3.2.3.2, §4.1.6.x, §4.1.12) was read as embedded verbatim in Cybergenetics' conformance document https://www.cybgen.com/reliability/SWGDAM2015TrueAllele.pdf; the original SWGDAM PDF was not fetched.
- ANSI/ASB Standard 018, *Standard for Validation of Probabilistic Genotyping Systems*, First Edition (2020). Clause text (§4.1–4.4) was read as embedded verbatim in https://www.cybgen.com/reliability/ANSI-ASBstd018TrueAllele.pdf (catalog page https://www.aafs.org/asb-standard/standard-validation-probabilistic-genotyping-systems).
- ProPublica, "Thousands of Criminal Cases in New York Relied on Disputed DNA Testing Techniques" (Sept. 4, 2017) and "Federal Judge Unseals New York Crime Lab's Software for Analyzing DNA Evidence" (Oct. 2017). Read at propublica.org.

**Execution (toy models only).** Commands, run in `support/` on an x86-64 Linux workstation with Python 3.13:

- `python3 probe_efm_formulas.py` produced `probe_efm_formulas.out`. Its incomplete-gamma and incomplete-beta implementations self-check against closed forms.
- `python3 probe_fst_port.py` produced `probe_fst_port.out`.

No R, C#, SQL Server, STRmix or TrueAllele code was run.

## Revalidation

1. **Pins resolve.** Run `gh api repos/oyvble/euroformix/commits/800c314c91235e2b9a67270437226d4dada325b4 --jq .sha` (and the same for `propublica/nyc-dna-software` at `5b3500de6f0b879350dd1b487218e590eeacc138`).
2. **EuroForMix gamma parametrization and drop-out** (cheapest discriminating check):
   `curl -sSL https://raw.githubusercontent.com/oyvble/euroformix/800c314c91235e2b9a67270437226d4dada325b4/src/EFMfastengine.cpp | grep -n "shape0 = 1/(omega\*omega)\|scale0 = mu/shape0\|pgamma(AT, shape1,scale0, 1, 1)\|log(1-m_pC)"`
   This should print L532, L533, L590/L596 and L257. For a newer EuroForMix, diff `calcEvidWeights` and `prepareMarker`.
3. **EuroForMix envelope:** `curl -sSL https://raw.githubusercontent.com/oyvble/euroformix/800c314c91235e2b9a67270437226d4dada325b4/R/validMLEmodel.R | tr -d '\r' | sed -n '29,45p'`, then re-run `python3 support/probe_efm_formulas.py`.
4. **EuroForMix conservative-LR construction:** `curl -sSL …/R/calcLRmcmc.R | tr -d '\r' | sed -n '47p;56p;63p;77p'`.
5. **FST 0.97 rule, drop-in and θ:**
   `curl -sSL https://raw.githubusercontent.com/propublica/nyc-dna-software/5b3500de6f0b879350dd1b487218e590eeacc138/FST.Common/Comparison.cs | tr -d '\r' | sed -n '267p;948p;1244,1253p;1300p;1345p;1405,1409p'`
   The FST repository is frozen (last commit 2017), so these lines should not move.
6. **Toy probes:** `python3 support/probe_fst_port.py`. The output must match `support/probe_fst_port.out` exactly; the rates are invented and the script is deterministic. Changing the rates changes magnitudes, not mechanisms.
7. **What would need repeating for stronger claims:**
   - Restore `FST_DB.bak` into SQL Server, extract the real tables, then re-run the port with them to quantify F1/F3/F4/F6 on real data.
   - Run EuroForMix under R on a public example (`inst/examples`) to measure L3/L6 and MCMC spread.
   - Obtain the full texts of Taylor 2013, Bright 2016 and Mitchell 2012 to replace the secondary STRmix description and the relayed Mitchell abstract.
