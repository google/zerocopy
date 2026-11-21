# Breast-cancer risk models and screening-invitation software: Gail/BCRAT, Tyrer–Cuzick, BOADICEA/CanRisk and Mirai implementations, their external validation, and the 2018 English invitation-cohort review

## Summary

- **The classic Gail/BCRAT absolute-risk computation is small and fully inspectable.** In the BCRA R package 2.1.2, absolute risk over `[T1, T2)` is a sum over one-year intervals between ages 20 and 90 of piecewise-constant competing-risk hazards. The breast-cancer hazard is `(1 − AR) · RR · λ1*` and the competing-mortality hazard is `λ2`. Relative risk switches at age 50, and there are 11 race/ethnicity codes, each with its own incidence, mortality, attributable-risk and coefficient tables. Every "unknown" input code (99) is recoded to the lowest-risk category. Running the pinned package confirmed that an all-unknown profile gets exactly the same risk as a profile that explicitly enters the lowest categories. `Basis: source + execution`
- **BCRA 2.1.2 accepts some inputs that are clearly invalid, and the outcome depends on the shape of the input data frame.** I ran the pinned package under R 4.4.1:
  - Biopsy counts of −1, −5, 1.5 and 150 are all silently recoded to the "≥ 2 biopsies" category, with no error flagged (`R/recode.check.R:34`).
  - The race check flags nothing when every row of the data frame has an invalid race code (`R/recode.check.R:90–91`). A one-row frame with race 12, 0 or −1 therefore gets `Error_Ind = 0`, and `absolute.risk` then stops with an R indexing error. Race 1.5 instead returns `NA`.
  - For race code 2 (African American), the checks that age at first birth is ≥ age at menarche and ≤ current age are switched off (`R/recode.check.R:55`).

  `Basis: source + execution`
- **The independent JavaScript port (bcra 1.0.1) matches the R package numerically but rejects six edge profiles that R accepts.** Agreement is within 5.0e-11 percentage points on every profile both implementations accept: 2,333 profiles, including 2,000 seeded random ones. The port upstream ships an R-generated reference fixture that records the negative-biopsy disagreement, but no test file at the pinned commit reads that fixture. `Basis: execution + source`
- **Head-to-head external validation.** In a 15,732-woman family-study cohort followed for a median of 11.1 years, BOADICEA and IBIS were well calibrated, with expected-to-observed ratios (E/O) of 1.05 and 1.03. BRCAPRO (0.59) and BCRAT (0.79) under-predicted. C-statistics were 0.70, 0.71, 0.68 and 0.60 (Terry et al. 2019). Earlier validations of the classic model were done in a single trial arm, and of the race-specific models in single cohorts. The image-based model Mirai reports discrimination separately for each of seven sites: Uno's C-index ranges from 0.75 to 0.84 (Yala et al. 2022). `Basis: documentation (peer-reviewed abstracts and full text where stated)`
- **The open BOADICEA/CanRisk web layer (`bws`) wraps a separate Fortran model executable that is not in the repository.** That executable is the source of the model version string (`<exe> -v`). Defaults are applied silently or with only a warning:
  - UK incidence and UK carrier frequencies.
  - The incidence option "Other" maps to UK rates.
  - If any family member is flagged Ashkenazi, the carrier frequencies are replaced with the Ashkenazi set.

  `Basis: source`
- **The 2018 English breast-screening incident was primarily a specification mismatch, not a failure of the invitation software** (Independent Breast Screening Review, HC 1799):
  - A November 2013 service specification said "until they reach the age of 71". The batch software had always selected women by year of birth.
  - About 196,000 women were contacted. The Review judged that about 129,000 of them (≈65 %) had been told incorrectly that they might have missed a screen. It found about 5,000 genuinely missed invitations over nine years, caused by user error and interval slippage, against 450,000 announced.
  - A genuine but small software interaction also existed. The age-extension trial's randomisation algorithm derived birth-year bounds from the *batch selection date*, which units could set into the next calendar year.
  - The discrepancy was noticed in 2017, when national data first became available through a new data system (BS-Select).

  `Basis: documentation (primary government report)`

## Applicability

**Subjects and how they relate.** The report covers four groups:
- Classic and extended absolute-risk models, read through one open implementation (`cran/BCRA` at the pinned revision, package version 2.1.2, dated 2020-06-30) and a derivative port (`epiverse/bcra-js` at the pinned revision, package version 1.0.1). The port's headers state that it is "a derivative work based on the BCRA R package".
- The pedigree/polygenic BOADICEA model, read through its open web-services layer (`CCGE-BOADICEA/bws` at the pinned revision).
- The image-based Mirai model, read through its research code base (`yala/Mirai` at the pinned revision).
- One national screening programme's invitation process, read through the Independent Breast Screening Review 2018 (England; laid before the House of Commons on 13 December 2018 as HC 1799).

The peer-reviewed papers are the model and validation definitions that these implementations claim to follow. The comparison between the R package and the JavaScript port is a differential test of one algorithm in two implementations. The other subjects are separate systems, compared only at the level of structure and validation design.

**Exact observations versus extensions.**
- Execution results apply only to the pinned BCRA source installed into R 4.4.1 (container image `docker.io/library/r-base:4.4.1`, digest `sha256:e7032f2f6fd273ee944a717b436bc66d1a89b1b90a9bbcaafcf1318d68a7d8b2`). They also apply to the pinned bcra-js source run under Node.js 22.11.0 (`docker.io/library/node:22.11.0-slim`, digest `sha256:f035ba7ffee18f67200e2eb8018e0f13c954ec16338f264940f701997e3c12da`).
- NCI's hosted web calculator and its SAS implementation were **not examined**. This report does not claim that the hosted calculator shares BCRA 2.1.2's input-handling behaviour. Its web form restricts many inputs to drop-down choices, so the malformed-input findings may not be reachable through it; this is unknown.
- BOADICEA numbers come from the cited papers. The `bws` findings concern only the Python/Django layer: inputs, defaults, process control and version reporting. The Fortran model was **not examined**.
- Mirai performance numbers come from the papers. The code findings concern only label construction, censoring and the export-time calibration step. The trained weights are distributed separately (in a Docker image) and were **not run**.
- The screening findings apply to England's programme as described in December 2018. Later changes to service specifications or IT systems were **not examined**.

## Findings

### 1. Model structures, inputs and baseline data

| Model | Structure | Risk-factor inputs | Baseline incidence / competing mortality | Development data | Basis |
|---|---|---|---|---|---|
| Gail 1989 ("model 1") | Proportional hazards; separate RR models below/at ≥ 50 because biopsy RR is smaller at older ages; baseline hazard = composite hazard × (1 − AR); competing risks | Age at menarche, age at first live birth, number of previous biopsies, number of first-degree relatives with breast cancer | Composite rates from BCDDP participants (screened annually) | BCDDP case-control data | documentation (abstract) |
| BCRAT invasive-only ("model 2", as coded in BCRA for race codes 1 and 4) | Same form, invasive cancer only | As above, plus atypical hyperplasia multiplier (0.93 / 1.00 / 1.82) | SEER white 1983–87 incidence, NCHS white 1985–87 mortality (inline comments, `R/absolute.risk.R:5–7, 51–53`) | — | source |
| CARE (race code 2) | Same form; RR model drops age at first birth and pools menarche categories (`R/recode.check.R:95–99`) | Menarche, affected mother/sisters, number of benign biopsies | SEER Black 1994–98; NCHS Black 1996–2000 (`R/absolute.risk.R:14, 60`) | 1,607 cases, 1,647 controls (CARE study) | documentation + source |
| Hispanic risk model (race codes 3 US-born, 5 foreign-born) | Nativity-specific RR/AR; US-born model drops menarche; biopsy ≥ 2 pooled with 1; first birth 25–29 pooled with 20–24 (`R/recode.check.R:102–116`) | First pregnancy age, benign biopsy, family history (+ menarche for foreign-born) | California Cancer Registry and SEER rates (comment "SEER Ca Hisp 1995-2004") | San Francisco Bay Area Breast Cancer Study | documentation + source |
| Asian American models (race codes 6–11) | Same form; relatives ≥ 2 pooled with 1 (`R/recode.check.R:119–120`) | Same four Gail factors | SEER18 1998–2002 by subgroup; NCHS 1998–2002 | (Matsuno et al. 2011, metadata only) | source |
| Tyrer–Cuzick (IBIS) | Bayes' theorem over the pedigree to obtain carrier likelihoods for BRCA1, BRCA2 and a hypothetical low-penetrance gene; refined by personal risk factors | Detailed family history plus personal/reproductive history | not examined | — | documentation (abstract) |
| BOADICEA (Lee et al. 2019) | Segregation model: truncating variants in BRCA1, BRCA2, PALB2, CHEK2, ATM; 313-SNP PRS explaining 20 % of polygenic variance; residual polygenic component; lifestyle/hormonal/reproductive factors; mammographic density; missing data allowed | Pedigree, genetic tests, PRS, risk factors, density | Country-specific incidence files selected at run time (see §4) | — | documentation (abstract) + source |
| Mirai | Deep network over four standard views (L CC, L MLO, R CC, R MLO); additive-hazard output for years 1–5; predicts missing risk factors; adversarial training for device invariance | Images, optionally risk factors | n/a (trained on outcomes) | MGH screening mammograms | documentation (README, paper) + source |
| iCARE framework | Builds a model from three user inputs: relative-risk model, age-specific incidence, risk-factor distribution; handles missing covariates by model averaging; SNPs from odds ratios and allele frequencies | User-specified | User-specified | — | documentation (abstract) |

**Absolute-risk judgement (BCRA 2.1.2, `R/absolute.risk.R:166–187`).** Let `j` index one-year intervals with `Strt_Intvl = floor(T1) − 20 + 1` and `NumbrIntvl = ceiling(T2) − floor(T1)`. Each interval contributes over a length `ℓ_j` (a partial year at either end). Define `h_j = (1−AR_j)·RR_j·λ1_j` and `Λ_j = h_j + λ2_j`. Then

```text
AbsRisk(T1,T2) = 100 · Σ_j  (h_j / Λ_j) · exp(−Σ_{k<j} Λ_k ℓ_k) · (1 − exp(−Λ_j ℓ_j))
RR_j = exp(LP1) for ages < 50, exp(LP1 + NB_Cat·β5) for ages ≥ 50
LP1  = NB·β1 + AM·β2 + AF·β3 + NR·β4 + AF·NR·β6 + log(R_Hyp)
```

The code is (lines 182–185):

```r
lambdaj <- lambda1[j_intvl]*One_AR_RR[j_intvl]+lambda2[j_intvl]
PI_j <- ((One_AR_RR[j_intvl]*lambda1[j_intvl]/lambdaj)*exp(-Cum_lambda))*(1-exp(-lambdaj*IntgrlLngth))
RskWrk <- RskWrk+PI_j
Cum_lambda <- Cum_lambda+lambdaj*IntgrlLngth
```

`Avg_White = 1` returns the "average woman" comparator. It sets `One_AR_RR` to 1 for all ages, so there is no `(1 − AR)` factor. For race codes 1 and 4 only, it also substitutes the SEER 1992–96 / NCHS 1992–96 rate vectors (`R/absolute.risk.R:153–165`). For the other race codes, it uses the same race-specific rates as the individualized risk. `Basis: source`

### 2. BCRA 2.1.2 input recoding, defaults and versioning

**Recoding rules and defaults** (`R/recode.check.R`; row-wise unless noted). The `Category` column gives what each raw input becomes:

| Input | Category | Line(s) | Notable property |
|---|---|---|---|
| `T1`, `T2` | error if `T1 < 20`, `T1 ≥ 90`, `T2 > 90` or `T1 ≥ T2` | 11–15 | Fractional ages are accepted |
| `N_Biop` 0 or 99 with `HypPlas ≠ 99` | error "A" | 24–25 | — |
| `N_Biop` in (0,99) with `HypPlas ∉ {0,1,99}` | error "B" | 28–29 | — |
| `N_Biop` 0 or 99 | 0 | 32 | unknown ⇒ "no biopsy" |
| `N_Biop` == 1 | 1 | 33 | — |
| any other value not yet categorized | 2 | 34 | see defect below |
| `AgeMen` ≥ 14 and ≤ T1, or 99 | 0 | 39 | unknown ⇒ latest menarche (lowest risk) |
| `AgeMen` 12–13.x | 1 | 40 | — |
| `AgeMen` in (0,12) | 2 | 41 | `AgeMen = 5` is accepted (executed) |
| `AgeMen` > T1 (not 99) | error | 42 | — |
| `Age1st` < 20, or 99 | 0 | 48 | unknown ⇒ youngest first birth (lowest risk); negative values accepted |
| `Age1st` 98 (nulliparous) | 2 (pooled with 25–29) | 50 | — |
| `Age1st` < AgeMen or > T1 | error, **except race 2** | 52–55, 97 | race-2 override comes after the error assignment |
| `N_Rels` 0 or 99 | 0 | 59 | unknown ⇒ no affected relatives |
| `HypPlas` 99 when biopsied | `R_Hyp = 1.00` | 80 | unknown ⇒ neutral multiplier |
| `Raw_Ind = 0` | all edit/consistency checks skipped | 66–73 | comment says "use this option at your own risk" |

Running the pinned package confirmed the "unknown ⇒ lowest category" rule. A white woman aged 40→50 with every factor set to 99 and the same woman with explicit lowest categories (`N_Biop=0, AgeMen=14, Age1st=19, N_Rels=0`) both receive **0.894502598596 %**. The equivalent pair for race code 3 both receive **1.15387100777 %**. `Basis: execution`

**Defect 1: the biopsy-count recode accepts any value.** At the pinned revision, line 34 reads:

```r
NB_Cat[which(NB_Cat == -1 & (data$N_Biop >= 2 | data$N_Biop != 99))] <- 2
```

Because the condition uses `|` (or), any value that reaches this line and is not 99 becomes category 2. Executed results:
- `N_Biop = −1, −5, 1.5, 150` all give `NB_Cat = 2`, `Error_Ind = 0` and 7.54082063321 % 10-year risk, which equals the explicit `N_Biop = 2` control.
- `N_Biop = 98` also gives category 2. Both implementations accept 98.

The upstream JavaScript port's R-generated fixture records the same result for `N_Biop = −1` (case 284, "Negative biopsies": `NB_Cat = "2"`, `Error_Ind = 0`, `AbsRisk = 7.5408206332`). `Basis: source + execution`

**Defect 2: the race check depends on the other rows in the frame.** Lines 89–93 read:

```r
set_Race_missing <- data$Race
Race_range<-seq(1,11)
set_Race_missing[-which(data$Race %in% Race_range)]<-"U"
...
Error_Ind[which(is.na(NB_Cat) | ... | set_Race_missing == "U")] <- 1
```

If no row has a valid race, `which(...)` is `integer(0)`. Negating an empty index selects nothing in R, so no row is marked `"U"`. Execution confirms this with each invalid row run as a one-row data frame:

| One-row input race | `Error_Ind` | `absolute.risk` outcome |
|---|---|---|
| 12 | 0 | R error `subscript out of bounds` |
| 0 | 0 | R error `replacement has length zero` |
| −1 | 0 | R error `number of items to replace is not a multiple of replacement length` |
| 1.5 | 0 | returns `NA` (R truncates the matrix index; `relative.risk` yields `NA` because `CharRace` is `"??"`) |
| same rows inside a frame with valid rows | 1 | skipped (returns `NA`) |

`Basis: source + execution`

**Defect 3: the race-2 consistency override.** Line 55 sets `AF_Cat[which(data$Race == 2)] <- 0` *after* line 53 has marked `Age1st > T1` as `NA`. Executed results for race 2:
- `Age1st = 45` with `T1 = 40` returns 2.73005757281 % with `Error_Ind = 0`.
- `Age1st = 10` with `AgeMen = 12` returns the same value.
- For race 1, the `Age1st = 45` control is rejected.

Age at first birth is not a covariate in the CARE model, so the value does not change the risk. The override does, however, hide data-entry errors that would be flagged for every other race. `Basis: source + execution`

**Versioning and dead tables.**
- `DESCRIPTION` identifies the package as version 2.1.2 (2020-06-30). It cites Gail 1989 and the Hispanic model (doi:10.1093/jnci/djw215; the author's name is misspelled "Marthew PB"). There is no runtime version accessor beyond R's `packageVersion`.
- `R/absolute.risk.R:12–13` and `:58–59` define `White_nlambda1` and `White_nlambda2` ("SEER white 1995:2003", "NCHS white 1995:2003"). A search of the package's `R/` sources finds these identifiers only at their definitions, so the more recent white incidence and mortality vectors are dead code. Computations for race code 1 use the 1983–87 and 1985–87 vectors.
- The comment at `R/recode.check.R:62` ("NR_Cat=2 is pooled with NR_Cat=2") misstates the code, which pools to 1.

`Basis: source`

### 3. Differential test: R package versus JavaScript port (shared synthetic profiles)

**Design.** `support/bcra_diff/` contains a profile generator, an R runner, a Node runner and a comparator. The 2,374 shared profiles comprise:
- the inputs of all 342 rows in the port's six R-reference fixture files;
- 27 hand-written edge rows, plus 5 rows that are also run alone as one-row data frames in R;
- 2,000 random profiles drawn with seed 20261121 from the documented input domains, all valid.

Each implementation computes individualized and average risk.

**Results** (executed 2026-11-21; Linux x86_64 virtual machine, 96 vCPU Intel Xeon @ 2.60 GHz, containers with networking disabled):

| Check | Result |
|---|---|
| R 2.1.2 now vs R values recorded in the port's fixtures | 342 rows; 0 `Error_Ind`/NA mismatches; max \|ΔAbsRisk\| = 5e-11 percentage points |
| Random set, both valid | 2,000 / 2,000 agree, max \|Δ\| = 4.98e-11 |
| Fixture set | 318 agree (≤ 1e-9); 23 both reject; **1 R accepts / JS rejects** (negative biopsies) |
| Edge set (frame mode) | 15 agree; 11 both reject; **6 R accepts / JS rejects** |
| Average-risk agreement where both valid | max \|Δ\| = 4.95e-11 |

The six edge disagreements are `N_Biop ∈ {−1, −5, 1.5, 150}`, and race 2 with `Age1st > T1` or with `Age1st < AgeMen`. The JavaScript port rejects these with the messages "Invalid number of biopsies", "Age at first birth cannot be greater than initial age" and "Age at first birth cannot be less than age at menarche". The port's biopsy rule accepts only `0`, `99`, `1`, or `2 ≤ n < 99` (`packages/bcra/src/core/recode-check.js:204–221`). Its first-birth checks run before the race-2 override (`:346`, `:358`, then `:364`).

**Why the existing cross-validation did not catch this.**
- The port's `test/README.md` lists `special-values.test.js`, `validation-errors.test.js` and `numerical-accuracy.test.js` as "(optional)".
- At the pinned commit, `test/cross-validation/` contains only `race-specific.test.js`, `age-edge-cases.test.js` and `pattern-numbers.test.js`, and only those three import an R-reference fixture.
- The R-generated `validation-errors.json` fixture, which contains the disagreeing case 284, is therefore not consumed by any test.

`Basis: execution + source`

**Throughput** (same host; a single timed run each, so treat these as order-of-magnitude figures):
- `absolute.risk` in R: 0.313 s for 2,000 profiles, i.e. 156.5 µs per profile.
- `calculateRisk` in JavaScript: 0.010 s for 2,000 profiles, i.e. 5.1 µs per profile.
- R full pipeline (`recode.check`, `relative.risk`, two `absolute.risk` calls) on 2,374 rows: 0.925 s.
- `R CMD INSTALL` of the pinned source: 1.8 s wall time.

`Basis: execution`

### 4. BOADICEA/CanRisk web services (`bws`): inputs, defaults, process control, versions

- **Engine boundary.** `bws/calc/calcs.py:315–385` runs the model as a subprocess. The command is `[HOME/EXE, -s <params>, -e Data/coeffs-<NAME>_<ethnicity>.nml, -o <out>, -p -rj -rl -rr -ry, <batch file>, <INCIDENCE><rates>.nml]`, with a 240-second timeout (`bws/settings.py:51`, `FORTRAN_TIMEOUT = 60*4`). The breast-cancer executable is `boadicea.exe` under `FORTRAN_HOME` (`settings.py:90–93`); it is not in the repository. Output is parsed from text sections (`## REMAINING LIFETIME RISK`, `## LIFETIME RISK`, `## 10-YEAR RISK`, `## PROBABILITIES`; `calcs.py:186–224`). `Basis: source`
- **Version identity.** The version is whatever the executable prints for `-v`, with `.exe` and newlines stripped (`calcs.py:280–312`). It is attached to the API response (`bws/rest_api.py:154`). The repository revision does not determine the model version. `Basis: source`
- **Calculation options** (`bws/calc/model.py:13–65`):
  - lifetime risk: proband age set to 20 and censor age to 80;
  - 10-year risk: ages 40–50;
  - "NHS protocol" 10-year risk: only for breast-cancer model targets under 50 without a diagnosis;
  - remaining lifetime risk from the actual age.

  Risks are not computed when the target is over `MAX_AGE_FOR_RISK_CALCS = 79` (`settings.py:68`; `pedigree.py:337`). `Basis: source`
- **Defaults and silent substitutions**:

  | Setting | Default / substitution | Location |
  |---|---|---|
  | Carrier frequencies | `population = data.get('mut_freq', 'UK')` | `model.py:102` |
  | Incidence | UK; the menu option "Other" maps to UK rates | `settings.py:164–181` (line 180 `('Other', 'UK')`) |
  | Ashkenazi | if any family member is flagged Ashkenazi and the population is not, frequencies are replaced (warning only) | `rest_api.py:109–117` |
  | Test sensitivity | DEFAULT BRCA1 0.98, BRCA2 0.99, PALB2 0.99, ATM 0.99, CHEK2 0.99, BARD1 0.99, RAD51C 0.98, RAD51D 0.98; a LEGACY set also exists | `settings.py:141–162` |
  | "UK, non-European" frequencies | differ from "UK" only in CHEK2 (0.00109 vs 0.00373) | `settings.py:99–118` |
  | Ethnicity with non-UK incidence | error | `rest_api.py:128–130` |

  `Basis: source`
- **Implementation has moved beyond the 2019 paper.** `BC_MODEL['GENES']` lists eight genes: BRCA1, BRCA2, PALB2, CHEK2, ATM, BARD1, RAD51C and RAD51D (`settings.py:95–96`). Lee et al. 2019 describes five. The PRS menu includes `BCAC 313` alongside 3,820-, 309-, 307- and other-SNP scores, with ancestry-specific files (`settings.py:182–211`). The validation papers cited here therefore describe an earlier model than the one this revision runs. `Basis: source + documentation (derived comparison)`
- **Baseline comparator.** The "baseline" risk recomputes the model for a single-person pedigree. The target keeps only age, year of birth and any first breast-cancer diagnosis, and has default genetic tests, risk-factor code `0`, no height, no density and no PRS (`bws/calc/risks.py:72–168`). `Basis: source`

### 5. External validation results

| Study | Population | Follow-up | Calibration | Discrimination | Basis |
|---|---|---|---|---|---|
| Costantino et al. 1999 | 5,969 white women aged ≥ 35, BCPT placebo arm | mean 48.4 months | E/O 0.84 (0.73–0.97) for model 1 (total breast cancer); 1.03 (0.88–1.21) for model 2 (invasive). Model 1 by age ≤ 49 / 50–59 / ≥ 60: 0.91 / 0.96 / 0.66. Model 2: 0.93 / 1.13 / 1.05. Both over-predict in the top quintiles of predicted 5-year risk and under-predict in the bottom quintiles | not in abstract | documentation (abstract) |
| Gail et al. 2007 (CARE) | Eligibility screening data from the STAR trial; independent WHI data | — | Well calibrated in WHI, except under-estimation in African American women who had had biopsies | Concordance lower than BCRAT's; 30.3 % vs 14.5 % of African American women at ≥ 1.66 % 5-year risk under CARE vs BCRAT | documentation (abstract) |
| Banegas et al. 2016 (Hispanic model) | WHI | — | **O/E** (observed/expected, the inverse of E/O) 1.07 (0.81–1.40) US-born; 0.66 (0.41–1.07) foreign-born, i.e. over-prediction | AUC 0.564 (0.485–0.644) US-born; 0.625 (0.487–0.764) foreign-born | documentation (abstract) |
| Terry et al. 2019 | ProF-SC: 18,856 women from Australia, Canada and the USA; 15,732 selected (aged 20–70, family history available); 619 cancers | median 11.1 y (IQR 6.0–14.4) | E/O BOADICEA 1.05 (0.97–1.14); IBIS 1.03 (0.96–1.12); BRCAPRO 0.59 (0.55–0.64); BCRAT 0.79 (0.73–0.85). BRCA-negative: 1.02 / 1.00 / 0.53 / 0.97. BRCA-positive: 1.17 / 1.14 / 0.80 (BCRAT not reported) | C 0.70 / 0.71 / 0.68 / 0.60 | documentation (abstract) |
| Lee et al. 2019 (BOADICEA) | UK population distribution (model-predicted, not observed) | — | — | Predicted lifetime risk 2.8 % (1st percentile) to 30.6 % (99th); 14.7 % predicted at 17–< 30 %, 1.1 % at ≥ 30 % | documentation (abstract) |
| Yala et al. 2021 (Mirai) | Held-out tests at MGH, Karolinska and CGMH | up to 5 y | not in abstract | C-index 0.76 (0.74–0.80), 0.81 (0.79–0.82), 0.79 (0.79–0.83). 5-year AUC higher than Tyrer–Cuzick (p < 0.001). At MGH, 41.5 % of 5-year cancers flagged high-risk vs 22.9 % by Tyrer–Cuzick lifetime risk | documentation (abstract, README) |
| Yala et al. 2022 (Mirai) | 128,793 mammograms from 62,185 patients at 7 sites in 5 countries; 3,815 followed by cancer within 5 years | 1–5 y | not in abstract | Uno's C, reported **per site**: MGH 0.75, Novant 0.75, Emory 0.77, Maccabi-Assuta 0.77, Karolinska 0.81, CGMH 0.79, Barretos 0.84 | documentation (abstract) |

Terry et al. also report that limiting the family-history input to first- and second-degree relatives did not appreciably change BOADICEA and IBIS scores. `Basis: documentation`

**Derived reading.**
- BCRAT's overall under-prediction in Terry et al. (0.79) disappears in BRCA-negative women (0.97). This is consistent with BCRAT's family-history input (count of affected first-degree relatives, capped at "2+") being too coarse for a family-enriched cohort.
- This reading is an inference from the two subgroup ratios. The paper's own causal analysis was **not examined**.

### 6. Mirai code base: labels, censoring and calibration

- **Label rule** (`onconet/datasets/csv_mammo_cancer.py:114–135`, with `max_followup = 5` at `:145`). The years-1–5 indicator vector is `y_seq` and the per-year evaluation mask is `y_mask`.
  - A row counts as a positive if `0 ≤ years_to_cancer < 5`. It is then marked positive from year `years_to_cancer` onward.
  - A row counts as a negative if `years_to_last_followup > 0`. It is then censored at `min(years_to_last_followup, 5) − 1`, and the mask covers years `0..time_at_event`.
  - Cancers found on the index mammogram are entered as `years_to_cancer = 0`, per `README.md:89`.
  - A cancer at year ≥ 5 with follow-up ≥ 5 is therefore a full-length negative.

  `Basis: source`
- **Calibration is applied only to exported predictions.** `scripts/main.py:123–137` loads a pickled calibrator list and replaces each horizon's raw value with `callibrator[i].predict_proba([[raw_val]])[0,1]`, one calibrator per year. The command-line help says the calibrator was "Produced for a single model on development set using Platt Scaling" (`onconet/utils/parsing.py:318`). The validation snapshot filename is `MIRAI_FULL_PRED_RF.callibrator.p` (`configs/validate_mirai.json`). The printed AUCs come from the raw scores. `Basis: source`
- **Derived consequence.** Each horizon is calibrated independently. Nothing in the export code enforces that calibrated 1- to 5-year risks are non-decreasing, even though the raw additive-hazard outputs are cumulative. Whether the shipped calibrators preserve monotonicity is **unknown**, because the pickle was not inspected.
- **Inclusion constraints** (`README.md:26`):
  - All four "For Presentation" views are required.
  - Marked-up or "For Processing" images are not supported.
  - Study images came from Hologic Selenia / Selenia Dimensions devices, and the README says "We have yet tested Mirai on other machines" (the authors evidently mean "not yet tested").
  - The validation configuration pins `img_size` 1664×2048, `img_mean` 7047.99, `img_std` 12005.5, `batch_size` 1 and `dataset` `csv_mammo_risk_all_full_future`.

  `Basis: documentation + source`
- **Discrimination metric.** `onconet/utils/c_index.py` is "Adapted from" lifelines' concordance code and accepts a `censoring_dist` argument (`get_censoring_dist`). That matches the Uno-style censoring-weighted C reported in the 2022 paper. Equivalence to the paper's estimator was **not verified**. `Basis: source`

### 7. The 2018 English invitation-cohort review

**How invitation cohorts were defined and computed.** Paragraph numbers are those of HC 1799. `Basis: documentation`
- *Policy.* From the programme's start, documents said "50–70" or "up to and including 70". The Review "has been unable to find any document that sets out how 70 should be defined (i.e. when a woman turns 70 or until just before her 71st birthday)" (para 1.12). The November 2013 Service Specification added "Ensure that women who have already attended for screening are offered screening again within 36 months of their previous screening, until they reach the age of 71" (para 1.25). The Review calls this clarification "too late and incorrect" (Executive summary item 1). The performance indicator wording "aged 53 to 70" was equally unspecific (para 3.18).
- *Implementation.* Women are invited in GP-practice batches by **year of birth**. The final routine screen falls in the year a woman turns 68, 69 or 70, and about one sixth are 67 at that screen (paras 2.5–2.9).
  - Three systems are involved: NBSS (78 instances, one per unit, Hitachi-maintained, PHE contract), NHAIS (82 databases) and BS-Select (introduced 2016, NHS Digital, PHE product owner). Staff enter batch parameters twice, in NBSS and in BS-Select. Only the BS-Select criteria determine the batch; the NBSS fields are legacy (para 2.15).
- *Age-extension trial algorithm (2009).* Batches requested ages 47–73. NBSS assigned code 0 to women aged 50–70, code 1 to those turning 47–49 and code 2 to those turning 71–73. Each batch was randomly allocated to add either the code-1 or the code-2 women (paras 2.16–2.17).
  - The minimum core birth year was computed as *batch selection year − 70*. Units could enter a selection date in the next calendar year. Some women aged 69 therefore received code 2 and were excluded from lower-arm batches (para 2.25, with a worked example).
  - The choice of selection date as input had been queried by the maintainer in 2009 and confirmed by the then product owner (para 2.26).

**Detection.** After BS-Select gave the first national view of the data, PHE reviewed it in 2016–2017. The review was checking that units which had been removed from the trial now invited the correct ages. During this work PHE "noticed that some women aged 69 were being randomised out by the AgeX algorithm" (paras 2.24, 4.5). The anomaly was reported at a January 2018 Research Advisory Committee meeting, and an incident was declared. PHE formally advised the Department on 15 March 2018 (para 4.14).

PHE then applied the 2013 specification as policy, on legal advice. It did so despite early advice from its own quality-assurance lead that the programme had never defined age in years and months (para 4.11). This choice inflated the affected population.

**Numbers** (Annex C and paras 4.17–4.18):

| Stage | Women |
|---|---|
| Announced in Parliament on 2 May 2018 (highest possible estimate) | 450,000 |
| Revised and announced on 4 June 2018 | 195,565 |
| Contacted by the Patient Notification Exercise | ≈ 196,000 |
| Later found by PHE to have been wrongly included | ≈ 74,000 |
| Remaining list given to the Review | ≈ 122,000 |
| Review: genuinely missed (user error, interval slippage, unactioned failsafe reports) | ≈ 5,000 over nine years |
| Review: final invitation in the year they turned 68, "in keeping with the way the IT systems had been designed" | ≈ 117,000 |
| Review: incorrectly told they might have missed a screen | ≈ 129,000 of 196,000 (≈ 65 %) |

At any given time at least one in five units was missing the 36-month interval (para 2.23).

**Recommended controls** (Executive summary):
- one published Service Specification stating the exact stopping age (1.1), used as "the central document" for implementation and assurance (1.2);
- reduced manual double entry across NBSS and BS-Select (2.1);
- overarching governance of the interacting IT systems, risk-based by clinical harm (2.2);
- IT reviewed against the clarified policy (2.3);
- a more specific eligible-population indicator (3.2);
- quality assurance against the policy (3.3) and contract management (3.4);
- incident protocols that include the owners of the supporting IT (4.1);
- the trial to continue to its planned end (6.1). The Review established "that the algorithm was operating as designed".

**Specification-conformance probe (toy model).** `support/invitation_conformance_toy.py` encodes the three prose rules above:
- `SPEC_71`: age at screening < 71;
- `YOB_70`: screening year − birth year ∈ [50, 70];
- `AGEX_SEL`: the year-of-birth rule with the code-2 bound taken from the selection year.

It checks the property *policy-eligible ⇒ implementation-includes* over a grid of 572 birth dates × 48 screening months × selection-date offsets {−45, 0, +45} days, 82,368 cases in all.

| Output (toy grid, not the programme) | Count |
|---|---|
| Review's worked example (born 1945-12-15, screened 2015-12-01): `AGEX_SEL` with selection 2015-11-01 / 2016-01-04 | included / **excluded** (age 69) |
| `SPEC_71` true and `YOB_70` false | 4,038 (all at age 70) |
| `YOB_70` true and `SPEC_71` false | 0 |
| `YOB_70` true and `AGEX_SEL` false | 209 |
| `AGEX_SEL` true and `YOB_70` false | 416 (selection date in the previous year admits older women) |

`Basis: execution (toy model of the rules as described in prose; not NBSS or BS-Select code)`

The probe shows that the cohort definitions are executable predicates that can be compared directly. The 2013 text and the as-built rule disagree only at age 70, and a selection-date offset moves the boundary in either direction.

### 8. Performance and resource footprint (six levels)

| Level | Gail/BCRAT (BCRA 2.1.2, bcra 1.0.1) | BOADICEA/CanRisk (`bws`) | Mirai | Screening invitation systems |
|---|---|---|---|---|
| L1 authoring velocity / maintenance cost | not measured | not measured. CanRisk usage: > 3,100 registrations and 98,000 calculations in the first 9 months (Carver et al. 2021); usage, not velocity | not measured | not measured. The Review cites manual double entry as an error source (qualitative) |
| L2 toolchain build | `R CMD INSTALL` 1.8 s wall (measured); bcra-js runs from source with no build step | not measured (Fortran executable not public) | not measured (Python 3.6 environment, Docker image distributed separately) | not applicable |
| L3 compile / elaboration latency | not applicable | not applicable | not applicable | not applicable |
| L4 execution | R `absolute.risk` 156.5 µs/profile; JavaScript 5.1 µs/profile (measured, n = 2,000); R full pipeline 0.925 s / 2,374 rows | Configured upper bound 240 s per subprocess (`FORTRAN_TIMEOUT`, source); actual latency not measured | not measured. Validation config lists 4 GPUs, 24 workers, batch size 1 (source) | BS-Select → NBSS transfer "within 24 hours"; NHAIS → NBSS previously "several weeks" (Review para 2.13) |
| L5 proof / certificate checking | not applicable (no certificates) | not applicable | not applicable | not applicable |
| L6 footprint | R sources 29,955 B; `data/` 4,116 B; installed package 90,776 B; bcra-js `src/` 106,373 B; R container image 880 MB, Node image 226 MB (all measured) | Repository checkout 1.4 MB (measured); `MAX_PEDIGREE_SIZE = 275` (source) | Snapshots not in repository; size not measured | not measured |

### 9. Comprehensibility and model refinement

- **C1, working-memory load.**
  - The Gail computation needs about seven concepts: four categorized factors, the hyperplasia multiplier, the age-50 switch, race-specific tables and one integration loop. All of them are visible in about 380 lines of R.
  - The hazards are the hard part to audit. The "unknown ⇒ lowest category" convention is spread across four separate assignments rather than declared once, and the race-specific poolings are applied in two places: the raw branch (`:43–44, :54–55, :62–63`) and again after the error check (`:95–120`). A reader must follow the assignment order to know which rule wins, which is how defect 3 arises.
  - BOADICEA's local reasoning burden is much higher: segregation analysis over pedigrees, eight genes, a PRS and a residual polygenic term. The human-auditable surface of the open code is the input contract and the defaults table, not the model.
  - Mirai's per-prediction reasoning is not human-auditable. Its auditable surface is the label rule, the inclusion criteria and the calibration step. `Basis: derived`
- **C2, one mechanism per invariant.**
  - *Input validity.* BCRA enforces it with a mixture of `which()` masks, NA sentinels and string sentinels ("A", "B", "U", "??"). The race check's dependence on the other rows comes from using a vectorized negative index as a set complement. A single row-wise predicate `valid(row)`, evaluated before any recoding, would turn all three defects into ordinary rejected cases. It would also remove the `Raw_Ind = 0` escape hatch as a separate code path. The JavaScript port is essentially that refactoring: per-field validators that return `{valid, error}`.
  - *Cohort eligibility.* The screening incident had three representations of one invariant: the policy text, the KPI wording and the batch rule. None of them was the executable source of truth. The minimal shared abstraction is an eligibility predicate over (birth date, screening date, previous screen) that both the specification and the software are tested against, as in §7. `Basis: derived`

### 10. How implementations and claims are validated (V1–V4)

- **V1, specification adequacy and non-vacuity.**
  - BCRA: the port's cross-validation is a golden-interpreter differential test, with R as oracle and tolerance ±0.01 percentage points absolute risk. It covers only valid-input fixtures; the invalid-input oracle file exists but is unused.
  - The differential test in this report adds 2,000 random valid profiles and malformed inputs. No mutation or property-based testing of either implementation was found.
  - BOADICEA and Mirai: model adequacy is assessed by external calibration and discrimination (§5). The software layers were not differentially tested here.
  - Screening: the Review's central finding is a specification-adequacy failure, in which the 2013 text did not describe the as-built system. The proposed control is a specification-conformance test (§7). `Basis: source + execution + documentation`
- **V2, compiler and checker soundness.** Not applicable as such. The nearest analogue is cross-language porting (R → JavaScript), validated above to 5e-11 percentage points on valid inputs. `Basis: execution`
- **V3, concurrency, crash and physical leakage.** Not examined. The `bws` subprocess model relies on per-request working directories and a timeout. Isolation between concurrent requests was **not examined**.
- **V4, field validation and human comprehension.**
  - Mirai's seven-site validation is the closest analogue to real-data replay; results are reported per site.
  - Terry et al. tested reduced-input operation. Its limited family history mirrors what clinicians actually collect.
  - For the screening programme, the Review's survey of affected women covers impact, not mental-model testing of operators. The failure is attributed to error-prone manual workflows across two systems, and **no** controlled operator study was reported. `Basis: documentation`

## Boundaries

- **Not examined:**
  - NCI's hosted BCRAT web calculator and SAS macro (version, input constraints, whether the defects in §2 are reachable).
  - The IBIS (Tyrer–Cuzick) software.
  - BRCAPRO/BayesMendel.
  - The BOADICEA Fortran executable.
  - The trained Mirai weights and calibrator pickles.
  - The full texts of Gail 1989, Costantino 1999, Gail 2007, Banegas 2016, Tyrer 2004, Lee 2019, Carver 2021, Terry 2019 and the Mirai papers; only their abstracts and the Mirai README were read. Numbers come from the abstracts.
  - Matsuno et al. 2011 (Asian American model, DOI 10.1093/jnci/djr154): metadata only.
  - The iCARE package source and execution: abstract only.
  - Screening-programme changes after December 2018.
- **Unknown:**
  - Whether any deployed calculator passes negative or fractional biopsy counts into BCRA 2.1.2.
  - Whether Mirai's per-horizon calibrators preserve monotone cumulative risk.
  - Why BCRAT under-predicts in Terry et al. overall but not among BRCA-negative women. §5's interpretation is an inference.
  - Whether the dead 1995–2003 white incidence and mortality vectors in BCRA reflect an intended but unimplemented update.
- **Known not to apply:** The R/JavaScript disagreements concern input validation only. No numerical disagreement exceeding 5e-11 percentage points was observed on any profile both implementations accepted, so this report provides no evidence that the port's risk *values* differ from R's.
- **Attractive stronger conclusions that the evidence does not establish:**
  - That clinicians have received wrong BCRAT risks because of defects 1–3. No deployment trace was examined.
  - That BOADICEA's 2019 validation results transfer to the eight-gene model run by `bws` at the pinned revision.
  - That Mirai is calibrated at external sites: the cited abstracts report discrimination only.
  - That the English invitation software was free of defects. The Review found the trial algorithm's selection-date interaction and about 5,000 genuinely missed invitations.
- **Unsupported (by subject):**
  - BCRA does not support ages < 20, `T1 ≥ 90` or `T2 > 90`.
  - `bws` does not compute risks for targets over 79.
  - Mirai does not support missing views, non-standard views, marked-up images or "For Processing" images.

## Evidence

**Pinned source (all fetched 2026-11-21 by commit SHA):**
- `cran/BCRA@05bfdea1a18c78f411afa9c8c0fbcdf0ccae7499`: `DESCRIPTION`; `R/absolute.risk.R:5–102` (rate, mortality and 1−AR tables; unused `White_nlambda1/2` at 12–13, 58–59), `:118–121` (error filtering), `:153–165` (`Avg_White`), `:166–187` (integration); `R/relative.risk.R:4–10` (β tables), `:40–41` (linear predictors); `R/recode.check.R:11–15, 24–35, 37–63, 66–73, 76–80, 89–93, 95–120`.
- `epiverse/bcra-js@4a38d20753fc28e1e0416818cef698b28415da18`: `scripts/generate-test-data.R` (R oracle generator); `packages/bcra/test/fixtures/r-reference/*.json` (342 R-recorded rows; `summary.json`); `packages/bcra/test/README.md` (optional-test list); `packages/bcra/test/cross-validation/` (three files); `packages/bcra/src/core/recode-check.js:134, 168–232, 273, 295, 346, 358, 364`; `packages/bcra/src/core/risk-calculator.js:86–212`.
- `CCGE-BOADICEA/bws@70aa1e618d8b0095d23be2804678ce7161aee34b`: `bws/calc/calcs.py:31–156, 158–224, 280–312, 315–385`; `bws/calc/model.py:13–115`; `bws/calc/risks.py:12–168`; `bws/settings.py:49–214`; `bws/rest_api.py:62–160`; `bws/pedigree.py:317–340`.
- `yala/Mirai@3904a9eaca046378a194b1eb8c62fa32f45ce83b`: `README.md`; `configs/validate_mirai.json`; `onconet/datasets/csv_mammo_cancer.py:114–160`; `scripts/main.py:110–140`; `onconet/utils/parsing.py:318`; `onconet/utils/c_index.py:1–80`.

**Literature** (each DOI verified against Crossref metadata on 2026-11-21 for title, authors, venue, year, volume and pages; abstracts read via Europe PMC on the same date):
- Gail MH, Brinton LA, Byar DP, et al. JNCI 81(24):1879–1886, 1989. doi:10.1093/jnci/81.24.1879.
- Costantino JP, Gail MH, Pee D, et al. JNCI 91(18):1541–1548, 1999. doi:10.1093/jnci/91.18.1541.
- Gail MH, Costantino JP, Pee D, et al. JNCI 99(23):1782–1792, 2007. doi:10.1093/jnci/djm223.
- Banegas MP, John EM, Slattery ML, et al. JNCI 109(2):djw215, 2017 (online 2016). doi:10.1093/jnci/djw215.
- Matsuno RK, Costantino JP, Ziegler RG, et al. JNCI 103(12):951–961, 2011. doi:10.1093/jnci/djr154 (metadata only).
- Tyrer J, Duffy SW, Cuzick J. Stat Med 23(7):1111–1130, 2004. doi:10.1002/sim.1668.
- Lee A, Mavaddat N, Wilcox AN, et al. Genet Med 21(8):1708–1718, 2019. doi:10.1038/s41436-018-0406-9.
- Carver T, Hartley S, Lee A, et al. Cancer Epidemiol Biomarkers Prev 30(3):469–473, 2021. doi:10.1158/1055-9965.EPI-20-1319.
- Pal Choudhury P, Maas P, Wilcox A, et al. PLOS ONE 15(2):e0228198, 2020. doi:10.1371/journal.pone.0228198.
- Terry MB, Liao Y, Whittemore AS, et al. Lancet Oncol 20(4):504–517, 2019. doi:10.1016/S1470-2045(18)30902-1.
- Yala A, Mikhael PG, Strand F, et al. Sci Transl Med 13(578), 2021. doi:10.1126/scitranslmed.aba4373.
- Yala A, Mikhael PG, Strand F, et al. J Clin Oncol 40(16):1732–1740, 2022. doi:10.1200/JCO.21.01337.

**Government report:** *The Independent Breast Screening Review 2018*, HC 1799, ordered printed 13 December 2018, ISBN 978-1-5286-0913-5, from the GOV.UK publication page (PDF URL in `REPORT.json`). Text read 2026-11-21. Cited: Executive summary items 1–6; paras 1.12, 1.25, 2.2, 2.5–2.9, 2.10–2.18, 2.20–2.35, 3.16–3.19, 4.5–4.21; Annex C.

**Execution (2026-11-21):**
- *Host:* Linux x86_64 VM, 96 vCPU Intel Xeon @ 2.60 GHz. Rootless containers with `--network=none`.
- *R:* `r-base:4.4.1`, digest above. The pinned BCRA source was installed with `R CMD INSTALL -l <lib> <checkout>`.
- *Node:* `node:22.11.0-slim`, digest above, running `packages/bcra/src/index.js` directly.
- *Support material:* `support/bcra_diff/` holds `gen_profiles.py`, `run_bcra.R`, `run_bcrajs.mjs`, `compare.py` and `README.md`. Raw logs are in `results/r_log.txt`, `results/js_log.txt` and `results/compare.txt`.
- *Large intermediates:* not retained. Their SHA-256 digests for the run reported here are:
  - `profiles.csv`: `d0b9a1a1fc5e6546f38c3af87c491e29fbc6cd7ee3b69b29125b84e9f62c30bb`;
  - `out_r.csv`: `c7e86fa8f3d9db23ed2afcfcc823271e8f495f329c16c7fb17ce4eabdbdec7c1`;
  - `out_js.csv`: `ea4644eac92f8019a77378e49c53723f13044ba36db6c1ad5dd39291841b27de`.

  The profile generator is deterministic (seed 20261121) given the pinned bcra-js fixtures. The R output CSV embeds only computed values, but the logs contain timing lines that vary between runs.
- *Toy probe:* `support/invitation_conformance_toy.py` with output `support/invitation_conformance_toy.out.txt`, run under Python 3.13 with the standard library only.

## Revalidation

- **BCRA input handling (cheapest check):** in any R ≥ 4 with BCRA installed, run:

  ```r
  d <- data.frame(ID=1:3, T1=40, T2=50, N_Biop=c(-1,1,1), HypPlas=99,
                  AgeMen=12, Age1st=25, N_Rels=1, Race=c(1,1,1))
  recode.check(d)$NB_Cat                                   # "2" "1" "1": defect 1 present
  recode.check(transform(d[2, ], Race = 12))$Error_Ind     # "0": defect 2 present (one-row frame)
  recode.check(transform(d, Race = c(1, 12, 1)))$Error_Ind # "0" "1" "0": same row flagged in a mixed frame
  ```

  These three lines and their outputs were executed against the pinned package on 2026-11-21. Then diff `R/recode.check.R` lines 34 and 89–93 against a newer CRAN release.
- **R vs JavaScript:** rerun the four scripts in `support/bcra_diff/` against a new pinned revision of either repository. The comparator prints the disagreement classes, and any `R accepts, JS rejects` row identifies a validation divergence. In the port, check whether `test/cross-validation/validation-errors.test.js` now exists and imports `validation-errors.json`.
- **bws defaults:** diff `bws/settings.py` (`GENES`, `MUTATION_FREQUENCIES`, `CANCER_RATES`, `GENETIC_TEST_SENSITIVITY`, `MAX_AGE_FOR_RISK_CALCS`), `bws/calc/model.py:102–115` and `bws/rest_api.py:109–130`. The model version must be read from the executable's `-v` output on a live deployment; the repository revision does not determine it.
- **Mirai:** diff `scripts/main.py` calibration export and `csv_mammo_cancer.py` `get_label`. Calibration monotonicity requires loading the calibrator pickle and evaluating each horizon on a grid of raw scores.
- **Validation numbers:** re-read the abstracts behind the DOIs above. Newer external validations would need a new literature search.
- **Screening specification:** obtain the current breast-screening Service Specification and apply the predicate format in `support/invitation_conformance_toy.py` to its stopping-age text. The toy model's counts do not transfer. Only the predicate structure is reusable.
