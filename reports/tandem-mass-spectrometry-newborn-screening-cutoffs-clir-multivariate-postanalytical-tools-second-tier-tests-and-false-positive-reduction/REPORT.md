# Newborn screening by tandem mass spectrometry: single-analyte cutoffs, CLIR/R4S multivariate post-analytical tools with covariate adjustment, second-tier tests, a Random Forest classifier, and screening principles — reported performance, public code, and a toy model of the trade-offs

## Summary

This report describes methods, implementations and published evidence. It gives no diagnostic or clinical-management advice.

- **Multi-analyte screening and its early outcomes.** Tandem mass spectrometry (MS/MS) of dried blood spots replaced "one-analysis, one-metabolite, one-disease" assays with "one-analysis, many-metabolites, many-diseases", chiefly amino acids and acylcarnitines (Chace–Kalas–Naylor 2003). In the first population study (Wilcken et al. 2003; 362,000 newborns in New South Wales and the Australian Capital Territory, April 1998–March 2002), the prevalence of the targeted inborn errors, excluding phenylketonuria, was 15.7 per 100,000 (95 % CI 11.9–20.4), against 8.6–9.5 per 100,000 in clinically diagnosed historical cohorts. Of the 57 cases diagnosed after screening began, 15 were diagnosed clinically and **7 of those 15 had a normal screening result**. The authors state it was "not yet clear" which screen-detected patients would have become symptomatic. Basis: documentation (published abstracts).
- **How the post-analytical tools differ from cutoffs.** The Region 4 Stork (R4S) tools, later Collaborative Laboratory Integrated Reports (CLIR), replace fixed cutoffs with:
  - condition-specific scores driven by the overlap between a cumulative reference range and a disease range;
  - all informative ratios of markers;
  - covariate-adjusted moving percentiles (age at collection and birth weight).

  Scores are expressed as the **percentile rank among known true-positive cases** of that condition.
- **Reported effects of the tools.** All of the following are retrospective estimates except the Minnesota figures, which are prospective programme outcomes:
  - Minnesota sustained a false-positive rate (FPR) below 0.1 % and a positive predictive value (PPV) above 60 % (Marquardt et al. 2012).
  - Applied retrospectively to California's January–June 2012 data, the tools plus second-tier tests could have lowered an actual FPR of 0.26 % with PPV 10 % to "as low as 0.02 %" with PPV above 50 % (Hall et al. 2014).
  - Minnesota in 2013, using the tools as primary interpretation, reported PPV 69 % and FPR 0.024 %.

  Basis: documentation.
- **Second-tier tests.** Mayo Clinic ran MS/MS-based second-tier tests on the same specimen for congenital adrenal hyperplasia, tyrosinaemia type I, methylmalonic acidaemias, homocystinuria and maple syrup urine disease. The programme reported an FPR of 0.09 %, PPV 41 % and detection of 1 affected case per 1672 screened (Matern et al. 2007). Basis: documentation.
- **A machine-learning second-tier filter.** A Random Forest trained on 39 analytes plus 6 clinical variables, using 2777 California screen positives (235 confirmed, 2542 false), reduced false positives by 89 % for GA-1, 45 % for MMA, 98 % for OTCD and 2 % for VLCADD "without changing the sensitivity" (Peng et al. 2020). The sensitivity-preserving threshold was set on the same held-out scores that were evaluated. The paper's printed PPVs are reproduced only if the true-positive counts are 43, 99, 18 and 60, not the 48, 103, 24 and 60 printed in the same table. Basis: documentation + derived.
- **Public code examined ([source]).**
  - An Arizona programme's R cutoff template (`AZ-NBS-Data/AZ-NBS-Cutoff-Analysis@46d2d03aa612eb8cff85b97cf2f49d28d25e58e8`) bins C0 and C0/(C16+C18) into four calls. As published, its in-silico section reads an object `df_clean` that the script never defines.
  - A UK notebook (`nf260/preanalyticalfactorsinNBS@49092996002c9bfa674b2370c29fea11c1c97f73`) classifies results with `'< cutoff' if x < cutoff else '>= cutoff'`, so a missing value (NaN) is labelled `>= cutoff`.
- **Toy model ([execution, toy model; not any programme]).**
  - At a matched 0.5 % FPR, adjusting for an invented birth-weight effect raised median sensitivity from 0.91 to 0.97, and cut the low-birth-weight share of false positives from 80 % to 8 %.
  - A classifier whose "keep every true positive" threshold was fixed in-sample missed at least one true positive in a fresh cohort in 12 of 20 seeds.

## Applicability

**Subjects.**
1. *Two public code repositories* written by screening laboratories or their staff:
   - an R/SQL template for single-analyte and ratio cutoff analysis against a NATUS Neometrics LIMS export, for Arizona;
   - Jupyter notebooks supporting Flynn, Hogg and Moat (2026) on how dried-blood-spot diameter and transit time shift results relative to UK cutoffs.

   Only the classification notebook and the R/SQL files were read. Neither repository contains data, and neither was executed (R is not installed on the host; the notebook's data are not published).
2. *Peer-reviewed papers* identified by DOI: Chace 2003; Wilcken 2003; Matern 2007; Marquardt 2012; Hall 2014; Minter Baerg 2018; Peng 2020; Hall–Wittenauer–Hagar 2020; Andermann 2008; Flynn 2026. They describe the methods and report programme outcomes.
3. *Wilson and Jungner's 1968 principles*, read as reproduced verbatim in Andermann 2008, Box 1.

**What was examined and what was not.** The CLIR/R4S software is a hosted web service and is **not** open source; nothing of it was executed or read. Its mechanics are taken from the published descriptions. Peng et al.'s Random Forest tool is published as a hosted web application (`https://rusptools.shinyapps.io/RandomForest/`), not as a repository; it was not used.

**Scope of the evidence.**
- *Retrospective versus prospective.* Retrospective estimates (California 2012; carrier-status analyses) and prospective programme outcomes (Minnesota; Kentucky lysosomal screening) are distinguished throughout.
- *Conditions.* Results are specific to the conditions and markers named. Lysosomal enzyme results (Minter Baerg 2018) are MS/MS-based but are enzyme activities, not amino acids or acylcarnitines.
- *Toy model.* It concerns an invented analyte, invented covariate effects and an invented prevalence. Its numbers describe mechanisms only.

**Host and environment for execution.** x86-64 cloud VM (Intel Xeon @ 2.60 GHz), Python 3.13.15, numpy 2.3.5; run on 2026-11-21.

## Findings

### 1. The multi-analyte measurement and the cutoff baseline

Basis: documentation (Chace 2003 abstract; Wilcken 2003 abstract via PubMed; Peng 2020 introduction).

- MS/MS measures amino acids and acylcarnitines in dried filter-paper blood; one analysis yields dozens of analytes (39 in the California panel per Peng et al.). Disorders of amino-acid, organic-acid and fatty-acid oxidation are detected from these profiles.
- **Cutoff interpretation** compares one or a few primary markers and ratios with fixed thresholds. Peng et al. give an example: MMA screen positives are identified by cutoffs on propionylcarnitine (C3) and its ratio to acetylcarnitine (C2), "two of the 39 analytes measured".
- The R4S project collected cutoffs across laboratories. Hall 2014 counts 8,382 active cutoff values at 151 sites and treats a cutoff as "validated" when it lies within the R4S target range *and* within the 25th–75th percentile of all posted cutoffs. Marquardt 2012 reports the median cutoff among laboratories for C8 as 0.35 µmol/L (N = 119) and for C14:1 as 0.60 µmol/L (N = 113). The ranges in heterozygous carriers overlap these cutoffs (carrier-group medians: C8 0.44, C14:1 0.84 µmol/L). This overlap is a stated source of false positives.
- **Outcome ascertainment matters.** Wilcken et al. ascertained cases clinically as well as by screening, and so could count 7 screen-negative cases among 57. Hall 2014 instead assumed "there were no additional false-negative events" during its evaluation period, relying on California's 15 metabolic referral centres. Sensitivity statements in the tool literature rest on that kind of assumption.

### 2. CLIR/R4S post-analytical tools: what is specified and what is not

Basis: documentation (Marquardt 2012; Hall 2014; Minter Baerg 2018; Hall–Wittenauer–Hagar 2020).

| Element | Published description | Specified enough to reimplement? |
|---|---|---|
| Reference data | Cumulative population results from participating labs (154 programmes in 49 countries in 2012) | no: the data are not public |
| Disease ranges | 767,464 results from 12,721 cases with 60 conditions (2012) | no: the data are not public |
| Marker selection | A marker is clinically significant when the median of its disease range lies above the 99th (or below the 1st) percentile of the normal population | yes (rule stated) |
| Score | "determined by the overlap between normal and disease ranges, penetration within the disease range, differences between conditions, and weighted correction factors" | **no**: weights and functional form not published in the abstract or the text examined |
| Display | each analyte as a multiple of the normal median on a log scale, overlaid with normal and disease ranges | yes |
| Output | score expressed as the percentile rank among all true-positive cases with the same condition; compared to "interpretation guidelines" | partially (guideline thresholds are tool-specific) |
| Informative threshold (Hall 2014) | score ≥ the value at the 1st percentile rank of known true positives (17,099 cases) | yes |
| Differential diagnosis | dual-scatter plots of two condition scores, with quadrant thresholds (e.g., MCAD versus carrier: x < 27 %, y > 96 %) | yes for the examples shown |
| Covariates | "continuous, covariate-adjusted, moving percentiles" (age at collection and birth weight) by a regression-based normalisation; more complex models with sex and location stated as work in progress (2018) | partially (method referenced, coefficients not given) |
| Ratios | "all informative permutations of ratios"; ratios between biochemically unrelated markers help correct "preanalytical factors and potential analytical bias" | rule stated, set not enumerated |
| Throughput | the tool runner had been applied 22,238 times by 30 programmes: 78 million scores, "on average 100,000 calculated scores per day" (Hall 2014) | cited |

**Reported performance (with baselines).**

| Study | Design | Baseline | With tools | Notes |
|---|---|---|---|---|
| Marquardt 2012 | retrospective | carrier false positives for fatty-acid oxidation disorders (279) | "at least half" avoidable; 88 % of known false-negative events "could have" been prevented | MN: FPR < 0.1 %, PPV > 60 % sustained |
| Hall 2014, CA | retrospective, 176,186 first specimens (exclusions by birth weight and age at collection) | FPR 0.26 %, PPV 10 % (cutoffs) | estimated FPR as low as 0.02 %, PPV > 50 %; "up to 90 %" fewer FPs | of 454 FPs, 66 % preventable by tools and rules; another 14 % by a second-tier test (utilisation 1 in 128) |
| Hall 2014, MN 2013 | prospective, 71,207 newborns | — | 38 of 55 referred confirmed: PPV 69 %, FPR 0.024 % | — |
| Minter Baerg 2018, KY | prospective, 55,161 specimens, lysosomal enzymes | — | 5 presumptive positives, 4 affected: FPR 0.0018 %, PPV 80 % | "preliminary evidence of no greater risk of false-negative events, still to be verified by long-term surveillance" |
| Hall–Wittenauer–Hagar 2020, GA | retrospective triage of follow-up | — | tools "appropriately assigned all true positive cases to the higher levels" for PKU, MCADD and VLCADD | abstract-level only |

**Derived consistency checks** (`support/ppv_checks.py`):
- California 2012: 0.26 % × 176,186 = 458 false positives, consistent with the 454 reported; PPV 10 % then implies about 51 true positives.
- Minnesota 2013: 38/55 = 69.1 % and 17/71,207 = 0.0239 %, matching the printed figures.
- Overlap persists after adjustment: Minter Baerg 2018 reports that the residual-activity ranges of true- and false-positive lysosomal cases "overlap almost completely, even after covariate adjustment". That is why their workflow adds second-tier tests.

### 3. Second-tier testing

Basis: documentation (Matern 2007 abstract, publisher-deposited; Hall 2014).

- A second-tier test re-analyses the *same* dried blood spot with a more specific method, run only on first-tier positives.
- Mayo applied such tests from 2004 for congenital adrenal hyperplasia, tyrosinaemia type I, methylmalonic acidaemias, homocystinuria and MSUD. It reported FPR 0.09 %, PPV 41 % and 1 affected per 1672 screened.
- Derived check: per 100,000 screened, 100,000/1672 = 59.8 detected and 0.09 % × 100,000 = 90 false positives, so PPV ≈ 59.8/149.8 = 39.9 %. The small gap from the printed 41 % probably reflects rounding of the published rates (unknown).
- Hall 2014 lists specific second-tier and rule-based resolutions:
  - homocysteine measurement for low methionine "would have resolved more than 800 cases";
  - a borderline free carnitine "could be disregarded when the sum of propionylcarnitine and palmitoylcarnitine is > 2 µmol/l" (an interpretation rule from cumulative R4S experience);
  - derivatised confirmation for malonylcarnitine flags that arise from isobaric interference.
- **What second-tier testing cannot do.** It filters first-tier positives only. A case below the first-tier cutoff never reaches it. Missed cases are found only through clinical presentation and referral, as Wilcken et al. observed (7 screen-negative of 57).

### 4. A Random Forest second-tier classifier (Peng et al. 2020)

Basis: documentation (paper text) + derived.

- **Data and labels.** 2777 California screen positives for GA-1, MMA, OTCD and VLCADD. Labels are confirmed true positives (235) versus false positives (2542).
- **Features.** 39 MS/MS analytes plus gestational age, birth weight, sex, race/ethnicity, age at collection and TPN status (one-hot encoded). Ratios were deliberately excluded from the model.
- **Model.** 1000 trees. The score is the fraction of trees voting true positive.
- **Validation.** Leave-one-out cross-validation, plus 10-fold cross-validation repeated 1000 times with stratified folds. Only held-out scores were used for the ROC curves and the AUC.
- **Threshold.** False-positive reductions are reported at "the sensitivity level of detecting this disorder in the California NBS program". The threshold is chosen on the same held-out scores, and **no temporally independent test cohort is reported** in the text examined.
- **Comparison.** For GA-1, Random Forest and CLIR were "similar", but disagreed on individual infants: 40 infants were true positive by CLIR and false positive by Random Forest.

| Disorder | Confirmed | FP first tier | FP after RF | FP reduction | PPV printed (first → RF) | PPV from the table's own counts | TP that reproduces printed PPVs |
|---|---|---|---|---|---|---|---|
| GA-1 | 48 | 1344 | 150 | 88.8 % | 3.1 % → 22.3 % | 3.4 % → 24.2 % | 43 |
| MMA | 103 | 502 | 276 | 45.0 % | 16.4 % → 26.4 % | 17.0 % → 27.2 % | 99 |
| OTCD | 24 | 496 | 11 | 97.8 % | 3.5 % → 62.1 % | 4.6 % → 68.6 % | 18 |
| VLCADD | 60 | 200 | 196 | 2.0 % | 23.1 % → 23.4 % | 23.1 % → 23.4 % | 60 |

The reductions match the abstract. The PPV columns are internally consistent with a smaller true-positive count for three disorders. The text examined does not explain the difference; one possibility is that some confirmed cases were excluded from PPV, but that is **unknown**.

### 5. Public code: what screening laboratories actually run for cutoff work

Basis: source.

**`AZ-NBS-Data/AZ-NBS-Cutoff-Analysis` @ `46d2d03aa612eb8cff85b97cf2f49d28d25e58e8`.** `R/README.md` describes it as "an R script template used in the Arizona Newborn Screening Program for cutoff analysis".
- **Data pull** (`SQL/AZ_sql_cutoff_analysis.sql`):
  - Collection and birth times are validated by string tests, and an invalid time is set to `NULL` (lines 17–33).
  - Age at collection is computed in hours as date difference plus time difference (line 51).
  - Birth weight, gestational age, NICU status and feeding are carried as columns (lines 54–57).
  - With a `NULL` time, `AGECOLL_HRS` is `NULL`.
- **Pre-processing** (`R/AZ-R-Cutoff-Analysis.r`):
  - Unsatisfactory specimen codes are removed (lines 40–48).
  - Line 51 stratifies by age with `df$age_group <- ifelse(df$AGECOLL_HRS < 120, "<120 hrs", "≥120 hrs")`. Specimens with `NULL` age therefore form a separate `NA` group in every `group_by(age_group)` summary (derived from R's `ifelse` semantics).
  - The percentile tables go down to the 0.01st percentile (lines 56–149).
- **In-silico cutoff rule** (lines 156–190; thresholds at lines 156–158: `C0_hight <- 70`, `C0_ratiot <- 85`, `high_ratiot <- 150`):
  - normal: `C0_C16C18 < 85`;
  - borderline: `C0 < 70 & 85 ≤ C0_C16C18 ≤ 150`;
  - abnormal: `C0 ≥ 70 & 85 ≤ C0_C16C18 ≤ 150`;
  - high: `C0_C16C18 > 150`.

  For non-missing values the four bins are disjoint and exhaustive. Rows with a missing value fail every `filter()` condition and appear in no bin, so the four counts do not sum to the cohort size (derived from documented dplyr `filter` behaviour). The analyte pair is that used for carnitine palmitoyltransferase I deficiency (free carnitine high relative to C16+C18). The thresholds are template placeholders, not a statement of Arizona's operational cutoffs.
- **Undefined object.** Lines 160, 168, 176 and 184 each read `df_clean %>%`, but the only assignments in the file are `df <- read.csv("INSERT_FILENAME.csv")` (line 30) and `df <- df %>%` (line 44). Run top to bottom as published, the in-silico section stops with an "object not found" error unless the user creates `df_clean`. Not executed (no R on host); Basis: source.
- `library(pROC)` is loaded (line 22) but no ROC function is called.

**`nf260/preanalyticalfactorsinNBS` @ `49092996002c9bfa674b2370c29fea11c1c97f73`.** Notebook `Pre-analytical factors in NBS - Modelling impact on result classification - single CoV.ipynb`; line numbers below are raw JSON lines of the `.ipynb`.
- **Encoded cutoffs.** "UK newborn screening cut-off values" (µmol/L) are encoded at lines ≈1290–1310: C10 0.5, C8 0.5, Phe 240, Tyr 240, C5 2.0, C5DC 0.70, Met 50, Xleu 600 (`'Phe': 240` at line 1302). Elsewhere TSH is 8 mU/L and IRT 56 ng/mL. These are the values *as encoded in the notebook*; they were not checked against a UK programme document.
- **Classifier** (lines 1196–1201): `lambda x: (f'< {cutoff} {unit}' if x < cutoff else f'>= {cutoff} {unit}')`. Because `NaN < c` is false, a missing value is labelled `>= cutoff`. Executing that comparison with a numpy float64 NaN gives `False` (`support/ppv_checks_out.txt`). Upstream, `handle_lt_gt` turns non-numeric strings into NaN with `pd.to_numeric(..., errors="coerce")` (line 236), and replaces censored strings such as "<x" or ">x" with the boundary value x (lines 225, 233). Whether any NaN reaches the classifier in the authors' data is **unknown**, since the data are not public. In the agreement analysis a NaN would be labelled identically before and after correction, so it would not create a spurious "changed classification".
- **Transit-time correction** (lines 939–946): `cf = 1 / (1 - adj*(reference_trans - days))`, with per-analyte daily coefficients, for example `'Met': -0.0379`, `'Xleu': 0.0047`. This is a linear-drift model of analyte change in transit, applied multiplicatively.
- *Relevance.* Pre-analytical covariates (spot size, transit time) move values across fixed cutoffs. Adjusting for them is the same idea as CLIR's covariate adjustment, applied before classification instead of inside a score.

### 6. Toy model: cutoffs, covariate adjustment, two-marker score, and an in-sample "keep every TP" threshold

Basis: execution (toy model written for this report; `support/nbs_cutoff_toy.py`; 20 seeds; full output `support/nbs_toy_out.json`).

**Invented population:**
- 10⁶ unaffected newborns per cohort, with prevalence 5 × 10⁻⁵.
- 8 % low birth weight, which raises log X by 0.30 per kg below 3.3 kg; early collection also raises X.
- Disease shifts log X by N(1.6, 0.5) and lowers a partner analyte Y.
- Rules compared: (A) cutoff on raw log X at the unaffected 99.5th percentile; (B) the same cutoff on covariate-regression residuals; (C) a score of residual X minus residual Y (a log ratio), with its threshold set to match A's sensitivity; (D) a logistic second-tier model on A-positives.

| Rule | Sensitivity, median [min–max] | False positives per 10⁶ | Low-BW share of FPs |
|---|---|---|---|
| A raw cutoff (FPR 0.5 %) | 0.91 [0.83–1.00] | 5000 | 79.7 % |
| B covariate-adjusted cutoff (FPR 0.5 %) | 0.97 [0.85–1.00] | 5000 | 8.1 % (≈ population share 8 %) |
| C two-marker score at A's sensitivity | 0.91 | median 62.5 [0–9661] | median 7.9 % |

| D: second-tier logistic model on A-positives | median [min–max] |
|---|---|
| FP reduction with threshold = lowest cross-validated TP score | 99.8 % [71.0–100] |
| sensitivity among screen positives, same data | 1.00 by construction |
| next-cohort sensitivity with threshold fixed on training data | 0.978 [0.82–1.00] |
| next-cohort missed true positives | median 1 [0–9]; at least 1 missed in 12/20 seeds |

**Mechanisms the toy exposes:**
1. *Unadjusted cutoffs concentrate false positives in covariate strata.* This is the motivation for covariate-adjusted percentiles. Hall 2014's exclusions by birth weight and age at collection are the alternative of removing those strata from the analysis.
2. *Equal-FPR comparisons are fair; matched-sensitivity thresholds on few cases are unstable.* With about 45 affected per cohort, matching sensitivity is a quantile of very few points, hence C's FP range of 0 to 9661.
3. *"Without changing sensitivity" is a property of the data the threshold was chosen on.* In a new cohort the same threshold lost one or more true positives in most seeds. This is the general risk in Section 4's design; it is not a demonstration that Peng et al.'s model loses cases.

### 7. Screening principles that govern thresholds and adding conditions

Basis: documentation (Wilson–Jungner 1968 as reproduced in Andermann 2008, Box 1; Andermann's synthesis, Box 2).

| Wilson–Jungner principle | Decision it bears on in this report |
|---|---|
| 1 important health problem; 2 accepted treatment; 3 facilities for diagnosis and treatment | adding a condition (e.g., OTCD is "not currently on the RUSP", per Peng et al.); second-tier and confirmatory capacity |
| 4 recognisable latent or early symptomatic stage; 7 natural history adequately understood | Wilcken's caveat on which screen-detected patients would have become symptomatic; carrier and pseudo-deficiency results in Marquardt and Minter Baerg |
| 5 suitable test; 6 acceptable to the population | analytical specificity, false-positive burden on families (cited as motivation by Peng, Hall and Minter Baerg) |
| 8 agreed policy on whom to treat as patients | case definitions used as training labels (Section 4) and the "informative score" thresholds (Section 2) |
| 9 cost of case-finding economically balanced | second-tier utilisation (1 in 128 in Hall 2014); referral volume |
| 10 case-finding a continuing process | cumulative reference and disease databases; periodic cutoff review (Hall 2014 validation criterion) |

Andermann's synthesis adds, among other criteria: "There should be quality assurance, with mechanisms to minimize potential risks of screening", "Programme evaluation should be planned from the outset" and "The overall benefits of screening should outweigh the harm". These bear on the false-negative ascertainment gap noted in Sections 1 and 3.

### 8. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | effort to build or maintain CLIR tools; cutoff templates | not measured | — |
| L2 toolchain build | — | not applicable (no build) | — |
| L3 scoring latency | CLIR tool-runner volume | 78 million scores over 22,238 runs; on average 100,000 scores/day | cited (Hall 2014) |
| L3 scoring latency | Random Forest tool per case | "within minutes, given the RF model has been established" | cited (Peng 2020) |
| L4 throughput | toy model, 20 seeds × 2 cohorts of ≈10⁶ | 18.22 s wall | measured (`/usr/bin/time -v`) |
| L5 verification | independent recomputation of published metrics | 4 of 4 published rate sets checked arithmetically; Peng PPV inconsistency found | derived (`support/ppv_checks.py`) |
| L6 memory | toy model peak RSS | 193,052 KiB | measured |
| L6 data | CLIR reference/disease database size | 767,464 results / 12,721 cases (2012); 17,099 true-positive cases referenced in 2014 | cited |

### 9. Comprehensibility and model simplicity (C1–C2)

- **C1.** A cutoff is the easiest rule to audit: one number, one comparison. It is also covariate-blind and silent about overlap with carriers. CLIR outputs (percentile rank among true positives, overlays in multiples of the median, dual-scatter quadrants) are legible to a laboratory director, but the score function is not published enough to reproduce independently (Section 2). A Random Forest score (fraction of 1000 trees) is the least locally explainable; Peng et al. supply mean-decrease-in-accuracy rankings rather than per-case reasons. In the public code, the hidden footguns are mundane: an undefined object, NaN falling to the positive side, missing rows silently dropped from bin counts. Basis: derived.
- **C2.** All three interpretive layers estimate one quantity: how much more likely a profile is under a condition than under the unaffected population, conditional on covariates. A cutoff is the degenerate case: one marker, a step function and no covariates. CLIR adds overlap-weighted markers, ratios and covariate conditioning. A classifier learns the boundary from labelled screen positives. Second-tier tests add an independent measurement to the same decision. Treating these as one evidence-accumulation step with one explicit, prospectively validated operating point would make "sensitivity preserved" a testable claim, not a property of the tuning data. This is a design inference, not a tested system.

### 10. Validation of implementations and proposals (V1–V4)

- **V1 specification adequacy.** The labels (confirmed case versus false positive) come from follow-up. False negatives are ascertained only by clinical referral (Wilcken: 7 of 57 diagnosed cases were screen-negative), or are assumed absent (Hall 2014). Any FPR or PPV improvement is therefore conditional on unobserved missed cases. Prospective surveillance is the stated remedy (Minter Baerg 2018).
- **V2 differential checks.** The Random Forest and CLIR were compared case by case for GA-1, and disagreed on individual infants. This report's arithmetic recomputation of published metrics found one table-level inconsistency (Section 4).
- **V3.** Not applicable.
- **V4 field validation.** The strongest evidence is prospective deployment: Minnesota 2013 and Kentucky 2016–2017. Retrospective "could have" estimates (California 2012) are weaker. No randomised or temporally held-out evaluation of the Random Forest was found in the text examined.

## Boundaries

- **Not examined: CLIR software, its score function and its reference data.** These are hosted and not open. All CLIR claims are documentation-level. The functional form and weights of the score are **unknown** from the sources examined.
- **Not examined: Peng et al.'s web tool and training data.** The data come from the California Biobank (access-controlled).
- **Not examined: full texts of Wilcken 2003 (abstract via PubMed only), Matern 2007 (publisher-deposited abstract only), Hall–Wittenauer–Hagar 2020 (abstract only) and Flynn 2026 (Crossref metadata; the notebook was read, the paper was not).** Chace 2003 was read at abstract level. Wilson and Jungner's monograph was read only as reproduced by Andermann 2008.
- **Not examined: repository execution.** The R template was not run (no R on host). The notebook was not run (data not public). The `df_clean` finding is from source reading. The NaN behaviour was checked only by executing the comparison itself.
- **Unknown:** why Peng et al.'s printed PPVs imply 43, 99 and 18 true positives for GA-1, MMA and OTCD; whether NaN values reach the UK notebook's classifier; the exact current cutoff values of any programme named (template and notebook values are illustrative or as encoded).
- **Known not to apply:** toy-model numbers to any real analyte, disorder, programme, CLIR tool or published classifier.
- **Not established:**
  - that CLIR, second-tier tests or Random Forests reduce false positives *without* increasing false negatives (claims are retrospective or rely on referral ascertainment);
  - that covariate adjustment removes overlap (Minter Baerg reports near-complete overlap after adjustment for lysosomal enzymes);
  - that the performance figures transfer between programmes, analyte panels or populations.

## Evidence

All web and repository material was observed on **2026-11-21 (UTC)**. DOIs were verified against Crossref metadata on that date (title, authors, venue, volume and pages).

- D. H. Chace, T. A. Kalas, E. W. Naylor, "Use of Tandem Mass Spectrometry for Multianalyte Screening of Dried Blood Specimens from Newborns", *Clin. Chem.* 49(11):1797–1817, 2003. doi:10.1373/clinchem.2003.022178 (abstract via Crossref and Europe PMC, PMID 14578311).
- B. Wilcken, V. Wiley, J. Hammond, K. Carpenter, "Screening Newborns for Inborn Errors of Metabolism by Tandem Mass Spectrometry", *N. Engl. J. Med.* 348(23):2304–2312, 2003. doi:10.1056/NEJMoa025225 (abstract via PubMed, PMID 12788994).
- D. Matern, S. Tortorelli, D. Oglesbee, D. Gavrilov, P. Rinaldo, *J. Inherit. Metab. Dis.* 30(4):585–592, 2007. doi:10.1007/s10545-007-0691-y (abstract in Crossref record).
- G. Marquardt, R. Currier, D. M. S. McHugh, et al., "Enhanced interpretation of newborn screening results without analyte cutoff values", *Genet. Med.* 14(7):648–655, 2012. doi:10.1038/gim.2012.2 (article page at nature.com/articles/gim20122).
- P. L. Hall, G. Marquardt, D. M. S. McHugh, R. J. Currier, H. Tang, S. D. Stoway, P. Rinaldo, "Postanalytical tools improve performance of newborn screening by tandem mass spectrometry", *Genet. Med.* 16(12):889–895, 2014. doi:10.1038/gim.2014.62 (article page at nature.com/articles/gim201462).
- M. M. Minter Baerg, S. D. Stoway, J. Hart, et al., "Precision newborn screening for lysosomal disorders", *Genet. Med.* 20(8):847–854, 2018. doi:10.1038/gim.2017.194 (article page: Methods, "Covariate adjustment", Discussion).
- G. Peng, Y. Tang, T. M. Cowan, G. M. Enns, H. Zhao, C. Scharfe, "Reducing False-Positive Results in Newborn Screening Using Machine Learning", *Int. J. Neonatal Screen.* 6(1):16, 2020. doi:10.3390/ijns6010016 (full text at mdpi.com; Table with FP/PPV columns; Methods on LOOCV and 10-fold × 1000).
- P. L. Hall, A. Wittenauer, A. Hagar, *Int. J. Neonatal Screen.* 6(1):20, 2020. doi:10.3390/ijns6010020 (abstract).
- A. Andermann, "Revisting [sic] Wilson and Jungner in the genomic age", *Bull. World Health Organ.* 86(4):317–319, 2008. doi:10.2471/BLT.07.050112 (PMC full text; Box 1 reproduces J. M. G. Wilson and G. Jungner, *Principles and Practice of Screening for Disease*, WHO Public Health Papers 34, 1968; no DOI).
- N. Flynn, S. Hogg, S. J. Moat, *Clin. Chem. Lab. Med.*, online 2026-10-20. doi:10.1515/cclm-2026-0976 (metadata only).
- Repositories:
  - `AZ-NBS-Data/AZ-NBS-Cutoff-Analysis` @ `46d2d03aa612eb8cff85b97cf2f49d28d25e58e8`: `R/AZ-R-Cutoff-Analysis.r` (lines 22, 30, 40–51, 56–149, 156–190), `SQL/AZ_sql_cutoff_analysis.sql` (lines 14–57), `R/README.md`, `SQL/README.md`.
  - `nf260/preanalyticalfactorsinNBS` @ `49092996002c9bfa674b2370c29fea11c1c97f73`: classification notebook (raw JSON lines 225–236, 939–946, 1196–1201, ≈1290–1310), `README.md`, `CITATION.cff`.
- Execution (support material):
  - `support/nbs_cutoff_toy.py`. Command `python3 nbs_cutoff_toy.py --seeds 20 > nbs_toy_out.json`; 18.22 s wall, 193,052 KiB maximum RSS.
  - `support/ppv_checks.py` with output `support/ppv_checks_out.txt`.

## Revalidation

1. **Repositories.** At the pinned revisions, or any newer one:
   - `grep -n "df_clean" R/AZ-R-Cutoff-Analysis.r` together with `grep -n "df_clean *<-" R/AZ-R-Cutoff-Analysis.r` (an empty second result means the object is still undefined);
   - in the UK notebook, search for `if x < cutoff else` (the NaN behaviour) and `IMD_CUTOFFS` (the encoded cutoffs).
2. **Published numbers.** Rerun `python3 support/ppv_checks.py` (well under 1 s). It recomputes every derived check here from the printed inputs. If a correction to Peng et al. appears, compare it with the "TP implied by printed PPVs" line.
3. **Toy mechanisms.** Rerun `python3 support/nbs_cutoff_toy.py --seeds 5` (about 5 s). Rules A and B should show the low-birth-weight FP concentration and its removal; rule D should show at least one seed with missed next-cohort true positives. These outputs test only the toy.
4. **CLIR behaviour.** No cheap check exists, because the software is closed. Re-read the newest CLIR method publications for a published score function or covariate model before relying on Section 2's "not specified" entries.

