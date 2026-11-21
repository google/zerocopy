# Kidney-function estimating equations, creatinine assay standardization, renal dosing formulas, and how two open R packages encode them

## Summary

- **One model covers every serum-creatinine eGFR equation examined.** Each is a power law in rescaled creatinine `r = Scr/Q`, sometimes with a knee at `r = 1`. Each also carries an age term and a sex factor: `eGFR = A · min(r,1)^α · max(r,1)^β · g(age) · s`. The equations differ only in coefficients, in the rescaler `Q(age, sex)`, and in the age term. Cockcroft–Gault is a different quantity: absolute creatinine clearance in mL/min, not normalized to 1.73 m², and it needs body weight. A system that confuses the two quantities produces a unit error, not a rounding difference. (Basis: normative + source + derived)
- **The 2021 CKD-EPI race-free creatinine refit** is `142 · min(Scr/κ,1)^α · max(Scr/κ,1)^−1.200 · 0.9938^age · 1.012[female]`, with κ = 0.7 (F) / 0.9 (M) mg/dL and α = −0.241 (F) / −0.302 (M). These values were verified against the published coefficient table. The NKF-ASN Task Force recommended it for immediate implementation in all US laboratories, together with wider use of cystatin C. (Basis: normative)
- **Assay standardization is a calibration change, not a new equation.** One laboratory derived its relation as standardized Scr = 0.95 × original MDRD-study Scr. That is why the re-expressed MDRD intercept is 175 rather than 186: 186 × 0.95^1.154 = 175.3. A calibration shift factor `f` multiplies Cockcroft–Gault by `1/f`, MDRD by `f^−1.154`, and CKD-EPI above the knee by `f^−1.2`. Below the knee the change is much smaller. The 2010 NCI CTEP follow-up letter said that no correction factor should be applied and that the GFR used in the Calvert formula should not exceed 125 mL/min. That cap implies a maximum dose of AUC × 150 mL/min. (Basis: normative + documentation + derived)
- **Two open implementations agree on arithmetic but disagree on defaults and edges.** `kidney.epi` 1.4.0 and `nephro` 1.5 were executed on R 4.4.2 against the same synthetic inputs:
  - **Identical:** the 2021 refit, apart from `kidney.epi`'s rounding to 2 dp.
  - **2009 equation:** they differ by up to 0.32% because they implement the two published forms (table versus single equation).
  - **EKFC:** up to 0.63%, because adult Q is written in µmol/L in one package and in mg/dL in the other.
  - **MDRD default:** 6.3%, because the defaults are non-IDMS 186 versus IDMS 175. In addition, `nephro` treats `'idms'` (lowercase) as non-IDMS.
  - **Edge inputs:** an invalid sex code or EKFC age ≤ 2 gives `NA` in `kidney.epi` but `0` in `nephro`. Scr = 0 gives `Inf` in both.
  - **Units:** `kidney.epi` defaults to µmol/L, so 1.0 entered in mg/dL without a unit argument yields 302.83 instead of 73.04. `nephro` is mg/dL-only and silently accepts µmol/L values. (Basis: execution + source)
- **The Calvert formula needs absolute GFR in mL/min.** Passing a BSA-indexed eGFR mis-scales the dose term by BSA/1.73. For eGFR 90 and three synthetic body sizes, de-indexing changes the formula output from 575 to between 481 and 767 (−16% to +33%). (Basis: normative + derived)

## Applicability

- **Equations and dosing formulas.** The report covers serum-creatinine equations for adults (Cockcroft–Gault, MDRD 4-variable, CKD-EPI 2009 and 2021). It also covers the creatinine EKFC equation (ages 2–90 in its publication), the published form of the EKFC cystatin C rescaler, and the Calvert carboplatin formula, together with the CTEP safeguards that apply to it.
- **Not covered.** Cystatin-C CKD-EPI equations appear only as coefficients. Paediatric-only equations (Schwartz, CKiD) were not examined.
- **R packages.** Both packages were examined at the pinned mirror commits in `REPORT.json`:
  - `cran/kidney.epi` @ `04297148e9dc8077a99a5b39f4c11471d15aee54` (version 1.4.0, published 2025-05-31);
  - `cran/nephro` @ `5d906c2d898597e0bfb2d9731cbcd01f6a8d958a` (version 1.5, published 2025-02-11).
  - Both repositories are read-only mirrors of CRAN package archives, so the revision identifies the released package source.
  - The packages were not installed. Their own `R/*.R` files were `source()`d into R 4.4.2 inside container image `docker.io/library/r-base:4.4.2` (image ID `242d80afc130…`, manifest digest `sha256:cdeeabb2…`), with networking disabled.
  - `kidney.epi` declares imports (`readxl`, `openxlsx`, `purrr`) that the executed functions never call. Running under an installed package namespace could still differ, for example in warning formatting; that case was not examined.
- **Subject relationships.**
  - The publications define the formulas; the R packages are implementations compared with each other and with a Python transcription of the published formulas.
  - The CTEP letter and McLean et al. concern how GFR estimates feed the Calvert formula.
  - Matzke et al. and Delgado et al. are guidance documents, used only for what their abstracts state.
- **Host.** All numbers come from synthetic inputs on a 96-vCPU Intel Xeon 2.60 GHz virtual machine, single-threaded.
- **Not clinical guidance.** This report describes formulas, implementations and evidence. It is not clinical or dosing guidance.

## Findings

### 1. Equation catalogue

| Equation | Published form (Scr in mg/dL unless stated) | Output | Derivation / validation evidence (as published) |
| --- | --- | --- | --- |
| Cockcroft–Gault 1976 | `(140 − age) · weight_kg / (72 · Scr)`, × 0.85 if female | creatinine clearance, mL/min (absolute) | Age–creatinine-excretion relation from 249 patients aged 18–92. Compared with the mean of two 24-h clearances in 236 patients: r = 0.83. |
| MDRD 4-variable (1999; re-expressed 2006/2007) | `175 · Scr^−1.154 · age^−0.203 · 0.742[F] · 1.212[Black]` for IDMS-traceable Scr. The 1999-calibration intercept is 186; the µmol/L intercept is 30849. | mL/min/1.73 m² | 1628 MDRD-study patients with CKD (1070 training, 558 validation). The re-expressed equation had 90% of estimates within 30% of measured GFR (¹²⁵I-iothalamate), Cockcroft–Gault 60%. Few patients had GFR > 90. |
| CKD-EPI 2009 | `141 · min(Scr/κ,1)^α · max(Scr/κ,1)^−1.209 · 0.993^age · 1.018[F] · 1.159[Black]`, with κ 0.7/0.9 and α −0.329/−0.411. The table form folds the sex and race factors into rounded intercepts 144/141/166/163. | mL/min/1.73 m² | Development: 8254 participants, 10 studies (iothalamate). Validation: 3896 participants, 16 studies. Median bias 2.5 vs 5.5 (MDRD); P30 84.1% vs 80.6%. |
| CKD-EPI 2021 creatinine (race-free refit of 2009) | `142 · min(Scr/κ,1)^α · max(Scr/κ,1)^−1.200 · 0.9938^age · 1.012[F]`, with κ 0.7/0.9 and α −0.241/−0.302. The 95% CI for 142 is 139–144. | mL/min/1.73 m² | Same 10 development studies (8254 participants, 31.5% Black). Validation: 12 studies, 4050 participants, 14.3% Black. Underestimated measured GFR by a median 3.6 in Black participants and overestimated it by 3.9 in non-Black participants (mL/min/1.73 m²). At least 85% within 30% in both groups. |
| CKD-EPI 2021 creatinine–cystatin C | `135 · min(Scr/κ,1)^α · max(Scr/κ,1)^−0.544 · min(Scys/0.8,1)^−0.323 · max(Scys/0.8,1)^−0.778 · 0.9961^age · 0.963[F]`, with α −0.219 (F) / −0.144 (M) | mL/min/1.73 m² | 13 studies, 5352 participants. "More accurate than new creatinine equations, with smaller differences between race groups." |
| EKFC creatinine 2021 | `107.3 · (Scr/Q)^(−0.322 if Scr/Q < 1 else −1.132) · (0.990^(age−40) if age > 40)`. Adult Q = 62 µmol/L (F) / 80 µmol/L (M). For age ≤ 25, `ln Q` is a cubic in age plus a `ln(age)` term (coefficients in §6). | mL/min/1.73 m² | Development and internal validation: 11,251 participants, 7 studies. External validation: 8378 participants, 6 studies. Ages 2–90, Scr 40–490 µmol/L. Bias −1.2 (children) and −0.9 (adults). No Black patients. |
| EKFC cystatin C 2023 | Same form with `Scys/Q`. Q = 0.83 mg/L below age 50, `0.83 + 0.005·(age − 50)` from 50. | mL/min/1.73 m² | Rescaler from 227,643 Swedish patients. Validated in 11,231 European, 1093 US and 508 African patients. |
| Calvert 1989 | `dose_mg = target_AUC · (GFR + 25)`. An earlier fit was `AUC · (1.2·GFR + 20)`. | mg | Retrospective PK in 18 patients (GFR 33–136 mL/min). Prospective study in 31 patients and 40 courses, AUC 3–8: observed/predicted AUC 1.24 ± 0.11, r = 0.886, then refit to `GFR + 25`. |

Basis: normative. Sources:
- **Coefficients:** for CKD-EPI 2009 and 2021, the published tables (PMC full text). For MDRD, the Levey 2007 abstract.
- **Cohort figures:** the abstracts.
- **EKFC:** the coefficients are stated in both implementations, which agree exactly (source). The primary full text was not examined (see Boundaries).

### 2. The common model and what is genuinely different

| Equation | Q | α (r < 1) | β (r ≥ 1) | g(age) | s | Units native |
| --- | --- | --- | --- | --- | --- | --- |
| MDRD | 1 mg/dL | −1.154 | −1.154 (no knee) | age^−0.203 | 0.742 F | mg/dL (30849 for µmol/L) |
| CKD-EPI 2009 | 0.7 / 0.9 mg/dL | −0.329 / −0.411 | −1.209 | 0.993^age | 1.018 F | mg/dL |
| CKD-EPI 2021 | 0.7 / 0.9 mg/dL | −0.241 / −0.302 | −1.200 | 0.9938^age | 1.012 F | mg/dL |
| EKFC | Q(age, sex), µmol/L | −0.322 | −1.132 | 1, or 0.990^(age−40) after 40 | none (sex is in Q) | µmol/L |

Derived consequences:
- **Calibration sensitivity is set by the exponent.** Below the knee, a creatinine calibration error of factor `f` scales eGFR by `f^α`, which is small (|α| ≈ 0.24–0.41). Above the knee it scales by `f^β`, which is large (|β| ≈ 1.1–1.2).
- **EKFC moves sex into the rescaler.** EKFC has no separate sex factor and uses one exponent pair for everyone. It puts all sex and age dependence into Q. This removes a free parameter but adds a different discontinuity (§6).

### 3. Assay standardization and recalibration

- **Calibration bias.** Myers et al. (NKDEP Laboratory Working Group, 2006) reported that between-laboratory creatinine variability makes all GFR equations less accurate below 1.5 mg/dL (133 µmol/L), which is the range relevant to detecting CKD. Standardizing calibration does not correct analytical non-specificity, for example Jaffe interferences. (Basis: documentation, abstract)
- **The MDRD re-expression.** Levey 2007 cross-calibrated against reference materials traceable to IDMS. Combining factors, they found standardized Scr = 0.95 × original MDRD Scr, and re-expressed the equation as `175 · Scr^−1.154 …` (µmol/L intercept 30849). The probe checks this arithmetic: `186 × 0.95^1.154 = 175.31` and `175 × 88.4^1.154 = 30849`. (Basis: normative + derived; `support/egfr_reference.out`)
- **Propagation of a calibration factor `f` (Scr_new = f · Scr_old).** With `f = 0.95`, the single-laboratory factor above and not a general conversion:

| Quantity | Ratio new/old |
| --- | --- |
| Cockcroft–Gault | `1/f` = 1.0526 |
| MDRD | `f^−1.154` = 1.0610 |
| CKD-EPI 2021, Scr above κ | `f^−1.200` = 1.0635 |
| CKD-EPI 2021, Scr below κ | 1.0124 (F), 1.0156 (M) |

  Calvert dose uses `GFR + 25`, so its relative change is smaller than the GFR change. For five synthetic Cockcroft–Gault profiles the change was +3.0% to +4.6% when uncapped. In the one profile where the 125 mL/min cap binds (male, 30 y, 90 kg, Scr 0.8 → CG 172 → 181), the capped output is fixed at AUC × 150 regardless of `f`. (Basis: derived; `support/egfr_reference.out`)
- **The CTEP follow-up letter (2010-10-22).** It follows an Action Letter of 2010-10-01, which was not examined directly. It states:
  - by 2010-12-31 all US clinical chemistry laboratories would use IDMS-traceable creatinine;
  - older methods varied too much for a single conversion factor;
  - IDMS "in general generates a lower creatinine value … in patients with normal renal function".

  It asks protocols to:
  1. not use any correction factor;
  2. impose a maximum carboplatin dose based on target AUC, or require measured GFR when Scr is below the lower limit of normal;
  3. cap the GFR used in Calvert at 125 mL/min, so that the maximum equals `target AUC × 150 mL/min` (the letter's table gives 900, 750 and 600 mg for AUC 6, 5 and 4);
  4. in patients with abnormally low creatinine, either use a minimum creatinine of 0.6 mg/dL or apply the 125 cap;
  5. measure GFR when concerned.

  (Basis: documentation) The letter therefore names two different safeguards: a pre-equation floor on the input and a post-equation cap on the output. They interact. For a female, 35 y, 55 kg, Scr 0.45 profile, CG is 151.5; the floor gives 113.6, the cap 125.0, and both together 113.6. Software must record which safeguard it applies and in what order. (Basis: derived)
- **Field evidence that the cap does not remove the error.** McLean et al. 2020 compared Cockcroft–Gault GFR from IDMS creatinine with ⁵¹Cr-EDTA GFR in 550 patients. The median ratio was 1.04 (range 0.43–3.38), and the ratio exceeded 1.2 in 33%. Even with the CG-GFR cap of 125 mL/min, AUC-6 dosing would have under-dosed 18% and over-dosed 23% of patients by more than 100 mg relative to ⁵¹Cr-GFR. The authors recommend capping when ⁵¹Cr-GFR is unavailable. (Basis: documentation, abstract)

### 4. The race-free refit and the task-force process

- **Task-force process and recommendations.** Delgado et al. (AJKD 2022; simultaneously JASN 2021) worked for 10 months. They narrowed 26 candidate approaches to 5 and judged them on six attributes: assay availability and standardization, implementation, diversity in development, performance against measured GFR, consequences, and patient-centredness. They recommended:
  1. immediate implementation of the CKD-EPI creatinine refit without race in all US laboratories;
  2. national efforts to increase routine, timely cystatin C use, especially to confirm eGFR;
  3. research on new filtration markers.

  (Basis: documentation, abstract)
- **Validation numbers that motivated the refit (Inker et al. 2021).**
  - The 2009 equation with the race term overestimated measured GFR by a median of 3.7 mL/min/1.73 m² in Black participants and 0.5 in non-Black participants.
  - Dropping the race term from the 2009 equation without refitting underestimated by 7.1 in Black participants.
  - The refit underestimated by 3.6 in Black participants and overestimated by 3.9 in non-Black participants.
  - Creatinine–cystatin C refits were more accurate and narrowed the between-group gap.

  (Basis: normative, abstract + table)
- **Implementation consequence.** "Remove the race coefficient" and "use the 2021 refit" are different operations. The intercept, exponents, age base and sex factor all changed: for example 141 → 142, −1.209 → −1.200, 0.993 → 0.9938, 1.018 → 1.012. A system that simply sets the race multiplier to 1 implements the 7.1-unit-bias variant, not the recommended equation. (Basis: normative + derived)

### 5. Dosing-guidance quantities

- **Cockcroft–Gault output.** It estimates absolute creatinine clearance (mL/min). It was derived with pre-standardization assays, so its relation to IDMS creatinine is not the one in the original paper. (Basis: normative + derived from §3)
- **Calvert input.** Calvert's formula takes GFR in mL/min, which is absolute. An eGFR reported per 1.73 m² must be de-indexed (× BSA/1.73) before use. Otherwise the output is mis-scaled. With eGFR 90 mL/min/1.73 m² and target AUC 5, using DuBois BSA:

| Synthetic body size | BSA | Output, indexed value used | Output, de-indexed |
| --- | --- | --- | --- |
| 150 cm, 45 kg | 1.37 m² | 575 | 481 |
| 170 cm, 70 kg | 1.81 m² | 575 | 596 |
| 190 cm, 120 kg | 2.47 m² | 575 | 767 |

  (Basis: normative + derived; `support/egfr_reference.out`)
- **KDIGO conference (Matzke et al. 2011).** It states that GFR is the metric used to guide dose adjustment, but that kidney disease also affects non-renal clearance, which most pharmacokinetic studies do not consider adequately. It produced 37 practice, 32 research and 24 regulatory recommendations. Which kidney-function measure it recommends in which situation was **not examined** beyond the abstract. (Basis: documentation, abstract)

### 6. How the two R packages encode the equations

**Input pipeline.**
- **`kidney.epi`:**
  1. Arguments are checked: equal lengths, obligatory parameters, a single unit string lower-cased and matched against `mg/dl`, `micromol/l` and `mmol/l`.
  2. Inputs are filtered: `service.check_and_correct_numeric` replaces values failing a rule with `NA` and warns.
  3. Units are converted by dividing by 88.4.
  4. The equation is computed with `pmin`/`pmax` and rounded to 2 dp.
- **`nephro`:** each function coerces inputs with `as.numeric` and records the indices of `NA` inputs. It then substitutes the placeholder `10` for missing values ("Replace missing data with fake data to avoid problems with formulas"), computes, and restores `NA` at the recorded indices. It takes Scr only in mg/dL and sex only as 0 (female) or 1 (male). (Basis: source)

**Quoted source at the pinned revisions.** `kidney.epi`:
- `R/egfr_ckdepi2021.R:33`: `creatinine_units = "micromol/l",` (the default unit). Lines 66–67: `lower_than = max_age,` / `greater_than = 18,` (the age rules). Lines 92 and 98: `a [sex %in% label_sex_female] <- -0.241` and `eGFR <- 142 *`.
- `R/service.general.R:14`: `service.check_and_correct_numeric <- function(x, x_name, rules = c(non_negative = TRUE)) {`. Line 27: `failed <- x < 0`. Line 35: `failed <- x <= threshold`, so `greater_than = 18` rejects exactly 18. Line 65: `failed <- x >= threshold`, so `lower_than = 100` rejects exactly 100. Line 91: `x[!valid] <- NA`.
- `R/service.check_plausibility.R:99`: `if(creatinine_units == "micromol/l") creatinine <- creatinine / 88.4`.
- `R/egfr_mdrd.R:39`: `creatinine_method = "non-IDMS",`. Lines 127–128: `eGFR * 175,` / `eGFR * 186`.
- `R/egfr_ekfc.R:107,110`: adult Q `62,` / `80,` (µmol/L). Line 76: `greater_than = 2,`. Lines 120 and 123: `0.74 * 88.4,` / `1.02 * 88.4,` (Q override when ethnicity is labelled African, applied at every age).
- `R/egfr_other_adults.R:129`: `#' @return numeric creatinine clearance expressed in ml/min/1.73m…`. The Cockcroft–Gault body at line 198 is `(140 - age) * weight / (72 * creatinine)`, which is absolute mL/min, so the documented unit is wrong.

`nephro` (`R/nephro.R`):
- Line 41: `eGFR * ifelse(method == 'IDMS', 175, 186)` (case-sensitive; default `method="IDMS"` at line 9).
- Lines 196–200: `k <- a <- numeric(n)`, then `k[sex == 0] <- 0.7` … `a[sex == 1] <- -0.302`. A sex code other than 0 or 1 leaves `k = a = 0`, so `Scr/0 = Inf` and the result is `0`.
- Lines 620–637 (EKFC): `Qcrea_mgDl` is zero-initialised and is assigned only for `age > 25` (0.7 or 0.9) and for `age > 2 & age <= 25` (polynomial / 88.4). For age ≤ 2, `creatinine/0 = Inf` and `Inf^−1.132 = 0`.
- Line 456: `eGFR <- (140-age) * wt / (72 * creatinine)` with no age bound.

(Basis: source)

**Executed behaviour on shared inputs.** Full grid and outputs are in `support/egfr_probe.out`. Grid comparison over 48 profiles (sex × age 20/40/60/80 × Scr 0.5–4.0 mg/dL):

| Equation | Max relative difference between packages | Cause |
| --- | --- | --- |
| CKD-EPI 2021 | 0.032% | `kidney.epi` rounding only |
| CKD-EPI 2009 | 0.36% | Table intercept 144 versus compact 141 × 1.018 = 143.538 (0.32%), plus rounding |
| EKFC | 0.65% | Adult Q 80/88.4 = 0.9050 versus 0.90 mg/dL, eGFR × 1.0063 above the knee for men (× 1.0022 for women), plus rounding |
| MDRD (defaults) | 6.30% | 186 versus 175 |
| Cockcroft–Gault | 0.034% | Rounding |

Against the Python transcription of the published formulas (`support/egfr_reference.py`), each package matched the form it implements to within 0.005 (`kidney.epi`) or exactly (`nephro`). (Basis: execution)

| Edge input (CKD-EPI 2021 unless stated) | `kidney.epi` | `nephro` |
| --- | --- | --- |
| Scr = 0 | `Inf` | `Inf` |
| Scr = −1 | `NA` (warning) | `NaN` |
| Scr = `NA` | `NA` | `NA` |
| age 18.0 / 18.5 / 10 | `NA` (warning "lower or equal than 18") / 109.12 / `NA` | 109.46 / 109.12 / 115.05 |
| age 100 / 150 | `NA` / `NA` | 65.73 / 48.16 |
| sex not in labels (`"X"`, code 2) | `NA` (silent) | `0.000` |
| 1.0 (meant as mg/dL), no unit argument | 302.83 (read as µmol/L) | 73.04 |
| 88.4 µmol/L | 73.04 (unit given) | 0.337 (read as mg/dL) |
| EKFC age 2.0 / 1.5 | `NA` / `NA` | `0` / `0` |
| EKFC sex not in labels | `NA` | `0` |
| Cockcroft–Gault, female, age 150, 70 kg, Scr 1.0 | `NA` | −8.26 |
| Cockcroft–Gault, weight 0 | 0 | 0 |
| MDRD default `method` / `'idms'` | 87.96 (186) / 82.76 | 82.76 (175) / 87.96 (186) |
| return type of EKFC | `numeric` | `matrix` (n × 1) |

(Basis: execution, R 4.4.2; rerun produced byte-identical output.)

**Formula properties (derived, from the transcription).**
- **EKFC discontinuity at age 25.** The polynomial Q at age 25 is 62.43 µmol/L (F) and 80.86 µmol/L (M), while the adult constants are 62 and 80. For Scr above Q, eGFR therefore steps by × 0.9922 (F) and × 0.9879 (M) between age 25 and just over 25. Both packages reproduce this because both encode the same coefficients.
- **CKD-EPI 2021 continuity and monotonicity.** CKD-EPI 2021 is continuous at κ. It is strictly decreasing in Scr on 0.30–5.29 mg/dL and in age on 18–100.

(Basis: derived; `support/egfr_reference.out`)

### 7. Defects and hazards at the pinned revisions

Each item quotes its source above.
1. **Default unit trap (`kidney.epi`).** The default `"micromol/l"` combines with plausibility checks that only reject negative creatinine. As a result, an mg/dL value entered without a unit argument gives eGFR about 4.1× too high (302.83 vs 73.04). No warning is issued, because neither the creatinine nor the eGFR has an upper plausibility bound.
2. **Unit-blind input (`nephro`).** The functions are mg/dL-only and do not check magnitude, so µmol/L input yields eGFR below 1.
3. **Zero creatinine.** In both packages Scr = 0 passes the plausibility check, because the non-negativity rule (`x < 0`) and `as.numeric` both accept 0, and the result is `Inf`.
4. **Invalid sex codes (`nephro`).** They yield `0`, a plausible-looking result for kidney failure, instead of `NA`.
5. **Age boundaries (`kidney.epi`).** The two age rules disagree at 18. `greater_than = 18` rejects age 18.0, while the `adult_equation = 18` message says that only ages under 18 need paediatric equations. The default `max_age = 100` rejects age 100 exactly, and the EKFC default upper age of 100 exceeds the published validation range of 2–90.
6. **Opposite MDRD defaults.** The two packages use opposite defaults, and `nephro` matches `'IDMS'` case-sensitively.
7. **Documentation defects (`kidney.epi`).** The Cockcroft–Gault return unit is documented as per 1.73 m². The EKFC references at `R/egfr_ekfc.R:9` and `:152` cite `doi: 10.1056/NEJMoa22037`. The Crossref-registered DOI of the cited title is `10.1056/NEJMoa2203769`; a lookup of the truncated string through the tools used returned no record, which was not independently confirmed as unregistered.

(Basis: source + execution)

### 8. Performance and resource footprint

| Level | Measurement | Value | Basis |
| --- | --- | --- | --- |
| L1 authoring | Source size | `kidney.epi` `R/` 4532 lines in 16 files (CKD-EPI 2021 file 256 lines); `nephro` one 888-line file, CKD-EPI 2021 function 40 lines (176–215). Person-month and LLM-token cost: **not measured**. | measured (`wc -l`) |
| L2 build | Package installation / build time | **not measured** (sourced, not installed). Container image size 875,368,437 bytes. | measured (image inspect) |
| L3 compile/elaborate | n/a for interpreted R. `source()` latency **not measured** separately. Whole R probe 1.47 s wall including container start. | 1.47 s | measured |
| L4 execution | Vectorised CKD-EPI 2021, n = 10⁶ synthetic inputs | `kidney.epi` 0.517 s (1.93 M/s); `nephro` 6.696 s (0.149 M/s, about 13× slower: row-wise `apply(cbind(...),1,min)`) | measured (`support/egfr_timing.out`) |
|  | n = 10⁵ | 0.086 s vs 0.475 s | measured |
|  | n = 10⁴ | 0.110 s vs 0.108 s (fixed overhead dominates) | measured |
| L5 verification | Reference-formula differential check | 0.03 s wall, 11 MB RSS (Python) | measured |
| L6 footprint | Package archive bytes | `kidney.epi` 408,906; `nephro` 12,746 (codeload tarballs at pinned revisions) | measured |
|  | R max memory at n = 10⁶ (`gc()` "max used") | `kidney.epi` 142 MB; `nephro` 314 MB | measured |
|  | Energy | **not measured** | — |

Host: 96-vCPU Intel Xeon @ 2.60 GHz VM, R 4.4.2 single-threaded in a container.

### 9. Comprehensibility and model refinement (C1, C2)

**C1, human comprehension.** A correct call depends on eight facts that are invisible at most call sites:
1. the equation version;
2. the unit;
3. the calibration (IDMS or not);
4. the sex encoding;
5. the race or ethnicity encoding (2009, MDRD, and EKFC for African Q);
6. whether the output is indexed (per 1.73 m²) or absolute;
7. the age domain;
8. any downstream cap or floor.

Footguns that a human reviewer would not see from the call alone:
- default units in `kidney.epi`;
- silent zeros in `nephro`;
- two "published" 2009 forms that differ by 0.32%;
- defaults that differ between packages;
- the Cockcroft–Gault unit label.

Diagnostics also differ in legibility. `kidney.epi` warnings name the failed rule ("1 value is lower or equal than 18"). `nephro` returns numbers for every invalid case, which a person can audit only by already knowing the coding contract. This is a statement about human audit, not agent execution. (Basis: derived)

**C2, simplicity and refinement.**
- **One evaluator with typed inputs.** All creatinine eGFR equations are instances of one evaluator, `A · min(r,1)^α · max(r,1)^β · g(age) · s` with `r = Scr/Q`, parameterised by a coefficient record.
- **Fewer function bodies.** With this model, the 2009 table and compact forms, the 2021 refit and MDRD become rows of data rather than separate functions. Both packages instead duplicate the validation and conversion code per equation (`kidney.epi`) or the NA-substitution idiom per function (`nephro`).
- **Unit and calibration as types.** Making unit and calibration part of the creatinine value's type (a quantity tagged mg/dL or µmol/L, IDMS or non-IDMS) removes the default-unit and 175/186 hazards. Callers must already know these facts, so this is a deep-module improvement rather than a shift of complexity to callers.
- **Absolute versus indexed outputs as types.** Cockcroft–Gault and de-indexed eGFR (mL/min) belong to a different output type from indexed eGFR (mL/min/1.73 m²). Calvert should accept only the former.
- **The model's limit.** EKFC's age-25 step shows that the common model does not remove domain discontinuities. It only makes them visible as properties of Q.

(Basis: derived)

### 10. Validation coverage (V1–V4)

- **V1, specification adequacy.**
  - The differential test compared two implementations with a transcription of the published formulas. It kills transcription errors in coefficients, as both packages matched their chosen forms.
  - It cannot detect a coefficient copied wrongly into both the reference and an implementation from a shared secondary source. The EKFC coefficients are exposed to that risk, because the primary text was not examined.
  - Property checks (continuity at κ, monotonicity) passed for CKD-EPI 2021, and the EKFC age-25 discontinuity was found this way.
  - Mutation testing and property-based fuzzing of the packages were **not performed**.
- **V2, lowering and checker soundness.** There is no compiler pipeline here. The cross-implementation differential is the analogue. Floating-point differences between R and Python were below 1e-6 in the unrounded comparisons.
- **V3, concurrency, crash and physical.** **Known not to apply**: these are pure functions without state.
- **V4, field and plant validation.**
  - Equation accuracy is validated against measured GFR (iothalamate, ⁵¹Cr-EDTA and other exogenous markers) in the cited cohorts.
  - Dosing-formula adequacy has field evidence: McLean 2020, with 18% and 23% of patients mis-dosed by more than 100 mg despite the cap.
  - Human-operator comprehension of unit and indexing choices has **not been examined** in any study found.

## Boundaries

- **Not examined.**
  - **Full texts:**
    - Pottel 2021 (EKFC coefficients rest on agreement between the two packages and secondary calculators);
    - Pottel 2023 creatinine Q values for Black African and European subjects (the 0.74 and 1.02 mg/dL in `kidney.epi`);
    - Matzke 2011 recommendations beyond the abstract;
    - the CTEP Action Letter of 2010-10-01 (only the 2010-10-22 follow-up was read);
    - KDIGO 2024 CKD guideline;
    - FDA/EMA renal-impairment PK guidance;
    - carboplatin product labels;
    - Eneanya–Yang–Reese 2019 (metadata only).
  - **Equations:** paediatric equations (Schwartz, CKiD), BIS and FAS implementations in `kidney.epi`, cystatin-only CKD-EPI 2012, and the `nephro` Stevens/Virga functions.
  - **Execution modes:** running the packages as installed namespaces, and other R versions.
  - **Other implementations:** laboratory-information-system eGFR reporting, EHR calculators and commercial dosing software.
- **Unknown.**
  - Whether any downstream user of `kidney.epi` relies on the µmol/L default with mg/dL data; no usage data were examined.
  - Whether the Q values written in mg/dL (`nephro`) or in µmol/L (`kidney.epi`) are the authors' intended canonical values; the 0.63% difference cannot be resolved without the primary text.
- **Known not to apply.**
  - The 0.95 calibration factor is specific to the MDRD study laboratory. The CTEP letter explicitly states that no single factor works across laboratories, so the §3 propagation ratios illustrate the mathematics of sensitivity only.
  - Calvert's derivation population (adults, GFR 33–136 mL/min) does not cover paediatric or high-AUC transplant settings, which the CTEP letter also sets apart.
- **Unsupported.** `nephro` does not support µmol/L input or non-0/1 sex codes. `kidney.epi`'s adult equations do not support ages ≤ 18 or ≥ `max_age`. Its EKFC does not support age ≤ 2.
- **Stronger conclusions not established.**
  - No package was shown to be "wrong" for its documented contract. The hazards arise at the contract boundaries: defaults, codes and units.
  - Agreement within 0.005 does not validate clinical accuracy.
  - The −16% to +33% indexing effect assumes eGFR 90 and DuBois BSA; other BSA formulas were not compared.
- **Performance cells marked "not measured"** in §8 are unmeasured, not small.

## Evidence

**Observation date.** All evidence was gathered on 2026-11-21 (UTC).

**Repositories.** HEAD SHAs were resolved through the GitHub API and the sources were downloaded as codeload tarballs at those SHAs:
- `cran/kidney.epi` @ `04297148e9dc8077a99a5b39f4c11471d15aee54`. Tarball SHA-256 `da96279f77abb58d225b309a846707beeecddc26899898ad2632af4e83f103ff`. Files: `R/egfr_ckdepi2021.R`, `R/egfr_ckdepi2009.R`, `R/egfr_ekfc.R`, `R/egfr_mdrd.R`, `R/egfr_other_adults.R`, `R/service.general.R`, `R/service.check_plausibility.R`. Lines are as quoted in §6–§7.
- `cran/nephro` @ `5d906c2d898597e0bfb2d9731cbcd01f6a8d958a`. Tarball SHA-256 `ac8e5723151da52c21fbe8b3f174aab251048e458241f5438e65bab9a6071885`. Files: `R/nephro.R` and `man/MDRD4.Rd`, `man/CKDEpi2021.creat.Rd` (unit and coding contract: "creatinine values in mg/dl", "0 for females and 1 for males").

**Literature.** Every DOI was resolved through the Crossref REST API (title, authors, venue, volume, pages). Content statements come from:
- Europe PMC or PubMed abstracts: PMIDs 1244564, 2681557, 10075613, 16332993, 19414839, 34554658, 36720134, 16908915, 17332152, 21918498, 33166224, 34563581, 32220419.
- PMC full-text tables: Levey 2009 (PMC2763564), for the table and single-equation forms and the statement that table intercepts fold in the sex and race factors; Inker 2021 (PMC8822996), for the 2021 coefficients and confidence intervals.
- Metadata only: Eneanya, Yang and Reese, JAMA 322(2):113, 2019 (`10.1001/jama.2019.5774`).
- Crossref notes: it records Cockcroft–Gault with a 2008 online date (print 1976). It also records the `kidney.epi` CRAN DOI `10.32614/CRAN.package.kidney.epi`.

**CTEP letter.** Read as text from the URL in `REPORT.json`, a three-page memo dated 2010-10-22 and signed by CTEP branch chiefs.

**Execution.** Commands, outputs and scripts are in `support/`.
- `egfr_probe.R` gives the grid, edge cases and warnings; output `egfr_probe.out`. Run with `KIDNEY_EPI_DIR=<tree> NEPHRO_DIR=<tree> Rscript egfr_probe.R` inside `docker.io/library/r-base:4.4.2` with `--network=none`.
- `egfr_timing.R` gives throughput and memory; output `egfr_timing.out`.
- `egfr_reference.py egfr_probe.out` gives the published-form identities, propagation, cap and floor, indexing, properties and the grid comparison; output `egfr_reference.out`. It needs Python 3.10+ and the standard library only.
- Toy versus real: the R outputs are executions of the real package code. The Python file is a transcription of the published formulas, not an implementation under test.

## Revalidation

1. **For a new package release,** rerun `support/egfr_probe.R` against the new source tree and diff the output against `support/egfr_probe.out`. Any change in the edge-case table or in grid differences beyond 0.005 is material.
2. **Cheapest targeted diffs.** In `kidney.epi`, inspect the default of `creatinine_units`, the rules passed to `service.check_and_correct_numeric`, and whether a creatinine upper or zero bound has been added. In `nephro`, inspect `k <- a <- numeric(n)` and the `ifelse(method == 'IDMS', …)` line, plus the `Qcrea_mgDl` initialisation in `EKFC.creat`.
3. **For a new equation or guideline version,** check the coefficient table in the primary publication against `support/egfr_reference.py` first, then rerun the grid comparison. For EKFC, obtain the Pottel 2021 full text to settle the canonical Q unit and the polynomial coefficients.
4. **For carboplatin safeguards,** re-read the current CTEP guidance. The cap value of 125 mL/min and the floor of 0.6 mg/dL are the specific points to check.
5. **Scope of a passing rerun.** It shows only that the implementations still behave as recorded. It does not establish clinical accuracy.
