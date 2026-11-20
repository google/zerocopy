# Operational sepsis labels, deployed sepsis-alert validation, and early-warning scores: Sepsis-3 cohort SQL, an external validation of a proprietary sepsis model, the prospective TREWS outcome analysis, NEWS2, TRIPOD and calibration

## Summary

- **The label is part of the model.** Every reported discrimination number for a sepsis alert is conditional on (a) an operational sepsis definition, (b) a choice of *onset time*, and (c) which predictions are eligible relative to onset and to clinical recognition. For one widely deployed proprietary model the same hospitalizations produced AUROC 0.63 when scores after sepsis onset were excluded, 0.80 when scores up to 3 h after onset were included, and 0.72–0.76 when each 15‑minute prediction was scored against a fixed horizon (Wong et al. 2021). A later analysis of the same vendor model reported AUROC 0.62 before sepsis criteria were met but 0.47 once predictions made after clinical recognition (antibiotics, fluids, blood culture or lactate orders) were also excluded (Kamran et al. 2024). Basis: documentation.
- **Threshold metrics in the external validation are internally consistent.** Recomputing from the published counts (38,455 hospitalizations, 2,552 with sepsis, 6,971 ever alerting at score ≥ 6, 1,709 septic hospitalizations never alerting) reproduces sensitivity 0.330, specificity 0.829, PPV 0.121, NPV 0.946, alert fraction 0.181 and number-needed-to-evaluate 8.3. Basis: derived (support/derived_metrics.py).
- **The prospective TREWS study is an observational within-alert comparison, not a deployment trial.** Its primary contrast is between alerted septic patients whose alert a provider *confirmed within 3 h* and those whose alert was not confirmed within 3 h (adjusted absolute in-hospital mortality reduction 3.3%, CI 1.7–5.1; relative 18.7%, CI 9.4–27.0; Adams et al. 2022). The public notebook shows the estimator: near-unpenalized logistic regression (`C=1000`), standardization over the cohort with the exposure set to 0 and 1, and 5,001 bootstrap replicates; missing binary covariates are set to 0, missing continuous covariates to the column mean, missing GCS to 15. Basis: source + documentation.
- **The open Sepsis-3 SQL makes several choices the consensus text leaves open**, and the MIMIC-III and MIMIC-IV versions disagree on two of them: the MIMIC-IV query excludes an antibiotic and a culture charted at the *same* timestamp (both window predicates are strict at the shared end), and sets the suspected-infection time to the *antibiotic* time when the antibiotic came first, whereas the MIMIC-III query includes ties and always uses a *culture* time. The MIMIC-IV Sepsis-3 table assumes a baseline SOFA of 0 for every ICU stay, imputes missing SOFA components as 0, requires an antibiotic prescription started inside the ICU stay, and uses prescription *orders* rather than administrations. Basis: source + execution (transcribed predicates).
- **NEWS2 is a fixed integer chart with explicit gaps and a non-monotone oxygen-saturation scale**; discrimination evidence for the original NEWS is AUROC 0.722 (cardiac arrest), 0.857 (unanticipated ICU admission), 0.894 (death) and 0.873 (any outcome) within 24 h of an observation set (Smith et al. 2013). Basis: normative + documentation.
- **Reporting and monitoring guidance (TRIPOD 2015 → TRIPOD+AI 2024; Van Calster et al. 2019; Finlayson et al. 2021)** asks for calibration curves, recalibration/updating, and active dataset-shift surveillance; the external validation reported only calibration *plots* (judged poor), and the outcome study reported no calibration of the alert score at all. Basis: documentation + derived.

## Applicability

**What the findings cover.** (1) The behaviour of the Sepsis-3, suspicion-of-infection, SOFA, SIRS and antibiotic concept queries in `MIT-LCP/mimic-code` at revision `303d26c623dcc9c49cc0f204468d4acc2f063797` (BigQuery dialect files under `mimic-iv/concepts/` and `mimic-iii/concepts/`). The repository also ships PostgreSQL and DuckDB transliterations (`concepts_postgres/`, `concepts_duckdb/`); those were listed but not diffed line by line, so claims are about the BigQuery files. (2) The analysis code for the prospective TREWS outcome study in `royadams/adams_et_al_2022_code` at `96fffd7a14804feb506c8b62391d2c942c541146` (a single Jupyter notebook; cell indices below are 0‑based positions in the notebook's `cells` array). The input data and the TREWS model itself are proprietary and were not available. (3) The published results of the external validation of the Epic Sepsis Model (ESM) and related studies, read from the PubMed Central full text (Wong et al. 2021; Wong et al. 2021 JAMA Netw Open), the NSF public-access abstract (Kamran et al. 2024), and publisher abstracts (Adams et al. 2022; Henry et al. 2022). (4) NEWS2 Charts 1 and 2 as published by the Royal College of Physicians (2017), and the abstract of Smith et al. (2013) for the original NEWS.

**How subjects relate.** The two code repositories are *exemplars of label construction*: `mimic-code` constructs a retrospective Sepsis-3 label on a public ICU database; the TREWS notebook constructs an analysis cohort and outcome contrast on a proprietary EHR extract. The ESM validation papers are interpreted *through* the label-timing lens that the code makes concrete. TRIPOD, TRIPOD+AI, Van Calster et al. and Finlayson et al. are guidance applied to both deployed-model studies. NEWS2 is an aggregate track-and-trigger score included as the non-learned comparator class; it is not a sepsis-specific model.

**Scope limits.** No MIMIC data were queried (credentialed access was not used), so no cohort counts or query timings for the SQL are reported. The ESM is proprietary; its inputs, coefficients and version at each study site are not public. Nothing here establishes the current performance of any vendor model.

## Findings

### 1. Sepsis-3 as written versus as executable

The consensus definition (Singer et al. 2016, Box 3) states: sepsis is "life-threatening organ dysfunction caused by a dysregulated host response to infection"; organ dysfunction "can be identified as an acute change in total SOFA score ≥2 points consequent to the infection"; and "the baseline SOFA score can be assumed to be zero in patients not known to have preexisting organ dysfunction." The criteria study (Seymour et al. 2016, Methods) operationalized *suspected infection* in EHR data as the combination of antibiotics and body-fluid cultures: "If the antibiotic was given first, the culture sampling must have been obtained within 24 hours. If the culture sampling was first, the antibiotic must have been ordered within 72 hours. The 'onset' of infection was defined as the time at which the first of these 2 events occurred." Maximum SOFA was computed "for the time window from 48 hours before to 24 hours after the onset of infection." Basis: normative (Singer) + documentation (Seymour).

Choices these texts leave open, and what `mimic-code` (MIMIC-IV, BigQuery files) does:

| Open choice | `mimic-iv/concepts/...` behaviour at the pinned revision | Lines |
|---|---|---|
| Antibiotic event source | `prescriptions` orders (`starttime`), filtered by a drug-name `LIKE` list and route exclusions (eye/ear/topical); not `emar` administrations | `medication/antibiotic.sql` 1–181 |
| Location gate | antibiotic gets a `stay_id` only if `starttime ≥ intime AND starttime < outtime` of an ICU stay | `medication/antibiotic.sql` 197–201 |
| Culture source and positivity | `microbiologyevents` collapsed per `micro_specimen_id`; positive iff organism non-null, non-empty, not `CANCELLED`, and `org_itemid NOT IN (90856, 90760)` | `sepsis/suspicion_of_infection.sql` 23–44 |
| Culture→antibiotic window | `antibiotic_time > culture_time AND antibiotic_time <= culture_time + 72 h`; earliest such culture chosen | `suspicion_of_infection.sql` 67–99 |
| Antibiotic→culture window | `antibiotic_time >= culture_time − 24 h AND antibiotic_time < culture_time` | `suspicion_of_infection.sql` 133–150 |
| Date-only cultures | day-granularity variants: culture-first `antibiotic_date ∈ [chartdate, chartdate + 3 days]`; antibiotic-first `antibiotic_date ∈ [chartdate − 1 day, chartdate]` | 92–97, 146–148 |
| Suspected-infection time | `COALESCE(last72_charttime, antibiotic_time)` — culture time if culture-first, else antibiotic time | 169–173 |
| SOFA sampling | hourly rows; each component is the worst value in the hour, then `MAX(...) OVER (ROWS BETWEEN 23 PRECEDING AND 0 FOLLOWING)`; hour grid starts 24 h before the ICU in-time, which `icustay_hourly.sql` takes from the first charted heart rate rounded up to the hour (`GENERATE_ARRAY(-24, …)`, line 29; header lines 1–5) and output is filtered to `hr >= 0` *after* windowing | `score/sofa.sql` 26–38, 325–379 |
| Missing SOFA components | component `NULL` when data absent, then `COALESCE(…, 0)` — treated as normal; no last-observation carry-forward beyond the 24‑row window | `sofa.sql` 233–238, 328–368 |
| Urine output | 24‑h rate used only when 22–30 h of observation time are present | `sofa.sql` 141–144 |
| Baseline SOFA | assumed 0 for every stay; Sepsis-3 is `sofa_24hours >= 2` | `sepsis/sepsis3.sql` 7–8, 20, 41–46 |
| SOFA–infection alignment | `sofa.endtime` within `[SI − 48 h, SI + 24 h]`, both ends inclusive | `sepsis3.sql` 55–62 |
| Onset selection | per stay, `ROW_NUMBER() … ORDER BY suspected_infection_time, antibiotic_time, culture_time, endtime`, keep `rn_sus = 1` | `sepsis3.sql` 48–53, 80 |

Basis: source. Derived consequences:

- **The `sepsis3` output column is constant.** Rows enter `s1` only through an inner join requiring `sofa_24hours >= 2` (line 20) and a non-NULL `suspected_infection_time` (a NULL makes `DATETIME_SUB(NULL, …)` NULL and the join predicate unknown), so `sofa_score >= 2 AND suspected_infection = 1` (line 46) is true for every output row; the table lists only septic stays. Basis: derived from source.
- **"Onset" is the earliest suspicion that *has* an organ-dysfunction partner**, not the earliest suspicion. A stay with an early culture/antibiotic pair without SOFA ≥ 2 and a later pair with SOFA ≥ 2 is labelled at the later pair. The reported `sofa_time` can precede the suspicion time by up to 48 h. Basis: derived from source.
- **ICU-only by construction.** The header says "this query can only define sepsis-3 onset within the ICU" (lines 4–5); together with the antibiotic location gate, a patient treated on a ward or in the emergency department who receives no new antibiotic order during the ICU stay has no suspicion row. Basis: source.
- **Universal zero baseline differs from the consensus default.** Singer et al. permit a zero baseline only for patients "not known to have preexisting organ dysfunction"; the query applies it to everyone, so chronic organ dysfunction (e.g., chronic kidney disease) can satisfy SOFA ≥ 2 without an acute change. MIMIC-IV notes that pre-admission laboratory "baseline" values are often available in the `hosp` module (Johnson et al. 2023), so a baseline-aware variant is possible but is not what this file computes. Basis: normative + source + documentation.

**Window boundary semantics (executed transcription).** `support/soi_window_probe.py` evaluates the transcribed charttime predicates with SQLite on a single antibiotic at t = 0 and a culture at offsets −73 h … +24.5 h. Output (`support/soi_window_probe.out.txt`):

| culture − antibiotic (h) | MIMIC-IV suspected? | MIMIC-IV SI time | MIMIC-III suspected? | MIMIC-III SI time |
|---|---|---|---|---|
| −73 | no | — | no | — |
| −72 | yes | −72 (culture) | yes | −72 |
| −0.5 | yes | −0.5 (culture) | yes | −0.5 |
| **0** | **no** | — | **yes** | 0 |
| +0.5 | yes | **0 (antibiotic)** | yes | **+0.5 (culture)** |
| +24 | yes | 0 (antibiotic) | yes | +24 (culture) |
| +24.5 | no | — | no | — |

Basis: execution (toy transcription of the predicates evaluated in SQLite 3 via Python 3.13 on an x86-64 Linux VM; not an execution of the upstream SQL against MIMIC). The MIMIC-III file (`mimic-iii/concepts/treatment/suspicion_of_infection.sql`) uses inclusive comparisons on both ends (lines 57–60, 76–79), uses `COALESCE(last72_charttime, next24_charttime)` as the suspicion time (line 104; a culture time in both branches), attaches every hospitalization prescription to every ICU stay (comment lines 14–15, join lines 24–26), does not collapse multiple matching cultures (no `ROW_NUMBER`), and counts any non-empty organism as positive (line 33). Basis: source.

Two documentation inconsistencies in the MIMIC-IV file at this revision (Basis: source): the `ab_then_me` CTE comment says it selects "the earliest culture before this abx" (lines 114–115), but its join (lines 137–142) selects cultures *after* the antibiotic; and the file header says each ICU stay "will get a copy of all prescriptions for that hospitalization" (lines 1–3), but the upstream `antibiotic.sql` assigns `stay_id` only when the prescription starts inside that stay (lines 198–201). Neither changes results; both mislead a reader reconciling the code with Seymour et al. The repository's only Sepsis-3 test (`mimic-iv/tests/test_sepsis.py`) asserts one row per `stay_id`; no test fixes the window semantics above.

**SIRS (`score/sirs.sql`)** is first-ICU-day only (joins `first_day_*` tables, lines 39–45), uses `>` / `<` thresholds (temperature < 36.0 or > 38.0 °C; heart rate > 90; respiratory rate > 20 or PaCO₂ < 32; WBC < 4.0 or > 12.0 or bands > 10%), and imputes missing components as 0 (lines 89–95). Basis: source.

**Sensitivity of incidence to the definition.** On initial adult admissions to non-cardiac surgical ICUs of a Boston tertiary teaching hospital (ICU database, 2008–2012), Johnson et al. (2018) found Sepsis-3 in 49.1% of the eligible subgroup, versus 31.9% (CDC), 28.6% (Angus), 14.7% (Martin), 11.0% (CMS) and 9.0% (explicit codes); in-hospital mortality ranged from 14.5% (Sepsis-3) to 30.1% (explicit codes). Basis: documentation.

### 2. External validation of a deployed proprietary sepsis model

Design facts (Wong et al. 2021, PMC full text). Retrospective cohort, Michigan Medicine, adults admitted 6 Dec 2018 – 20 Oct 2019; 27,697 patients, 38,455 hospitalizations; ESM scores computed every 15 min from emergency-department arrival; hospitalizations eligible for live alerts on the units where the ESM was switched on were *excluded* to avoid bias. Outcome: composite of the CDC Adult Sepsis Event surveillance definition, or an ICD‑10 sepsis code with 2 SIRS criteria and 1 CMS organ-dysfunction criterion within 6 h of one another. For septic patients, scores *after* onset were excluded. The model is described as penalized logistic regression developed on 405,000 encounters from 3 health systems (2013–2015). Threshold: score ≥ 6, chosen by the local operations committee, inside the vendor-recommended 5–8 range. Basis: documentation.

Results (same source) and derived checks:

| Quantity | Reported | Recomputed from counts (support/derived_metrics.py) |
|---|---|---|
| Sepsis prevalence (hospitalization) | 2,552 (7%); Table 2 incidence 6.6% | 2552/38455 = 0.0664 |
| Hospitalization-level AUROC | 0.63 (0.62–0.64) | — |
| Horizon AUROC 24/12/8/4 h | 0.72 / 0.73 / 0.74 / 0.76 | — |
| Sensitivity at ≥ 6 | 33% | 843/2552 = 0.3303 |
| Specificity at ≥ 6 | 83% | 29775/35903 = 0.8293 |
| PPV at ≥ 6 | 12% | 843/6971 = 0.1209 |
| NPV at ≥ 6 | 95% | 29775/31484 = 0.9457 |
| Hospitalizations ever ≥ 6 | 6,971 (18%) | 0.1813 |
| Number needed to evaluate | 8 (hospitalization); 42/59/73/109 at 24/12/8/4 h | 1/0.1209 = 8.27 |
| Median lead time, first ≥ 6 to onset | 2.5 h (IQR 0.5–15.6) | — |
| Flagged but no timely antibiotics | 183 (7%) | 0.0717 |
| Calibration | "poor at all time horizons" (eFigures 1–3, plots of rescaled score) | — |
| AUROC including scores ≤ 3 h after onset | 0.80 (0.79–0.81) | — |

Basis: documentation + derived. The 2×2 table is fully determined by the four published counts, so the recomputation is a consistency check, not new evidence.

How label timing moves the number: the authors attribute the gap from the developer's internal AUROC (0.76–0.83) and a vendor-coauthored preprint (0.73; Bennett et al. 2019, arXiv:1902.07276) to "our consideration of sepsis timing", noting that a prior study found alerts at a median 7 h after the first lactate. They also argue horizon-level AUROCs "are misleading because they treat each prediction as independent." Kamran et al. (2024) extended this on 77,582 hospitalizations (3,766 septic, 4.9%) from the same health system (2018–2020), defining treatment indicators as receipt of antibiotics, fluids, blood culture and/or lactate: AUROC 0.62 (0.61–0.63) before sepsis criteria, 0.47 (0.46–0.48) before clinical recognition. Basis: documentation.

**Prediction-eligibility judgment (derived).** Let *L* be the label time and *R* the time of first clinical-recognition action. Evaluations differ only in the eligibility set of scores *s(t)*: (i) all *t*; (ii) *t < L* (Wong primary); (iii) *t < L + 3 h* (Wong sensitivity); (iv) *t < min(L, R)* (Kamran). AUROC is monotone in how much post-recognition information leaks into eligible scores, which is why (iii) > (ii) > (iv) in the reported numbers. A report that does not state its eligibility rule is not comparable to another.

**Dataset shift in operation.** Across 24 hospitals in 4 health systems, comparing the 3 weeks before and after each system's first COVID-19 case (threshold 6, at most 1 alert per patient per day), alert proportion rose from 9% (953/10,159) to 21% (1,363/6,634) while census fell 35%, and total alerts per day rose 43% (Wong et al. 2021, JAMA Netw Open); recomputed: 0.0938 → 0.2055, census −0.3470, alerts +0.4302. Finlayson et al. (2021) report that the same model "had to be deactivated" at one hospital in April 2020 "because of spurious alerting owing to changes in patients' demographic characteristics", and give a checklist grouping shift causes into technology, population/setting and behaviour changes. Basis: documentation + derived.

### 3. The prospective TREWS outcome analysis

Published design (Adams et al. 2022 abstract): 590,736 patients monitored across five hospitals; analysis restricted to 6,877 septic patients identified by the alert *before* antibiotic initiation; exposure = provider confirmation within 3 h of the alert. Companion adoption study (Henry et al. 2022 abstract): among 9,805 retrospectively identified sepsis cases the tool flagged 82%; 89% of alerts were evaluated by a physician or advanced practice provider and 38% of evaluated alerts were confirmed; confirmation within 3 h was associated with a 1.85 h (1.66–2.00) shorter median time to first antibiotic order. Basis: documentation. The TREWS model code is proprietary ("not available"); the statistical analysis code is public. Basis: documentation (Adams et al., Code availability).

Cohort and estimator as implemented (notebook at the pinned revision; Basis: source):

- **Per-site deployment dates** gate inclusion (cell 11: 2018‑04‑01, 2018‑10‑10, 2019‑02‑27, 2019‑04‑16, 2019‑05‑15 for the five sites) and admissions before 2020‑10‑01 (cell 30). A `post_covid` indicator (admission ≥ 2020‑04‑01) is a covariate (cell 9).
- **Primary inclusion ("all", cell 30):** alert = 1; sepsis = 1; alert no earlier than 1 h before admission (`hours_admission_to_alert > -1`); antibiotics not before the alert (`~(hours_alert_to_abx < 0)`) and within 24 h after it (`<= 24`); admitting unit not ICU. The pre-COVID sensitivity cohort (cell 32) instead requires `hours_alert_to_abx > 0`, so it drops antibiotics at the alert instant that the primary cohort keeps.
- **Exposure:** `confirmed_in_3_hrs = 1*(hours_alert_to_confirmation <= 3)` (cell 7); missing confirmation compares as false, so never-confirmed alerts fall in the unexposed group; the model uses `A = 1 − confirmed_in_3_hrs` (cell 37).
- **Covariates (cell 14):** six SOFA components, APACHE II, Charlson index, sex, selected comorbidities, abnormal GCS, lactate indicator, histogram-encoded age/vitals/WBC/temperature/GCS, vasopressors, mechanical ventilation, `post_covid`, and site indicators.
- **Missing data (cell 12):** binary features → 0; continuous → column mean; GCS histogram feature → 15.
- **Mortality estimator (cell 37):** `LogisticRegression(C=1000, solver='liblinear')`; predictions with the exposure column forced to 0 and to 1; absolute difference of mean predicted risks and relative reduction `1 − mean(p0)/mean(p1)`; 5,001 bootstrap replicates (replicate 0 = original sample), percentile 95% CIs, `np.random.seed(5)`.
- **Secondary outcomes (cell 37):** SOFA at 72 h by OLS with HC1 robust errors, excluding `censored`/`hospice` discharges; length of stay by median quantile regression among survivors.

Interpretation constraints (Basis: derived): the exposure is a *provider behaviour* after the alert, so the contrast estimates the association of prompt confirmation with outcome among alerted septic non-ICU patients treated within 24 h, adjusted for measured severity. It does not estimate the effect of deploying versus not deploying the system, and is exposed to confounding by unmeasured factors that drive both prompt confirmation and survival (e.g., clinical obviousness). The analysis does not report discrimination or calibration of the alert score.

### 4. NEWS2 as a fixed aggregate score

Chart 1 (RCP 2017) bands, scored 3‑2‑1‑0‑1‑2‑3 from low to high: respiration ≤8:3, 9–11:1, 12–20:0, 21–24:2, ≥25:3; SpO₂ Scale 1 ≤91:3, 92–93:2, 94–95:1, ≥96:0; SpO₂ Scale 2 ≤83:3, 84–85:2, 86–87:1, 88–92:0, ≥93 on air:0, 93–94 on oxygen:1, 95–96 on oxygen:2, ≥97 on oxygen:3; supplemental oxygen +2; systolic BP ≤90:3, 91–100:2, 101–110:1, 111–219:0, ≥220:3; pulse ≤40:3, 41–50:1, 51–90:0, 91–110:1, 111–130:2, ≥131:3; consciousness Alert:0, new confusion/Voice/Pain/Unresponsive:3; temperature ≤35.0:3, 35.1–36.0:1, 36.1–38.0:0, 38.1–39.0:1, ≥39.1:2. Chart 2 triggers: aggregate 0–4 low; a single parameter scoring 3 ("red score") low–medium, urgent ward-based response; aggregate 5–6 medium, key threshold for urgent response; ≥7 high, emergency response. Basis: normative (column positions were reconstructed from the extracted PDF text order against the chart's fixed 3‑2‑1‑0‑1‑2‑3 layout).

Executed toy transcription (`support/news2_probe.py`): values between printed bands have no defined score (temperature 35.05, 36.05, 38.05, 39.05 °C; systolic 90.5 mmHg; respiration 8.5/min), so an implementation must choose rounding; Scale 2 is non-monotone in SpO₂ (on oxygen, 92 → 0 but 97 → 3; on air, ≥93 → 0). Basis: execution (author's toy implementation of the chart, not an official calculator).

Discrimination of the original NEWS (Smith et al. 2013, abstract): 198,755 observation sets from 35,585 acute medical admissions; outcomes within 24 h of an observation set; AUROC 0.722 (0.685–0.759) cardiac arrest, 0.857 (0.847–0.868) unanticipated ICU admission, 0.894 (0.887–0.902) death, 0.873 (0.866–0.879) any outcome; the 33 comparator scores ranged 0.736–0.834 for any outcome. Basis: documentation. These are observation-set-level AUROCs over a 24 h horizon — the evaluation unit that Wong et al. criticize for sepsis alerts — so they are not directly comparable with a hospitalization-level sepsis AUROC.

### 5. Reporting, calibration and shift guidance mapped onto the two deployed-model studies

- **TRIPOD (2015)**: 22-item checklist for development, validation or updating studies; external validation requires applying the original model to new participants and comparing predictions with outcomes. **TRIPOD+AI (2024)**: 27-item checklist that "supersedes the TRIPOD 2015 checklist, which should no longer be used"; defines calibration as best assessed with "a smoothed flexible calibration curve in the individual data"; adds emphasis on fairness, reproducibility and open science. Basis: normative (reporting guidance).
- **Van Calster et al. (2019)**: four levels — mean (calibration-in-the-large), weak (intercept target 0, slope target 1; slope < 1 means estimates too extreme), moderate (flexible curve), strong ("utopic"); recommends against the Hosmer–Lemeshow test; "a minimum of 200 patients with and 200 patients without the event has been suggested" for a precise flexible curve; calls for continued local monitoring and updating. Basis: documentation.

| Recommended step | External ESM validation | TREWS outcome study |
|---|---|---|
| Outcome definition and timing stated | yes (composite; post-onset scores excluded; sensitivity analysis at +3 h) | yes in notebook (inclusion relative to alert and antibiotics); sepsis label construction not in the public code |
| Discrimination at the decision unit | hospitalization-level AUROC + horizon AUROCs | not reported for the alert score |
| Calibration intercept/slope or flexible curve | plots of rescaled score vs observed risk, judged poor; no intercept/slope reported | not reported |
| Threshold metrics and alert burden | sensitivity, specificity, PPV, NPV, NNE, alert fraction | alert evaluation and confirmation rates (companion paper) |
| Clinical utility | comparison with timely antibiotics; no decision-curve analysis | adjusted outcome contrast by confirmation timing |
| Shift monitoring | separate alert-volume study during COVID-19 | `post_covid` covariate and pre-COVID sensitivity cohort |
| Model code/coefficients available | no (proprietary) | no (proprietary); analysis code yes |

Basis: derived from the documentation and source above.

**Toy illustration of why discrimination does not certify calibration** (`support/calibration_toy.py`, synthetic data, seed 20261120, 200,000 cases): a well-calibrated logit, the same logit doubled, and the same logit shifted by +1.5 all have AUROC 0.7871; calibration slopes are 1.000, 0.500 and 1.000 and slope-fixed intercepts +0.002, +1.788 and −1.498; logistic recalibration of the doubled score restores intercept −0.000 and slope 1.000 at the same AUROC. At fixed sensitivity 0.33 and specificity 0.83, PPV is 0.038 at prevalence 2%, 0.121 at 6.6%, 0.327 at 20%. Basis: execution (toy model of a generic risk score; not a property of the ESM or TREWS).

### 6. Performance, footprint, comprehensibility and validation matrix

| Level | Evidence | Value |
|---|---|---|
| L1 authoring/maintenance | concept-file sizes at the pinned revision | `sepsis3.sql` 2,824 B; `suspicion_of_infection.sql` 7,200 B; `sofa.sql` 12,361 B; `sirs.sql` 3,392 B; `antibiotic.sql` 10,091 B; TREWS notebook 54,501 B, 60 cells (measured with `wc -c` / JSON parse). Person-time and repair cost: not measured |
| L2 build | BigQuery/PostgreSQL concept build time | not measured |
| L3 query/elaboration latency | concept SQL runtime on MIMIC-IV | not measured; transcribed-predicate probe 0.02 s wall, 11.9 MB max RSS; calibration toy 2.76 s wall, 55 MB max RSS (`/usr/bin/time`, Python 3.13, Intel Xeon 2.60 GHz VM) |
| L4 deployed execution | scoring cadence and alert load | ESM every 15 min; 18% of hospitalizations ever alert; NNE 8 (hospitalization) to 109 (4 h horizon) (Wong 2021); TREWS 89% of alerts evaluated, 38% confirmed (Henry 2022). Inference latency: not measured |
| L5 checking speed | automated checks on labels | one SQL test (one row per stay); runtime not measured |
| L6 footprint | database and artifact sizes | MIMIC-IV size not measured; probe RSS as above |

**C1 — human comprehensibility.** A reader must hold about nine interacting concepts to predict a Sepsis-3 label: two event sources (orders vs administrations), two asymmetric windows with open/closed ends, the onset rule, the location gate, six SOFA components with their 24-row maximum, missing-as-normal imputation, the zero baseline, the −48/+24 h alignment and the earliest-qualifying-pair selection. Most are nonlocal (they live in four files), and the MIMIC-III/IV divergence (Section 1) shows that even maintainers re-derived them differently. Alert evaluations add a fifth axis — prediction eligibility — that changes AUROC from 0.80 to 0.47 for one model. Diagnostics are weak: a wrong onset produces no error, only a shifted label. Basis: derived.

**C2 — simplification.** The two windows, the date-only fallbacks and the SOFA alignment are all instances of one predicate, `|t_a − t_b| ∈ [lo, hi]` with stated open/closed ends and a declared tie rule; expressing them through one parameterized interval relation (and testing it with a boundary table like the probe's) would make the MIMIC-III/IV disagreements visible as parameter differences rather than prose. Likewise, every alert evaluation can be stated as one eligibility set `t < min(L, R) + δ`, making Wong's primary, Wong's sensitivity and Kamran's analyses instances (δ = 0 with R = ∞; δ = 3 h with R = ∞; δ = 0). The constant `sepsis3` column is an unnecessary distinction. Basis: derived.

**V1–V4 — validation of labels and deployed models.**
- V1 (specification adequacy): Johnson et al. (2018) is a definition-level differential (five definitions, 9.0–31.9% incidence plus Sepsis-3 at 49.1%); `mimic-code` has no boundary tests, and the window probe here is the only executed boundary check reported. Mutation testing of the SQL: not examined.
- V2 (differential testing of the lowering): the repository's three dialect copies are a natural differential target; executing them against each other was not done (no data access).
- V3 (concurrency, crash, silicon, physical leakage): known not to apply to these batch SQL queries and retrospective analyses; the operational analogue is alert-volume telemetry (Wong 2021 JAMA Netw Open), which detected the COVID-19 surge.
- V4 (field and human validation): provider evaluation/confirmation rates (Henry 2022) and the confirmed-within-3-h outcome contrast (Adams 2022) are the only human-in-the-loop evidence; signal-temporal-logic falsification and hardware-in-the-loop replay are known not to apply. Basis: documentation + derived.

## Boundaries

- **Not examined:** MIMIC data themselves (no counts, runtimes or prevalence from the SQL); the PostgreSQL and DuckDB transliterations line by line; the `gcs`, `ventilation`, `vitalsign`, `urine_output_rate` and vasopressor-rate concept files that feed SOFA; the `alistairewj/sepsis3-mimic` and other third-party Sepsis-3 derivations; the MIMIC-III database paper; the Smith et al. full text (only the abstract); the Adams et al. and Henry et al. full texts and supplements (only abstracts, plus the public notebook); Wong et al. supplementary eMethods (calibration plots not inspected); the TRIPOD+AI item list item by item; the FDA clinical decision support guidance; a factors-across-hospitals study of the same vendor model (Lyons et al., JAMA Intern Med 2023, doi:10.1001/jamainternmed.2022.7182 — DOI resolved, content not examined, so no numbers are reported).
- **Unknown:** how the sepsis label (`sepsis` column) in the TREWS notebook is constructed (computed upstream of the public code); the ESM's version, inputs and coefficients at each site and whether any site recalibrated it; whether the strict tie exclusion in the MIMIC-IV suspicion query changes any cohort materially (requires data).
- **Known not to apply:** the NEWS AUROCs to sepsis detection (different outcome and evaluation unit); the TREWS mortality association as an estimate of the effect of deploying an alert system; the toy calibration numbers to any real model; V3-style concurrency/silicon validation to these artifacts.
- **Unsupported / not established:** that the MIMIC-IV tie exclusion is a bug — Seymour et al. do not define ties, so it is an undocumented boundary choice; that the ESM is "worse" in general — the evidence is from one academic health system (two studies) and one multi-hospital alert-volume study without accuracy; that horizon-level AUROCs are invalid in general — they answer a different question.
- **Published-number anomaly (documentation):** the Smith et al. abstract gives the lowest comparator AUROC for unanticipated ICU admission as "0.570 (0.553-0.568)", an interval whose upper bound lies below the point estimate; the correct value could not be checked without the full text.

## Evidence

All sources were accessed on 2026-11-20 (UTC).

**Source code (Git).**
- `MIT-LCP/mimic-code@303d26c623dcc9c49cc0f204468d4acc2f063797` (default-branch HEAD on the access date; commit date 2026-09-01): `mimic-iv/concepts/sepsis/sepsis3.sql` (lines 1–80), `mimic-iv/concepts/sepsis/suspicion_of_infection.sql` (1–194), `mimic-iv/concepts/score/sofa.sql` (1–379), `mimic-iv/concepts/score/sirs.sql` (1–100), `mimic-iv/concepts/medication/antibiotic.sql` (1–203), `mimic-iv/concepts/demographics/icustay_hourly.sql` (line 29), `mimic-iv/tests/test_sepsis.py`, `mimic-iii/concepts/treatment/suspicion_of_infection.sql` (1–137). Quoted key lines: `sofa_score >= 2 AND suspected_infection = 1 AS sepsis3` (sepsis3.sql:46); `AND ab_tbl.antibiotic_time > me72.charttime` (suspicion_of_infection.sql:85); `AND ab_tbl.antibiotic_time < me24.charttime` (:141); `ELSE COALESCE(last72_charttime, antibiotic_time)` (:172); `ROWS BETWEEN 23 PRECEDING AND 0 FOLLOWING` (sofa.sql:374); `AND pr.starttime >= ie.intime` / `AND pr.starttime < ie.outtime` (antibiotic.sql:200–201).
- `royadams/adams_et_al_2022_code@96fffd7a14804feb506c8b62391d2c942c541146` (HEAD; commit date 2022-05-31): `trews_patient_outcome_analysis_public.ipynb`, cells 7, 9, 11, 12, 14, 30, 32, 37 as cited. Quoted: `data['confirmed_in_3_hrs'] = 1*(data.hours_alert_to_confirmation <= 3)` (cell 7); `lr = LogisticRegression(C=1000,solver='liblinear').fit(XA_s,Y_s)` and `n_bs_samples = 5001` (cell 37).

**Literature (DOIs resolved through the DOI handle API; titles/authors confirmed against PubMed, PubMed Central, publisher or Crossref records).**
- Singer M, et al. JAMA 2016;315(8):801–810. doi:10.1001/jama.2016.0287 (PMID 26903338, PMC4968574) — Box 3.
- Seymour CW, et al. JAMA 2016;315(8):762–774. doi:10.1001/jama.2016.0288 (PMID 26903335, PMC5433435) — Methods.
- Wong A, et al. JAMA Intern Med 2021;181(8):1065–1070. doi:10.1001/jamainternmed.2021.2626 (PMID 34152373, PMC8218233) — Methods, Results, Table 2, Discussion.
- Wong A, et al. JAMA Netw Open 2021;4(11):e2135286. doi:10.1001/jamanetworkopen.2021.35286 (PMID 34797372, PMC8605481).
- Kamran F, et al. NEJM AI 2024;1(3). doi:10.1056/AIoa2300032 — abstract via NSF public access repository record 10522981.
- Bennett T, et al. arXiv:1902.07276 (submitted 2019-02-19), verified on arXiv.
- Adams R, et al. Nat Med 2022. doi:10.1038/s41591-022-01894-0 — abstract and code-availability statement.
- Henry KE, et al. Nat Med 2022. doi:10.1038/s41591-022-01895-z — abstract.
- Collins GS, et al. BMJ 2015;350:g7594. doi:10.1136/bmj.g7594. Collins GS, et al. BMJ 2024;385:e078378. doi:10.1136/bmj-2023-078378.
- Van Calster B, et al. BMC Med 2019;17:230. doi:10.1186/s12916-019-1466-7.
- Finlayson SG, et al. N Engl J Med 2021;385(3):283–286. doi:10.1056/NEJMc2104626 (PMID 34260843, PMC8665481).
- Smith GB, et al. Resuscitation 2013;84(4):465–470. doi:10.1016/j.resuscitation.2012.12.016 (PMID 23295778) — abstract.
- Johnson AEW, et al. Sci Data 2023;10:1. doi:10.1038/s41597-022-01899-x — modules, de-identification by patient-level date shift, medication tables.
- Johnson AEW, et al. Crit Care Med 2018;46(4):494–499. doi:10.1097/CCM.0000000000002965 (PMID 29303796, PMC5851804).
- Royal College of Physicians. NEWS2, December 2017: Chart 1 (scoring system) and Chart 2 (thresholds and triggers), linked from https://www.rcp.ac.uk/improving-care/resources/national-early-warning-score-news-2/ (no DOI).

**Executed probes (package `support/`).** `soi_window_probe.py` → `soi_window_probe.out.txt`; `derived_metrics.py` → `derived_metrics.out.txt`; `news2_probe.py` → `news2_probe.out.txt`; `calibration_toy.py` → `calibration_toy.out.txt` (requires numpy; run with numpy 2.3.5). Environment: Python 3.13.15, x86-64 Linux VM, Intel Xeon 2.60 GHz. Commands: `python3 <script>.py`; wall time and max RSS from `/usr/bin/time -f "wall_s=%e maxrss_kb=%M"`.

## Revalidation

1. **Cohort SQL drift:** at a new `mimic-code` revision, diff only `mimic-iv/concepts/sepsis/{sepsis3,suspicion_of_infection}.sql`, `score/sofa.sql` lines 233–379 and `medication/antibiotic.sql` lines 183–203; then update the predicate strings in `support/soi_window_probe.py` and rerun it (< 0.1 s). A change at offset 0 or in the SI-time column means the boundary semantics changed.
2. **Constant `sepsis3` column:** confirm the inner join (sepsis3.sql 55–62) and the `WHERE sofa_24hours >= 2` filter (line 20) are still present; if either becomes an outer join, the column stops being constant.
3. **ESM numbers:** rerun `support/derived_metrics.py`; it only re-derives published values and needs re-inputting if a corrected or new study is used.
4. **TREWS estimator:** at a new notebook revision, re-read cells 7, 12, 30 and 37 for the exposure definition, imputation rules, inclusion filters and `LogisticRegression` arguments.
5. **NEWS2:** compare the band table in `support/news2_probe.py` with the current RCP Chart 1 PDF; any revision of NEWS2 requires re-transcription.
6. **What cannot be cheaply revalidated:** discrimination and calibration of any proprietary model at a new site — that requires a new local external validation with an explicitly stated prediction-eligibility rule.
