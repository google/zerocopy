# Recidivism risk instruments: COMPAS audit cohorts and error measures, calibration versus error-balance impossibility, lay and rule-list baselines, PSA revalidation and field effects, arrest-label validity, and judicial limits

## Summary

- **The published audit has two cohorts, and the famous error rates come from the larger one.** `propublica/compas-analysis` at `bafff5da3f2e45eca6c2d5055faad269defd135a` ships `compas-scores-two-years.csv` (7,214 rows). The regressions and histograms use a 6,172-row subset (screening within ±30 days of arrest). The false-positive/false-negative "truth tables" (Black FPR 44.85% vs. White 23.45%; FNR 27.99% vs. 47.72%) are computed on the full 7,214 rows. On the 6,172-row cohort the same quantities are 42.34% vs. 22.01% and 28.48% vs. 49.64% (measured). Downstream papers silently pick different cohorts: Chouldechova (n = 6,150) matches the Black+White rows of the 7,214 file; Flores et al. (n = 5,278) matches the Black+White rows of the 6,172 cohort.
- **Three of the four documented exclusion filters remove nothing from the published file.** Only the screening-window filter (including missing values) removes rows (1,042 of 7,214). The `c_charge_degree != "O"` exclusion in the notebook can never fire, because `truth_tables.py` lines 192–195 rewrote every degree to `F` or `M` before writing the file. The 6,172 cohort still contains 46 rows whose original degree codes are unusual, all coded as misdemeanours: one `(CO3)`, 40 `(MO3)`, three `(NI0)` non-criminal infractions, one `(TCX)` and one `(X)`. AIF360 copies the same no-op filter.
- **On the audit data, COMPAS at "Medium or High" (decile ≥ 5) is close to predictive parity but far from error-rate balance, and the gap is forced by arithmetic once prevalence differs.** On the 6,172 cohort the base rates are 52.31% (Black) and 39.09% (White), PPV is 0.650 vs. 0.595, FPR is 0.423 vs. 0.220, and FNR is 0.285 vs. 0.496. Chouldechova's identity FPR = p/(1−p) · (1−PPV)/PPV · (1−FNR) reproduces each group's FPR to six decimals. That is an algebraic identity of the confusion matrix, not evidence about COMPAS. Kleinberg et al. prove that calibration within groups, balance for the positive class, and balance for the negative class can hold together only with perfect prediction or equal base rates. Corbett-Davies et al. show that the safety-maximizing unconstrained rule is a single threshold, while statistical parity and predictive equality force race-specific thresholds.
- **Simple models match or slightly beat the proprietary score on this data, but only by small margins.** On the 6,172 cohort (measured), COMPAS at decile ≥ 5 has accuracy 0.661 and AUC 0.710. A two-feature logistic regression on age and priors has 10-fold CV accuracy 0.679 and AUC 0.728; the bootstrap 95% interval for its accuracy gain over COMPAS is [+0.6, +3.1] percentage points. Two published CORELS rule lists score 0.659 and 0.673. Untrained online participants matched COMPAS under the original protocol: 67.0% for pooled crowds vs. 65.2% for COMPAS on 1,000 defendants (Dressel–Farid). They fell behind once immediate feedback was removed or the base rate was low: 60% accuracy without feedback vs. 89% for COMPAS on violent rearrest (Lin et al.).
- **CORELS prints "OPTIMAL RULE LIST" whether or not optimality was certified, and an uncertified run can return a suboptimal list.** All runs used the repository's shipped COMPAS training file.
  - `-r 0.015` empties the queue in about 1.2 s with 4.7 MB peak RSS: a certified two-rule list.
  - `-r 0.01`, `0.005` and `0.001` hit the default 100,000-node cap. The minimum lower bound left in the queue is then below the reported objective, so optimality is not certified, yet the same header is printed.
  - At `-r 0.005` the capped run returned a three-rule list with objective 0.35357. With `-n 50000000` the search certified a different four-rule list with objective 0.34809, after 467 s and 600 MB peak RSS. That four-rule list is the README's example, up to the order of two "yes" rules.
- **The file's `age` column is age on 2016-04-19, not age at screening.** All 7,214 rows match that reference date exactly. The column exceeds age at the screening date by 1–4 years. For 1,012 of the 6,172 cohort rows, `age_cat` differs from the category implied by age at screening.
- **The pretrial PSA publishes its formula and has local revalidation and field evidence, but the evidence shows modest discrimination and small behavioural effects.** The formula has 9 factors, with point weights summing to at most 7 (FTA), 13 (NCA) and 7 (NVCA flag). In Kentucky (n = 164,597 released defendants) the AUCs are 0.646 (FTA), 0.650 (NCA) and 0.664 (NVCA), with differential prediction by race for FTA only. Kentucky's 2011 risk-assessment mandate produced a small release increase that eroded, and switching to the PSA in 2013 had essentially no effect on releases, FTA or pretrial crime (Stevenson). A randomized trial in Dane County, Wisconsin found little overall effect of showing the PSA to judges (Imai et al.).
- **Rearrest is a biased and heterogeneous proxy for reoffence, but not uniformly in one racial direction.** In NIBRS violent-offence data, 56% of incidents with White offenders and 42% with Black offenders resulted in arrest. The gap varies strongly by offence type and jurisdiction, and the authors decline causal conclusions (Fogliato et al.).
- ***State v. Loomis* (2016 WI 68) permits a proprietary score at sentencing only under limits.** The score may not be used to decide whether to incarcerate or how severe the sentence is, and may not be determinative on community supervision. The court must give independent reasons. Every presentence report carrying the score must include a written advisement of five cautions.

## Applicability

**Subjects and their relationship.** The report interprets one audit data release (`propublica/compas-analysis` at `bafff5da3f2e45eca6c2d5055faad269defd135a`) through three bodies of work:

1. the formal fairness results of Chouldechova, Kleinberg et al. and Corbett-Davies et al.;
2. alternative predictors: online lay participants (Dressel–Farid; Lin et al.), CORELS rule lists (`corels/corels` at `c54cba53b5f6c62472bef508c68c565367ba474c`; Angelino et al.), and a logistic baseline;
3. two widely used fairness toolkits, examined at source level only: `Trusted-AI/AIF360` at `34877916b789e569edf5c0aac033403ca90f34b3` and `fairlearn/fairlearn` at `34e44252a292159eecb67d94f6ef7f391d69c8bd`.

The PSA material (the Arnold Foundation formula sheet, DeMichele et al., Stevenson, Imai et al.) concerns a different instrument, and pretrial release rather than sentencing. It is a comparison case, not evidence about COMPAS. Fogliato et al. concerns the outcome label used by all of these instruments. *State v. Loomis* concerns legal conditions on using COMPAS in Wisconsin sentencing.

**Exact observation scope.**

- *Data.* Broward County, Florida pretrial COMPAS assessments from 2013–2014 with two-year rearrest follow-up, and the general "Risk of Recidivism" decile score only. Violent-recidivism and failure-to-appear scores were not analysed, except where quoted from papers.
- *Threshold and groups.* Most of the analysis uses the "Medium or High" threshold (decile ≥ 5, equivalently `score_text != "Low"`; verified equal on every row). Groups follow the file's `race` labels `African-American` and `Caucasian`, rendered here as Black and White.
- *Execution.* The probe ran on the published CSV (SHA-256 `c451db85…d0cc7d`), checked at run time. CORELS was built from source and run on the repository's own `data/compas_train.*` files. AIF360 and fairlearn were **not executed**: their behaviour is stated from source reading, and the metric definitions were re-implemented in the probe.

**Not extended.** No claim is made about other jurisdictions' COMPAS norms, later COMPAS versions, or other COMPAS scales. Nor is any claim made about PSA performance outside Kentucky, or outside the preliminary Dane County trial data. Numbers quoted from papers apply to each paper's own sample, which this report states each time because the cohorts differ.

## Findings

### 1. Audit data provenance and cohort construction

Basis: documentation + source + execution.

Larson et al. (methodology) obtained COMPAS scores for 18,610 people scored in 2013–2014 and kept 11,757 pretrial assessments. They matched these to Clerk of Courts records collected through 2016-04-01 by first name, last name and date of birth. In a random sample of 400 cases, that matching had a 3.75% (±1.8%) error rate. Recidivism means a new fingerprintable arrest within two years. Traffic tickets, some municipal-ordinance violations and failure-to-appear arrests are excluded. People with less than two years of follow-up are excluded unless they recidivated.

`truth_tables.py` builds `compas-scores-two-years.csv` from `cox-parsed.csv`, which has one row per custody interval:

- a person's `lifetime` is the sum of `end − start` over their rows (lines 41–45);
- `recidivist` means `is_recid == "1"` and `lifetime <= 730` (lines 47–50);
- the population keeps people with a valid score who either recidivated within 730 days or had more than 730 days of follow-up (lines 214–216).

| Cohort | Rows | Black | White | Used by |
|---|---:|---:|---:|---|
| Full two-year file | 7,214 | 3,696 | 2,454 | ProPublica truth tables (notebook cells 70–84); Dressel–Farid Table 2; Chouldechova (n = 6,150 = 3,696 + 2,454) |
| ±30-day screening window | 6,172 | 3,175 | 2,103 | ProPublica logistic models and histograms (notebook cell 4); Flores et al. (n = 5,278 = 3,175 + 2,103); AIF360 default preprocessing |
| CORELS repository split | 6,489 train + 721 test (7,210 of 7,214 rows) | not split by race | | `corels/corels` `data/compas_{train,test}.*` |
| Angelino et al. (JMLR) | 6,907 "without missing data" | | | CORELS paper experiments |

Larson et al. explain the split: the 7,214 population "slightly larger than the sample in the logistic models above, because we don't need a defendant's case information for this analysis". Chouldechova describes her 6,150 rows as following "the same data pre-processing and filtering as reported in the ProPublica analysis". Those rows are the Black+White subset of the unfiltered 7,214 file, not of the 6,172 cohort (derived from the counts above). A reader comparing her error rates with Flores et al.'s is comparing different cohorts.

### 2. The exclusion filters, and the one that cannot fire

Basis: source + execution.

The notebook's cell 4 (raw JSON line 93 of `Compas Analysis.ipynb`) applies:

```r
filter(days_b_screening_arrest <= 30) %>%
filter(days_b_screening_arrest >= -30) %>%
filter(is_recid != -1) %>%
filter(c_charge_degree != "O") %>%
filter(score_text != 'N/A')
```

Its markdown (cell 3) says ordinary traffic offences "with a `c_charge_degree` of 'O' … are removed (only two of them)". But `truth_tables.py` writes the file with:

```python
            if person.compas_felony:          # line 192; compas_felony = 'F' in c_charge_degree (line 109)
                row['c_charge_degree'] = 'F'
            else:
                row['c_charge_degree'] = 'M'  # line 195
```

Measured on the published 7,214-row file:

- `c_charge_degree` takes only the values `F` (4,666) and `M` (2,548);
- `is_recid == -1` occurs 0 times; so does `score_text == 'N/A'`;
- `days_b_screening_arrest` is empty in 307 rows (R's `filter` drops `NA`) and outside ±30 in 735 rows: 307 + 735 = 1,042, and 7,214 − 1,042 = 6,172.

Tracing the original degree codes from `cox-parsed.csv`, the 6,172 cohort contains, all coded `M`:

- one `(CO3)` ("arrest case no charge");
- 40 `(MO3)` (e.g. "arrest case no charge" ×12, "Poss Of Controlled Substance" ×6);
- three `(NI0)` ("Ride Tri-Rail Without Paying", "Violation Of Boater Safety Id", "Possess Tobacco Product Under 18");
- one `(TCX)` ("License Suspended Revoked");
- one `(X)`.

This report does not establish which raw codes the notebook's "O" was meant to match. Whatever they were, no row of the published file can match it.

The numerical effect on headline rates is small: even if every row with one of these unusual codes were excluded, 46 of 6,172 rows (0.75%, derived) would be affected. The structural lesson is that a documented exclusion was vacuous. AIF360's `default_preprocessing` (`aif360/datasets/compas_dataset.py` lines 18–22) replicates all five filters verbatim, including the vacuous ones.

A related precedence detail sits at `truth_tables.py` lines 102–105:

```python
return (self.__rows[0]['is_recid'] != "-1" and
        (self.recidivist and self.lifetime <= 730) or
        self.lifetime > 730)
```

Python parses this as `(A and B) or C`. People with `is_recid == "-1"` and more than 730 days of follow-up would therefore be admitted. `cox-parsed.csv` contains no `is_recid == "-1"` rows, so this has no effect on the published file (measured). Whether it was intended is unknown.

AIF360 additionally keeps `c_charge_desc` (line 38) and calls `df.dropna()` (`standard_dataset.py` line 97). Five of the 6,172 rows have an empty `c_charge_desc`, so the toolkit's dataset should have 6,167 rows (derived; not executed). The loader also drops the COMPAS score columns entirely: `features_to_keep` (lines 36–39) excludes `decile_score` and `score_text`. It therefore supports training new classifiers, not auditing COMPAS. It maps `sex` with `Female` as privileged and `race` as `Caucasian` vs. "Not Caucasian" (lines 31–32). The label `0` (no recidivism) is favourable (line 30).

### 3. Error rates, predictive values and calibration by group (measured)

Basis: execution (`support/compas_probe.py` on the pinned CSV).

Classifier: predict recidivism if decile ≥ 5.

| Cohort / group | n | prevalence | FPR | FNR | PPV | NPV | accuracy | selection rate | AUC (decile) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6,172 all | 6,172 | 0.4551 | 0.3027 | 0.3831 | 0.6300 | 0.6855 | 0.6607 | 0.4457 | 0.7098 |
| 6,172 Black | 3,175 | 0.5231 | 0.4234 | 0.2848 | 0.6495 | 0.6486 | 0.6491 | 0.5761 | 0.7043 |
| 6,172 White | 2,103 | 0.3909 | 0.2201 | 0.4964 | 0.5948 | 0.7100 | 0.6719 | 0.3310 | 0.6928 |
| 7,214 all | 7,214 | 0.4507 | 0.3235 | 0.3740 | 0.6135 | 0.6880 | 0.6537 | 0.4598 | 0.7022 |
| 7,214 Black | 3,696 | 0.5143 | 0.4485 | 0.2799 | 0.6297 | 0.6505 | 0.6383 | 0.5882 | 0.6918 |
| 7,214 White | 2,454 | 0.3936 | 0.2345 | 0.4772 | 0.5913 | 0.7119 | 0.6699 | 0.3480 | 0.6931 |

The 7,214 rows reproduce the notebook's printed confusion matrices exactly (Black: TN 990, FP 805, FN 532, TP 1,369; White: TN 1,139, FP 349, FN 461, TP 505). They also reproduce Dressel–Farid's COMPAS column (accuracy 65.4%, 63.8% Black, 67.0% White; FPR 44.8%/23.5%).

On the 6,172 cohort, fairlearn-style group metrics re-implemented from source (Black vs. White) are:

- equalized-odds difference = max(|ΔTPR|, |ΔFPR|) = 0.2116;
- demographic-parity difference = 0.2451;
- PPV gap = 0.0547.

Fairlearn's `equalized_odds_difference` returns `max(eo.difference(method=method))` for `agg="worst_case"` (`_fairness_metrics.py` line 186) over a frame of `{"tpr", "fpr"}` (line 260).

**Category-level calibration (6,172 cohort, measured)** reproduces Flores et al.'s Table 1 exactly:

| Group | Low (1–4) | Medium (5–7) | High (8–10) |
|---|---:|---:|---:|
| Black | 0.351 (n = 1,346) | 0.563 (n = 984) | 0.750 (n = 845) |
| White | 0.290 (n = 1,407) | 0.533 (n = 473) | 0.726 (n = 223) |

By decile the rates are close but not identical. For example, decile 3 has 0.419 (Black) vs. 0.345 (White), and decile 10 has 0.837 (n = 227) vs. 0.700 (n = 50). No calibration test statistic was computed (see Boundaries).

### 4. The impossibility results and what the data force

Basis: normative (theorem statements) + derived + execution.

**Chouldechova (2017), eq. (2.6).** At a threshold s_HR, prevalence p, PPV, FPR and FNR satisfy

$$\mathrm{FPR} = \frac{p}{1-p}\cdot\frac{1-\mathrm{PPV}}{\mathrm{PPV}}\cdot(1-\mathrm{FNR}).$$

If PPV is equal across groups (predictive parity, her Definition 2) and p differs, FPR and FNR cannot both be equal (error-rate balance, Definition 3). Her paper reports COMPAS as approximately calibrated and as satisfying predictive parity for s_HR ≥ 4, while failing error-rate balance at every cutoff.

Taking ratios between groups (derived) decomposes the FPR disparity into three factors:

FPR_B / FPR_W = [odds(p_B) / odds(p_W)] × [((1−PPV_B)/PPV_B) / ((1−PPV_W)/PPV_W)] × [(1−FNR_B) / (1−FNR_W)]

On the 6,172 cohort the factors are 1.709 × 0.792 × 1.420 = 1.923, matching the measured ratio 1.9232:

- the prevalence-odds factor alone (1.71) would produce a large FPR gap even with identical PPV and FNR;
- COMPAS's higher PPV for Black defendants shrinks the gap (0.79);
- its higher sensitivity for Black defendants widens it (1.42).

**Kleinberg, Mullainathan, Raghavan (2017).** A risk assignment can satisfy all three of the following only if prediction is perfect or the groups have equal base rates; approximate satisfaction requires approximately those cases:

- (A) calibration within groups;
- (B) balance for the negative class: equal mean score among true negatives across groups;
- (C) balance for the positive class.

The theorem concerns score means, not thresholded rates. Measured on the 6,172 cohort, the mean decile among non-recidivists is 4.225 (Black) vs. 2.942 (White), and among recidivists 6.236 vs. 4.715. Both balance conditions fail by more than one decile, consistent with approximate calibration plus unequal base rates.

**Corbett-Davies et al. (2017).** Release decisions are treated as maximizing public safety minus detention cost:

- the unconstrained optimum detains everyone above a single risk threshold;
- the optima under statistical parity, conditional statistical parity and predictive equality detain above group-specific thresholds.

On Broward data, they used 3,377 Black and White defendants with two-year violent recidivism and a re-trained L1-logistic model, whose held-out AUC was 0.75 vs. 0.73 for the COMPAS violent score. Holding detention at 30% (the COMPAS ≥ 5 fraction), they estimated:

| Constraint | Detainees who are low risk | Estimated increase in violent crime |
|---|---:|---:|
| Statistical parity | 17% | 9% |
| Predictive equality | 14% | 7% |
| Conditional statistical parity (priors only legitimate) | 10% | 4% |

These figures are averaged over 100 70/30 splits.

**Toolkit consequences (source).** Fairlearn's `ThresholdOptimizer` offers `SIMPLE_CONSTRAINTS` (`demographic_parity`, `selection_rate_parity`, `false_positive_rate_parity`, `false_negative_rate_parity`, `true_positive_rate_parity`, `true_negative_rate_parity`) plus `equalized_odds` (`_threshold_optimizer.py` lines 68–77). It has **no calibration or predictive-parity constraint**. It needs `sensitive_features` at prediction time and refuses unseen groups (`_constants.py` lines 14–17). Its predictions are randomized (`random_state`, line 361). These are exactly the group-specific, randomized thresholds that Corbett-Davies et al. characterize as the optimum under error-rate constraints.

### 5. Developer validation and the dispute over error measures

Basis: documentation.

| Claim source | Sample / outcome | Measure | Reported result |
|---|---|---|---|
| Brennan, Dieterich, Ehret 2009 (developer) | 2,328 presentence-investigation and probation-intake cases; Cox models, three outcome criteria | AUC | 0.66–0.80 across subpopulations; majority > 0.70 |
| Larson et al. 2016 (audit) | 7,214 (truth tables); 6,172 (logit); Cox on `cox-parsed.csv` | FPR/FNR by race; logistic odds of a higher score; Cox concordance | FPR 44.85/23.45, FNR 27.99/47.72; Black defendants 45% more likely to get a higher score after controls; concordance 0.636 (category), 0.664 (decile) vs. the developer's 0.68 |
| Flores, Bechtel, Lowenkamp 2016 (rejoinder) | 5,278 Black+White (any arrest); 3,967 (violent) | AUC by race with z-tests; logistic slope/intercept interaction tests; DIF-R | AUC 0.71 all, 0.69 White, 0.70 Black; category failure rates similar across race; "no bias" under test-bias framework |
| Northpointe (Dieterich, Mendoza, Brennan 2016), as summarized by Chouldechova and Dressel–Farid | Same data | predictive parity; "accuracy equity" (AUC) | COMPAS satisfies both; primary report not examined here |

The disagreement is definitional:

- The audit measures **error rates conditional on the outcome** (P(high | did not recidivate, group)).
- The rejoinder measures **outcome rates conditional on the score**, plus discrimination (AUC) and regression form.

On the same 6,172-row data, this report reproduces both sides' numbers (§3). Chouldechova's identity shows that both cannot be equalized when prevalence differs (§4).

One documentation inconsistency: Larson et al. report mean non-incarcerated follow-up as "622.87 days (sd: 329.19)", but notebook cell 73 prints "Average followup time 622.87 (sd 392.19)".

### 6. Lay predictors, simple models and rule lists

Basis: documentation + execution.

**Dressel–Farid (2018).** Mechanical Turk participants judged 1,000 defendants split into 20 subsets of 50, with 400 retained participants per condition after catch-trial exclusions (462 → 400; 449 → 400). They saw sex, age, charge, charge degree, and prior and juvenile counts, and received **immediate feedback after every answer**.

- Mean and median individual accuracy were 62.1% and 64.0%. Pooling 20 responses per defendant by majority gave 67.0%, vs. COMPAS's 65.2% on the same 1,000 (P = 0.85 for COMPAS better than the crowd).
- The crowd AUC was 0.71 vs. COMPAS's 0.70.
- On all 7,214 defendants, logistic regression with 7 features scored 66.6%, with 2 features (age, priors) 66.8%, and a nonlinear SVM 65.2%, vs. COMPAS's 65.4%.

**Lin et al. (2020).** This replication used the same 1,000 defendants and elicited probabilities. Participants received $1 plus up to a $5 Brier-score bonus, and only the 71% who passed attention checks were analysed.

- Under feedback on the original task: participants 64%, COMPAS 65%, the authors' logistic model 68%; without feedback, participants 62%.
- On violent rearrest (base rate 11%): COMPAS and logistic 89%; participants 83% with feedback and 60% without, because they overestimated risk despite being told the base rate.
- Enriched information (LSI-R factors) helped models more than people.
- Dressel–Farid's AUC of 0.71 is a crowd-pooled AUC, not an average individual AUC.

**This report's baselines (6,172 cohort, measured).** Classifiers were scored at threshold 0.5 (logistic) or as printed (rule lists). Intervals are paired percentile bootstraps over defendants with each classifier's predictions held fixed; they exclude the variance from refitting the CV models.

| Predictor | Accuracy | Black FPR / FNR / PPV | White FPR / FNR / PPV | Δ accuracy vs. COMPAS (bootstrap 95%, B = 1,000) |
|---|---:|---|---|---|
| COMPAS decile ≥ 5 | 0.6607 (95% [0.6492, 0.6721]) | 0.423 / 0.285 / 0.650 | 0.220 / 0.496 / 0.595 | — |
| Logistic(age column, priors), 10-fold CV | 0.6790 (AUC 0.7277) | 0.262 / 0.374 / 0.724 | 0.127 / 0.636 / 0.647 | [+0.0063, +0.0308] |
| Logistic(age at screening, priors), 10-fold CV | 0.6745 (AUC 0.7228) | not tabulated | not tabulated | not computed |
| CORELS README example rule list (prediction-equivalent to the certified `-r 0.005` list) | 0.6585 | 0.491 / 0.214 / 0.637 | 0.278 / 0.454 / 0.558 | [−0.0151, +0.0107] |
| Angelino et al. JMLR Figure 1 rule list | 0.6727 | 0.388 / 0.294 / 0.666 | 0.214 / 0.502 / 0.599 | [−0.0011, +0.0250] |

Three caveats apply to this comparison:

- Accuracy comparisons at different operating points are not like-for-like. The logistic classifier selects far fewer people (lower FPR, higher FNR in both groups), so AUC (0.728 vs. 0.710) is the fairer discrimination comparison.
- Every predictor shows the same direction of FPR/FNR disparity, as §4 predicts for any reasonably calibrated predictor at a common threshold.
- The rule lists were fitted on other splits that include this cohort's rows, so their accuracies here are not held-out.

**CORELS in practice (execution).** The objective is R(d) = misclassification(d) + c·length(d). Each prefix's lower bound is the parent bound minus the parent's equivalent-points term, plus prefix mistakes / n, plus c (`src/corels.cpp` line 76). Search prunes when the bound reaches the best objective (line 79). The equivalent-points bound adds the fraction of uncapturable "minority" points (lines 108–112). Built with `make NGMP=1 corels` and run as `./corels -r <c> -c 2 -p 1 ../data/compas_train.{out,label,minor}` on the 6,489-row training file:

| `-r` | Node cap | Exit | Min objective | Min lower bound left | Train accuracy | Wall | Peak RSS | Rule list |
|---|---:|---|---:|---:|---:|---:|---:|---|
| 0.015 | 100,000 | queue empty (certified) | 0.37797 | 1.0 (none) | 0.65203 | 1.17 s | 4.7 MB | {male ∧ juvenile-crimes > 0} → yes; {priors > 3} → yes; else no |
| 0.01 | 100,000 | node cap | 0.36797 | 0.35239 | 0.65203 | 0.88 s | 36.9 MB | same list |
| 0.01 | 50,000,000 | queue empty (certified) | 0.36797 | 1.0 (none) | 0.65203 | 43.96 s | 48.5 MB | same list |
| 0.005 | 100,000 | node cap | 0.35357 | 0.33493 | 0.66143 | 0.60 s | 35.4 MB | {age 18–20} → yes; {male ∧ age 21–22} → yes; {priors > 3} → yes; else no |
| 0.005 | 50,000,000 | queue empty (certified) | 0.34809 | 1.0 (none) | 0.67191 | 467.51 s | 599.9 MB | {age 23–25 ∧ priors 2–3} → yes; {male ∧ age 21–22} → yes; {age 18–20} → yes; {priors > 3} → yes; else no |
| 0.001 | 100,000 | node cap | 0.34149 | 0.32223 | 0.66251 | 0.66 s | 35.4 MB | four-rule list beginning {age 23–25 ∧ priors = 0} → no |

`run_corels_end` calls `print_final_rulelist` whenever an output file name is set (`src/run.cpp` lines 165–166). That function prints `"\nOPTIMAL RULE LIST\n"` unconditionally (`src/utils.cpp` line 134). The only certification signal is the "Exited because …" line printed by `src/corels.cpp` lines 247–253, together with the minimum lower bound.

The `-r 0.005` pair shows the consequence. The node-capped run labels a three-rule list (objective 0.35357) as optimal, but the certified optimum is a different four-rule list (objective 0.34809). The certified list contains exactly the rules of the README's "Example rule list" (age 23–25 ∧ priors 2–3; age 18–20; male ∧ age 21–22; priors > 3). Only the order of two consecutive "yes" rules differs, and that order cannot change predictions (derived). With the default cap, the README example therefore cannot be reproduced at `-r 0.005`; reproducing it requires a larger `-n`.

The JMLR paper reports mean 10-fold test accuracy of 0.665 (sd 0.018) for CORELS (λ = 0.005, feature set A, 122 antecedents) vs. 0.660 (sd 0.019) for COMPAS on its 6,907-row subset. The paper's age bins (21–23) differ from the repository's processing bins (21–22, 23–25; `processing/compas.py` lines 16–27).

**Rudin, Wang, Coker (2020).** They partially reconstructed COMPAS subscales from probation data. They argue that COMPAS depends nonlinearly on age, contrary to its documented linear form. After subtracting a hypothesized age component, they find no necessary dependence on race beyond age and criminal history. They also show that a model based only on age is as "unfair" as COMPAS by ProPublica's FPR criterion, and that many defendants have long criminal histories but low scores, which they attribute to probable data inconsistencies. These are inferences from a partial reconstruction, not inspection of COMPAS.

### 7. A data-quality observation: the `age` column

Basis: execution.

For every one of the 7,214 rows, `age` equals completed years between `dob` and **2016-04-19**. That is the only reference date in 2014–2017 that matches all rows; the next best, 2016-04-18, matches 7,200. That date is consistent with the records-collection cutoff of 2016-04-01 given by Larson et al. Age at `compas_screening_date` is smaller by 1 year (336 rows), 2 years (2,743), 3 years (3,845) or 4 years (290).

`age_cat` agrees with the category of this `age` in 7,101 of 7,214 rows. It disagrees with the category of age at screening in 1,012 of the 6,172 cohort rows. CORELS' processing script computes age at the screening date from `dob` (`processing/compas.py` lines 11–14 and 83).

Any model using the file's `age` or `age_cat` therefore uses age at data collection. This includes the notebook's logistic regression of score on `age_cat` and the age term in Dressel–Farid's two-feature model, if it used the column. In the probe the logistic accuracy changes from 0.6790 to 0.6745 when age at screening is used instead (measured). Effects on the published regression coefficients were not re-estimated.

### 8. The PSA: formula, revalidation, and field effects

Basis: documentation.

**Formula** (Laura and John Arnold Foundation, "Risk Factors and Formula", ©2013–2016). There are nine factors. Points:

- **FTA** (max 7):
  - pending charge 1;
  - prior conviction 1;
  - prior FTA in the past 2 years: 0 → 0, 1 → 2, ≥ 2 → 4;
  - prior FTA older than 2 years 1.
- **NCA** (max 13):
  - age ≤ 22 at current arrest 2;
  - pending charge 3;
  - prior misdemeanour conviction 1;
  - prior felony conviction 1;
  - prior violent conviction: 1–2 → 1, ≥ 3 → 2;
  - prior FTA in the past 2 years: 1 → 1, ≥ 2 → 2;
  - prior incarceration sentence 2.
- **NVCA flag** (max 7):
  - current violent offence 2;
  - current violent offence ∧ age ≤ 20 1;
  - pending charge 1;
  - prior conviction 1;
  - prior violent conviction: 1–2 → 1, ≥ 3 → 2.

The maxima check by summation: 1 + 1 + 4 + 1 = 7; 2 + 3 + 1 + 1 + 2 + 2 + 2 = 13; 2 + 1 + 1 + 1 + 2 = 7 (derived). FTA and NCA raw scores convert to 1–6 scales, and NVCA yields a binary flag. The sheet states that race, ethnicity and geography are not inputs. The formula is published, but the sheet also states that the PSA "cannot be implemented … without LJAF's express, prior written consent". It is transparent, not openly licensed.

**Kentucky revalidation (DeMichele et al. 2018).** Bookings ran from 2013-07-01 to 2014-12-30. 164,597 defendants (68.5%) were released and analysed; 75,662 (31.5%) were detained. Base rates were FTA 14.8%, NCA 10.6% and NVCA 1.1%. AUCs were 0.646 (FTA), 0.650 (NCA) and 0.664 (NVCA): "good" on the Desmarais–Singh scale, and slightly weaker for Black defendants (0.61–0.63). Regression tests found race moderating FTA prediction (flatter slopes, higher intercepts for Black defendants), no significant race differences for NCA or NVCA, and gender differences for NVCA. Outcomes are observed only for released defendants: a selective-labels limitation the authors acknowledge as weakening external validity.

**Field effects (Stevenson 2018).** Kentucky's HB 463 (2011) made risk assessment mandatory, with a presumptive non-monetary release for low- and moderate-risk defendants, who were about 90% of defendants. Effects:

- Release rose only trivially. FTA and pretrial crime rose with it.
- Judges deviated from the presumptive default in more than two-thirds of cases.
- Non-monetary release for low-risk defendants rose 63%, but the change eroded within a couple of years, to below the pre-law release rate.
- Within counties, Black and White defendants saw similar changes.
- The 2013 switch to the PSA produced "a small increase in the use of non-financial bond, and essentially no effect on releases, FTAs, pretrial crime, or racial disparities in detention".

**Randomized evidence (Imai et al. 2023).** In Dane County, Wisconsin, provision of the PSA and its decision-making framework to judges was randomized by the parity of the case number's last digit. On preliminary data (1,891 first-appearance cases), showing the PSA had little overall effect on judges' decisions or arrestee outcomes. There was suggestive evidence of more lenient decisions for female arrestees and stricter ones for risky male arrestees.

### 9. Arrest as the outcome label

Basis: documentation.

All of the instruments above are trained and validated on **rearrest**, not reoffence: COMPAS (two-year arrest), the PSA (NCA/NVCA are new arrests or charges), and the Lin et al. LSI-R datasets (rearrest; reincarceration in one dataset). Fogliato et al. (2021) analysed NIBRS incident-level violent offences (2007–2016, 16 states; Black and White offenders only):

- Arrest followed in 56% of incidents with White offenders vs. 42% with Black offenders.
- The gap was largest for robbery (36% vs. 19%) and aggravated assault (62% vs. 44%), and small for murder (73% vs. 67%) and rape (27% vs. 25%).
- Arrest rates for interracial crimes were within 2% across groups, except robbery.
- Much of the aggregate gap tracks geography. For simple assault, the 13-point aggregate gap (57% vs. 43%) shrinks to a pooled state-level mean gap of 6 points (sd 6).
- In Memphis, 26% of offences led to arrest and 89% of offenders were identified as Black.

The authors conclude that arrest data on violent crimes are not a random sample of offences. Instruments trained on rearrest may be miscalibrated relative to reoffence for subpopulations concentrated in low-arrest jurisdictions. Naive corrections can worsen disparities, and the data support no causal conclusion. "Violent rearrest is a clean label" and "arrest labels uniformly inflate Black risk" are both unsupported by this evidence.

### 10. Conditions on judicial use: *State v. Loomis*

Basis: normative (court opinion).

The Wisconsin Supreme Court (2016 WI 68, decided 2016-07-13) held that considering a COMPAS risk assessment at sentencing does not violate due process if its use is circumscribed.

- **Prohibited uses.** Under ¶98, risk scores may not be used:
  - "(1) to determine whether an offender is incarcerated";
  - "(2) to determine the severity of the sentence";
  - "as the determinative factor in deciding whether an offender can be supervised safely and effectively in the community".
- **Independent reasons.** Under ¶99, the court must explain the factors, besides the assessment, that independently support the sentence.
- **Written advisement.** Under ¶100, any presentence investigation report containing COMPAS must carry a written advisement of five cautions:
  1. the proprietary nature of COMPAS prevents disclosure of how factors are weighed;
  2. scores identify groups of high-risk offenders, not a particular high-risk individual;
  3. some studies raise questions about whether COMPAS disproportionately classifies minority offenders as higher risk;
  4. COMPAS compares defendants to a national sample with no Wisconsin cross-validation;
  5. tools must be constantly monitored and re-normed.
- **Updating.** Under ¶101, the cautions are to be updated as evidence changes, for example after a Wisconsin cross-validation.

The Chief Justice's concurrence (¶123) stresses that courts may *consider* but not *rely on* COMPAS.

### 11. Performance and resource footprint (L1–L6)

Basis: execution where marked, otherwise cited. Host class for measurements: 96-vCPU x86-64 Linux workstation (Intel Xeon 2.60 GHz, 236 GiB RAM), Python 3.13, g++ 15.2.

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | audit code size | `truth_tables.py` 229 lines; notebook 102 cells | source |
| L1 | probe for this report | 347 lines stdlib Python | execution (file size) |
| L1 | person-months or LLM tokens to build any instrument | not measured | — |
| L2 toolchain build | CORELS from scratch (`make NGMP=1 corels`, serial) | 10.5 s wall; binary 2,238,712 bytes (with `-g`) | execution |
| L2 | AIF360 / fairlearn install | not measured (not installed) | — |
| L3 fitting/search latency | CORELS COMPAS train (6,489 rows, 155 antecedents), certified at `-r 0.015` | 1.17 s, 99 prefixes evaluated | execution |
| L3 | CORELS certified at `-r 0.01` / `-r 0.005` | 43.96 s / 467.51 s with a 50M-node cap (3,802 / 64,646 prefixes evaluated) | execution |
| L3 | CORELS paper | optimal list "in a matter of seconds", certification "within about 10 minutes" on its benchmarks | cited (Angelino et al. JMLR) |
| L3 | probe end-to-end (cohorts, 3×10-fold logit fits, B = 1,000 bootstrap) | 11.4 s wall | execution |
| L4 scoring cost | rule list: ≤ 4 rule tests per defendant; PSA: ≤ 9 additive lookups; COMPAS: 137 features (Dressel–Farid) incl. questionnaire | per-prediction latency not measured | derived/cited |
| L5 checking | independent re-check of a CORELS optimality certificate | unsupported (no certificate format; only queue-exhaustion message) | source |
| L5 | re-deriving the audit's headline tables from the CSV | 11.4 s (whole probe) | execution |
| L6 memory/disk | CORELS peak RSS | 4.7 MB (certified `-r 0.015`); 35–48 MB at 0.01–0.001 with default or 50M cap; 599.9 MB for the certified `-r 0.005` search | execution |
| L6 | CORELS without the equivalent-points bound, ablation | terminated at 5 × 10⁸ cache elements after ~250 GB RAM | cited (Angelino et al.) |
| L6 | probe peak RSS | 50.5 MB | execution |
| L6 | audit artefacts | `compas-scores-two-years.csv` 2,546,489 B; `cox-parsed.csv` 4,594,051 B; `compas.db` 62,816,256 B | source (Git tree sizes) |
| L6 | energy | not measured | — |

### 12. Comprehensibility and conceptual simplicity (C1–C2)

Basis: derived.

- **C1, working-memory load of the fairness debate.** Every criterion in the dispute is a constraint on four confusion-matrix cells plus prevalence, or on score-conditional outcome rates. A reader needs only (i) the 2×2 table per group and (ii) eq. (2.6) to see that "biased" and "unbiased" can both be true of the same table. Leaving prevalence unstated is the main legibility hazard: claims are usually phrased as one rate ("twice as likely") without the conditioning event.
- **C1, legibility of instruments.** A four-rule list or the PSA's nine additive factors can be audited by hand, and their failure cases are enumerable. COMPAS's 137 inputs and undisclosed weights cannot. *Loomis*'s first caution exists precisely because of that.
- **C1, hidden footguns.** All of these are invisible in summary statistics:
  - the vacuous `c_charge_degree` filter (§2);
  - `age` measured at data collection (§7);
  - CORELS' unconditional "OPTIMAL" header (§6);
  - AIF360's "privileged" encodings (`Female`, `Caucasian`);
  - AIF360 discarding the COMPAS score while reusing the audit filter (§2).
- **C2, minimal abstraction.** The criteria reduce to "which conditional distribution is equalized across groups": P(Ŷ | G) for parity, P(Ŷ | Y, G) for error balance, P(Y | Ŷ or S, G) for calibration and predictive parity. With unequal P(Y | G), only one family can hold exactly (Kleinberg et al.; Chouldechova). Toolkits that expose a flat menu of constraint names (fairlearn's seven) hide this structure. Corbett-Davies et al.'s single-threshold view turns the "exceptions" (group thresholds) into explicit, priced policy choices rather than hiding them in adapters.

### 13. Validation coverage (V1–V4)

Basis: derived from §§1–10.

| Level | What exists | What is missing |
|---|---|---|
| V1 specification adequacy and non-vacuity | label validity studied (Fogliato et al.); conflicting fairness specifications formalized (§4); this report found one vacuous documented exclusion (§2) | no mutation-style test of the audit pipeline; no check that each documented filter removes rows; COMPAS's specification itself is not public |
| V2 differential re-implementation | independent re-derivation reproduces the notebook's 7,214-row tables and Flores et al.'s Table 1 exactly; Dressel–Farid reproduce COMPAS's accuracy; Corbett-Davies et al. retrain a risk model with higher AUC | AIF360 and fairlearn not executed here; no independent checker for CORELS optimality |
| V3 concurrency, crash, silicon, physical leakage | known not to apply: the subjects are statistical instruments and single-threaded batch code | — |
| V4 field and human-behaviour validation | the Kentucky natural experiment (Stevenson); the Dane County RCT (Imai et al.); lay-prediction experiments (Dressel–Farid; Lin et al.) testing human mental models of risk, including base-rate neglect | no RCT of COMPAS at sentencing; outcomes observed only for released defendants (selective labels) |

## Boundaries

- **Not examined:**
  - COMPAS's violent-recidivism and failure-to-appear scores, and any COMPAS version or jurisdiction other than Broward 2013–2014.
  - The primary text of Northpointe's 2016 response report; its position is taken from Chouldechova, Dressel–Farid and Flores et al.
  - The Cox models in the notebook, which were not re-run.
  - AIF360 and fairlearn at run time; the 6,167-row AIF360 count is derived, not observed.
  - The PSA's raw-to-scaled conversion tables.
  - Stevenson's regression specifications and confidence intervals.
  - Lin et al.'s supplementary tables S1–S5.
  - Imai et al.'s final (non-preliminary) data.
  - The human-subject experiments, which were not replicated.
  - CORELS' Python and R bindings.
- **Unknown:**
  - Whether certified searches at `-r 0.001` reproduce the uncapped list printed in §6. The certified `-r 0.001` search was not run.
  - Whether the `is_recid` precedence at `truth_tables.py` lines 102–105 was intended.
  - How much the published regression coefficients move if age at screening replaces the `age`/`age_cat` columns.
  - Whether calibration differences at individual deciles, such as decile 3 and decile 10, are statistically significant; no test was run.
- **Known not to apply:**
  - Chouldechova's identity is per threshold; it says nothing about rankings (AUC).
  - Kleinberg et al.'s balance conditions concern mean scores, not thresholded FPR/FNR.
  - Corbett-Davies et al.'s thresholds assume a correctly estimated P(Y | X) and a utility with a constant cost of detention. They do not address label bias (§9).
- **Unsupported:**
  - Fairlearn's `ThresholdOptimizer` cannot impose calibration or predictive parity, and cannot score groups unseen in training.
  - CORELS emits no checkable optimality certificate.
  - The PSA formula may not be reimplemented in software without the foundation's consent.
- **Attractive conclusions the evidence does not establish:**
  - That COMPAS is or is not "racially biased" without naming the criterion.
  - That laypeople generally predict recidivism as well as instruments; this holds only under immediate feedback and balanced base rates.
  - That rule lists or two-feature models dominate COMPAS. The accuracy differences are 1–2 points, with intervals near zero.
  - That mandated pretrial risk assessment by itself reduces detention.
  - That violent rearrest removes label bias.
  - That *Loomis* endorses COMPAS. It permits only "consideration" with cautions.

## Evidence

Evidence was gathered on 2026-11-21 (UTC). All GitHub pins below equaled each repository's `HEAD` when resolved through the GitHub API on that date.

- **`propublica/compas-analysis` at `bafff5da3f2e45eca6c2d5055faad269defd135a`** (commit date 2017-06-13):
  - `truth_tables.py`: lines 41–50 (lifetime, recidivist), 102–105 (`valid`), 109 (`compas_felony`), 192–195 (degree recoding), 214–216 (population);
  - `Compas Analysis.ipynb`: cell 3 (filter rationale, raw JSON line 65), cell 4 (filters, raw JSON line 93), cells 70–84 (truth tables), cell 73 (follow-up sd);
  - `compas-scores-two-years.csv` (SHA-256 `c451db85908b2f7fef1d83203bedf6b71ecda0d5af468d82ae62178f91d0cc7d`) and `cox-parsed.csv` (SHA-256 `6bf532b103cba89d0f0d870e9b240fe613044da095d840a24bf0326861fdb26a`).
- **`Trusted-AI/AIF360` at `34877916b789e569edf5c0aac033403ca90f34b3`:** `aif360/datasets/compas_dataset.py` lines 8–42; `aif360/datasets/standard_dataset.py` lines 83–102.
- **`fairlearn/fairlearn` at `34e44252a292159eecb67d94f6ef7f391d69c8bd`:** `fairlearn/metrics/_fairness_metrics.py` lines 118–188 and 259–270; `fairlearn/postprocessing/_threshold_optimizer.py` lines 64–112 and 361; `fairlearn/postprocessing/_constants.py` lines 14–17.
- **`corels/corels` at `c54cba53b5f6c62472bef508c68c565367ba474c`:**
  - `src/corels.cpp` lines 76, 79, 108–112, 247–253; `src/run.cpp` lines 131–133, 140–169; `src/utils.cpp` line 134; `src/main.cc` line 29 (default `max_num_nodes = 100000`);
  - `processing/compas.py` lines 11–37, 83; README "Example rule list"; `data/compas_train.*`.
- **Literature.** DOIs were verified against Crossref metadata on 2026-11-21. Kleinberg et al. (`10.4230/LIPIcs.ITCS.2017.43`) was verified against DataCite (LIPIcs vol. 67, 43:1–43:23). arXiv identifiers were verified on arxiv.org.
  - Brennan et al. 2009 (`10.1177/0093854808326545`), CJB 36(1):21–40; abstract via Crossref.
  - Chouldechova 2017 (`10.1089/big.2016.0047`; arXiv 1703.00056): eq. (2.6), Definitions 1–4, §1.2 sample of n = 6,150.
  - Kleinberg et al. 2017 (arXiv 1609.05807).
  - Corbett-Davies et al. 2017 (`10.1145/3097983.3098095`; arXiv 1701.08230): Table 1 and §4.
  - Angelino et al. KDD 2017 (`10.1145/3097983.3098047`) and JMLR 18(234) 2018 (arXiv 1704.01701): Figure 1, Table 2, §6.4.
  - Dressel & Farid 2018 (`10.1126/sciadv.aao5580`): Tables 1–2 and Methods; full text read via PMC5777393.
  - Lin et al. 2020 (`10.1126/sciadv.aaz0652`): Results and Methods; full text read via PMC7021503.
  - Rudin et al. 2020 (`10.1162/99608f92.6ed64b30`): abstract and §2; author-hosted final PDF.
  - DeMichele et al. 2018 (`10.2139/ssrn.3168452`): abstract and pp. 31–32; a state-court-hosted copy of the April 2018 version.
  - Stevenson (`10.2139/ssrn.3016088`; 103 Minn. L. Rev. 303): Introduction pp. 308–310.
  - Imai et al. 2023 (`10.1093/jrsssa/qnad010`; arXiv 2012.02845): abstract and §2.
  - Fogliato et al. 2021 (`10.1145/3461702.3462538`; arXiv 2105.04953): §5, §8, §9.
  - Flores et al. 2016, Federal Probation 80(2):38–46 (no DOI; uscourts.gov PDF): methods and Tables 1–2.
  - Larson et al. 2016 (ProPublica methodology page).
  - PSA Risk Factors and Formula (Arnold Foundation sheet, copy hosted by the Utah courts).
  - *State v. Loomis*, 2016 WI 68, 371 Wis. 2d 235, 881 N.W.2d 749: ¶¶98–101, 104, 123; Justia slip-opinion text.
- **Execution:**
  - `support/compas_probe.py` (stdlib only) with full output in `support/compas_probe_output.txt`;
  - CORELS runs, including the two 50,000,000-node runs, in `support/corels_runs.txt`.
  - Bootstrap seed 7 and CV shuffle seed 20261121 are fixed in the script.

## Revalidation

1. **Audit numbers (about 15 s).** Fetch the CSV at the pinned revision (command in the probe docstring) and run `python3 support/compas_probe.py /tmp/compas-scores-two-years.csv`.
   - Check the printed SHA-256, then `cohort filtered: n=6172` and `cohort unfiltered: n=7214`.
   - Check the Black/White FPR of `0.4234`/`0.2201` (6,172) and `0.4485`/`0.2345` (7,214).
   - Check that the identity column equals FPR, and the age-offset histogram `{1: 336, 2: 2743, 3: 3845, 4: 290}`.
   - A different SHA-256 means the subject changed; re-run everything.
2. **Vacuous filter.** At a new revision, inspect `truth_tables.py` around `write_two_year_file`. If the `F`/`M` recoding remains, `c_charge_degree != "O"` stays vacuous. Confirm with `cut -d, -f23 compas-scores-two-years.csv | sort | uniq -c`; column 23 is `c_charge_degree` in this header.
3. **Toolkits.**
   - AIF360: `grep -n "c_charge_degree != 'O'" aif360/datasets/compas_dataset.py` and check `features_to_keep`.
   - fairlearn: check `SIMPLE_CONSTRAINTS` and `ALL_CONSTRAINTS` in `_threshold_optimizer.py` for any added calibration constraint, and `equalized_odds_difference` for the `worst_case` aggregation.
4. **CORELS labelling.** Build with `make NGMP=1 corels` and run `./corels -r 0.005 -c 2 -p 1 ../data/compas_train.out ../data/compas_train.label ../data/compas_train.minor`. If the output says "max number of nodes" and still prints "OPTIMAL RULE LIST", the labelling behaviour persists. Also check `src/utils.cpp` near `print_final_rulelist` for a certification guard.
5. **Literature claims.** No cheap probe exists. Re-read the cited tables: Chouldechova eq. (2.6); Corbett-Davies Table 1; Dressel–Farid Tables 1–2; Lin et al. Results; DeMichele pp. 31–32; Stevenson pp. 308–310; Fogliato §5; *Loomis* ¶¶98–100. Any new PSA validation or COMPAS re-norming is a new subject and needs its own report.
