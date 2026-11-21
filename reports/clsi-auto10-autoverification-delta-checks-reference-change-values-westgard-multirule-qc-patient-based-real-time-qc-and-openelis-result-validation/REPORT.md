# Laboratory result autoverification, delta checks and reference change values, multirule and patient-based quality control, and how two open laboratory systems evaluate limits and QC status

## Summary

- **Where the error-detection rules act.** In the total testing process, most reported errors are pre-analytical (46–68.2% of errors) or post-analytical (18.5–47%), not analytical.
  - Delta checks mainly target pre-analytical specimen misidentification.
  - Statistical QC targets analytical error.
  - Autoverification is the post-analytical gate that decides whether a result reaches a clinician unreviewed.
  - One academic core laboratory reported autoverifying 99.5% of chemistry results after 13 years of rule development.

  (Basis: documentation)
- **OpenELIS Global 2's release gate is one explicit conjunction.** At the pinned commit it reads `isClear = rangeKnown ∧ inRange ∧ qc≠FAIL ∧ ¬nceOpen ∧ ¬modified ∧ ¬critical ∧ ¬nonconforming ∧ ¬ackPending` (`ValidationSignals`).
  - **Holds:** unparseable, censored (`<0.5`), non-finite and unauthored-range values (execution).
  - **Releases without QC:** a missing QC evaluation (`UNKNOWN`) "neither clears nor blocks", so a result with no QC evaluation can be released automatically.
  - **Releases below the range:** with only an upper normal bound and no valid range, `-5` is NORMAL and clear. (Basis: source + execution)
- **The OpenELIS Westgard evaluators have three fail-open paths and one false-alarm path** (execution of the unmodified classes):
  - **SD zero or null.** `calculateZScore` returns z = 0. 1₃ₛ, 2₂ₛ, R₄ₛ and 4₁ₛ then never fire, but 10ₓ fires "below side of mean", because `isPositiveSide(0)` is false.
  - **Unconfigured or failing evaluation.** No enabled rule, no statistics, or an exception during evaluation all yield no rejection.
  - **Non-standard R₄ₛ.** R₄ₛ is implemented as `|z_t − z_(t−1)| ≥ 4` across consecutive results of a control lot. The published rule is within-run only and requires one control above +2s and another below −2s. The upstream unit tests assert this non-standard form.
  - **Default does not block.** A site flag making open QC failures block release defaults to `false`.
- **Rolling QC statistics absorb a persistent shift.** In OpenELIS's rolling mode, statistics are recomputed over the last 20 results with no exclusion of rejected ones. In a toy model of that rule, a persistent +1 SD shift was detected within 40 runs 58% of the time with rolling statistics versus 94% with fixed statistics. Undetected series' z-scores decayed to about 0. (Basis: execution, toy model of the algorithm, not OpenELIS itself)
- **SENAITE treats unknowable results as in range.** `is_out_of_range` returns "in range" for empty results, non-floatable non-list results, and analyses without a range. (Basis: source)
- **Delta-check performance depends on individuality and prevalence.** The reference change value is `RCV = √2 · Z · √(CV_A² + CV_I²)`, and a log-normal form gives asymmetric up and down limits. Delta checks perform best for analytes with a low index of individuality (CV_I/CV_G). Their positive predictive value for mix-ups is low at realistic prevalence. A toy model reproduces both effects (sensitivity 0.67 vs 0.15 at II 0.2 vs 1.0; PPV 0.013 at 0.1% prevalence). Published simulations on historical data found extremely low yields for some routinely used thresholds, and the performance did not transfer between two patient populations. (Basis: documentation + execution, toy model)

## Applicability

- **OpenELIS Global 2.** Repository `DIGI-UW/OpenELIS-Global-2` @ `2865b4cfec53a0334d3f5a33e14e350e8ee64e55`. This is the default-branch head on 2026-11-21, committed 2026-11-21T02:09:32Z. The repository was transferred by its owners, so the project's older name may appear in other references.
  - **Examined by source:** `resultvalidation/` (`ValidationSignals`, `ResultsValidationUtility`, `ResultValidationServiceImpl`), `resultlimit/` and `resultlimits/` (`ResultLimitServiceImpl`, `ResultLimit`), `qc/` (evaluators, `WestgardRuleEvaluationServiceImpl`, `QCResultServiceImpl`, calculators, `QcHoldServiceImpl`) and one Liquibase changelog.
  - **Executed:** eleven classes compiled unmodified: the evaluators, `RuleEvaluationResult`, `ValidationSignals` and `ResultLimit`.
  - **Stubs used for execution:** Spring's `@Component` annotation, three QC value holders reduced to their getters, commons-validator `GenericValidator` (stated semantics), the `ResultType` enum, and data-holder classes that the executed methods do not use.
  - **Not executed:** services, persistence and the user interface.
- **SENAITE.** Repository `senaite/senaite.core` @ `4ba33292398c337a47c058a51a99799494829648` (setup version 2.7.0). Examined by source only: `src/bika/lims/api/analysis.py` and `src/bika/lims/api/__init__.py`. The files under `src/senaite/core/validators/` are `formula.py`, `interimfields.py` and `imports.py`. Only `formula.py` was read; it validates calculation formulas and interim fields, which are configuration, not results.
- **Professional guidance.** The CLSI documents AUTO10 (*Autoverification of Clinical Laboratory Test Results*, 1st ed., 2006 as AUTO10-A), AUTO15 (*… for Specific Disciplines*, 1st ed., 2019), EP33 (*Use of Delta Checks in the Medical Laboratory*, 1st ed., 2016) and C24 (4th ed., 2016), and ISO 15189, are **not examined**. Their content was not available. Editions are taken from CLSI and ANSI catalogue listings.
- **Toy models.** All simulation numbers come from toy models with synthetic parameters in `support/lab_qc_sim.py`. They characterise rule definitions, not any laboratory or analyser.
- **Not clinical guidance.** This report is not guidance for clinical decisions.

## Findings

### 1. Where each rule family acts

| Phase | Reported share of errors | Rule family that can act | Evidence |
| --- | --- | --- | --- |
| Pre-analytical (order, patient ID, collection) | 68.2% (1997 stat-lab study); 46–68.2% (2006 review) | Delta checks (misidentified specimens); specimen-integrity rules (interference indices); "absurd value" rules | Plebani & Carraro 1997: 40,490 analyses, 189 mistakes (0.47%); 74% without effect on outcome, 6.4% associated with inappropriate care. Plebani 2006 review. |
| Analytical | 13.3% (1997) | Statistical QC on control materials (Westgard multirule); patient-based real-time QC (moving averages); instrument flags; measuring-range checks | Plebani 2006: analytical errors much reduced, but immunoassay interference remains serious |
| Post-analytical | 18.5% (1997); 18.5–47% (2006) | Autoverification gate, critical-value notification, reporting | Carraro & Plebani 2007: 51,746 analyses, 160 confirmed errors (3092 ppm), significantly lower than 1996; pre- and post-analytical phases still had the highest prevalences |

Ladenson (1975) introduced the computer "delta check" that compares a patient's result with their previous one. Over 22 months in a 1200-bed hospital it found specimen misidentification to be "a serious problem" that other QC did not detect. (Basis: documentation, abstracts)

### 2. Autoverification rule types and how each behaves when it cannot be evaluated

Krasowski et al. (2014) built rules first in the LIS and then mostly in middleware. The rules used instrument error flags, interference indices, analytical measurement ranges, delta checks, dilution protocols, results suggesting compromised or contaminated specimens, and absurd values. Examples of absurd values were albumin above total protein, and bilirubin discordant with the icteric index (IgM paraprotein interference). Over 13 years the autoverification rate rose from 40% to 99.5%, and "a high percentage of critical values now autoverify". The lowest rates were for some drug levels and free light chains, which need offline dilution. (Basis: documentation, abstract)

The table below states what each rule input does in OpenELIS when the input is absent or indeterminate. For each input it says whether the gate holds or releases.

| Rule input | OpenELIS representation | If missing / unparseable | Basis |
| --- | --- | --- | --- |
| Reference range | `ResultLimit` selected for patient sex, age (days) and specimen | Synthetic empty limit (`id` null): flag `null`, **hold** | source + execution |
| Numeric value | `Double.parseDouble(normalizeScientificNotation(v.trim()))` | `<0.5`, `>20`, `NaN`, `Infinity`, `4,0`, empty: flag `null`, **hold** | execution |
| Valid (absurd-value) range | `lowValid`/`highValid`, default ±∞ | Unauthored: no INVALID check, so a value below an upper-only normal range is **released** (`-5` is NORMAL and clear) | execution |
| Critical limits | `lowCritical`/`highCritical`; ±∞ means "not authored" | Unauthored: never critical. Censored `<0.5` below a critical low of 2.5 is not flagged critical, but is held as unparseable. | execution |
| QC status | PASS / FAIL / UNKNOWN per analysis | `UNKNOWN` (no evaluation): **neither blocks nor clears**, so release is possible | source + execution |
| Non-conformity event status | `isNceOpen(status)` | null or blank: open, **hold**. Comparison is case-sensitive, so `"closed"` counts as open, **hold**. | execution |
| Modified after first save | `isModified(revision)` | Unparseable revision: not modified, so **release** is possible | execution |
| Stale page token | `isStale(token, lastupdated)` | Missing token: not stale (legacy client, **proceeds**). Unparseable token: stale, **blocks**. | execution |
| QC hold lookup | `analysisIdsBlockedFromRelease` | Exception: withhold the whole batch, **hold** | source |

The stated design rule is to read every indeterminate input "as risk present, never as clearance", except QC that does not exist. In fact the code holds on range, value, non-conformity event and lookup failures, but releases on an unparseable revision and on an unauthored valid range. (Basis: source + execution)

### 3. The OpenELIS clearance rule, quoted

`src/main/java/org/openelisglobal/resultvalidation/util/ValidationSignals.java`:
- **Lines 251–255:**
  ```
  public static boolean isClear(boolean rangeKnown, boolean inRange, String qcStatus, boolean nceOpen,
          boolean modified, boolean critical, boolean nonconforming, boolean ackPending) {
      return rangeKnown && inRange && !QC_FAIL.equals(qcStatus) && !nceOpen && !modified && !critical
              && !nonconforming && !ackPending;
  ```
- **Lines 280–296 (`isClearAtEntry`):** for numeric results, `rangeKnown = Double.isFinite(limit.getLowNormal()) || Double.isFinite(limit.getHighNormal())`, so one finite bound is enough. `inRange = FLAG_NORMAL.equals(resultFlag(...))`, and `ackPending` is passed as `false`.
- **Lines 121–144 (`resultFlag`):** the precedence is INVALID (outside the valid range), then CRITICAL, then ABNORMAL (outside the normal range), then NORMAL. A null id, a non-numeric type, a blank value, a parse failure or a non-finite value returns `null`.
- **Lines 82–89 (`isCritical`):** a bound counts only when `Double.isFinite`. The `ResultLimit` defaults (`ResultLimit.java:13–22`) are `lowCritical = Double.POSITIVE_INFINITY`, `highCritical = Double.POSITIVE_INFINITY`, and `lowNormal`/`lowValid`/`lowReportingRange = Double.NEGATIVE_INFINITY` with matching `POSITIVE_INFINITY` highs.

**Two code paths compute "critical" differently.** The validation queue sets the row's critical flag with `ValidationSignals.isCritical(resultLimit, result)` (`ResultsValidationUtility.java:715`). That overload parses `value.trim()` without normalising scientific notation (`ValidationSignals.java:91–104`), whereas `resultFlag` normalises. Executed results:
- `7×10⁰` gets `resultFlag` CRITICAL but `isCritical(Result)` false.
- `Infinity` gets `resultFlag` null but `isCritical(Result)` true.

Neither case is cleared, but the critical signal shown to a reviewer can disagree with the flag. (Basis: source + execution, `support/oe_probe.out`)

| Value (normal 3.5–5.1, critical < 2.5 or > 6.5, valid 0–20) | `resultFlag` | `isCritical(Result)` | Clear at entry (QC UNKNOWN) |
| --- | --- | --- | --- |
| `4.0`, ` 4.0 `, `5×10⁰` | NORMAL | false | **true** |
| `5.5` | ABNORMAL | false | false |
| `7.0`, `7e0` | CRITICAL | true | false |
| `7×10⁰` | CRITICAL | **false** | false |
| `25`, `-1` | INVALID | true | false |
| `<0.5`, `>20`, `NaN`, `4,0`, empty | null | false | false |
| `Infinity` | null | **true** | false |
| `4.0` with QC FAIL / QC PASS | NORMAL | false | false / true |

**QC failures and release.**
- **Acknowledgement before release.** `ResultValidationServiceImpl.enforceQcAcknowledgment` (lines 265–321) throws when any analysis in the sample batch has a result with `QcEvaluation.FAIL` and no acknowledgment record. A sibling whose id does not parse as an integer is skipped (`catch (NumberFormatException e) { continue; }`, line 307).
- **Blocking is a site option, off by default.** `QcHoldServiceImpl.blocksRelease()` (lines 79–82) reads the site property `qcFailBlocksValidation`. Liquibase changeset `qc-026-qc-fail-hold-flag` (`src/main/resources/liquibase/qc/010-manual-rdt-qc.xml:179–200`) inserts it with `<column name="value" value="false"/>` (line 193). By default an open QC failure therefore requires acknowledgment rather than blocking release. Run-level holds through `runQcService` still apply, but that service was not examined.
- **Batch QC status.** `qcStatusFor` (`ResultsValidationUtility.java:977–992`) returns FAIL if any result failed, PASS only if all passed, and otherwise UNKNOWN.

(Basis: source)

### 4. Reference-range selection with missing demographics (OpenELIS)

`ResultLimitServiceImpl.selectForPatientWithReason` (lines 286–307) selects as follows:
- **Sex or birth date missing.** It uses only a range that does not depend on the missing value, "never a range borrowed from one sex or one age band". If none exists, it returns an empty `ResultLimit` with a `RangeNotAppliedReason`. This avoids silently applying the wrong sex's range, and the result then cannot clear.
- **Specimen-scoped ranges** take precedence over shared ones (lines 245–272).
- **Age bands** are compared in days and are inclusive at both ends (`getCurrPatientAge(patient) >= limit.getMinAge() && getCurrPatientAge(patient) <= limit.getMaxAge()`, line 441). Where bands touch, the first band in list order wins.

(Basis: source) Upstream integration tests cover missing sex and age (`ResultLimitMissingSexAgeIntegrationTest`); they were not run.

### 5. Statistical QC: the published multirule versus the OpenELIS evaluators

**Published rules.** As stated by Westgard QC, the multirule of Westgard, Barry, Hunt and Groth (1981) is:
- **1₂ₛ** is a *warning* that triggers inspection by the rejection rules in the classic procedure.
- **1₃ₛ:** reject on one control beyond the mean ± 3s.
- **2₂ₛ:** two consecutive control measurements beyond the same +2s limit, or beyond the same −2s limit.
- **R₄ₛ:** one control in a group above +2s and another below −2s, "interpreted within-run, not between-run".
- **4₁ₛ:** four consecutive controls beyond the same 1s limit (across runs or materials).
- **10ₓ:** ten consecutive controls on one side of the mean.
- In the "modern" variant, 1₂ₛ gating is dropped.
- With 2s limits and N = 2, about 9% of good runs are falsely rejected; with 3s limits, about 1%.

(Basis: documentation. The 1981 paper's full text was not examined; its metadata was verified.)

**OpenELIS evaluators** (`src/main/java/org/openelisglobal/qc/service/evaluator/`):

| Rule (code string) | Severity | Test as implemented | Difference from published rule |
| --- | --- | --- | --- |
| 1₂ₛ (`"1₂ₛ"`) | WARNING | `\|z\| ≥ 2` | Used as a warning but does not gate other rules |
| 1₃ₛ | REJECTION | `\|z\| ≥ 3` (`exceedsThreshold`: `zScore.abs().compareTo(threshold) >= 0`, base class lines 69–71) | `≥` instead of "exceeds" (boundary only) |
| 2₂ₛ | REJECTION | current and previous result of the **same lot**, `\|z\| ≥ 2`, same side | No within-run, across-level form |
| R₄ₛ | REJECTION | `currentZScore.subtract(previousZScore).abs()` `≥ 4` (`RuleR_4sEvaluator.java:57–60`), previous result of the same lot | Across runs instead of within; range form instead of "one above +2s and one below −2s" |
| 4₁ₛ | REJECTION | last 4 of the lot, `\|z\| ≥ 1`, same side | Same lot only |
| 10ₓ | REJECTION | last 10 of the lot on the current result's side; side = `zScore.compareTo(ZERO) > 0` (base lines 79–81) | z = 0 is counted as "below" |
| 3₁ₛ, 7ₜ (trend) | WARNING | additional rules | Not part of the 1981 procedure |

Base class `AbstractWestgardRuleEvaluator.java:29–34`:
```
protected BigDecimal calculateZScore(BigDecimal value, BigDecimal mean, BigDecimal stdDev) {
    if (stdDev == null || stdDev.compareTo(BigDecimal.ZERO) == 0) {
        return BigDecimal.ZERO;
    }
```
The persisted z-score uses the same convention: `QCResultServiceImpl.computeZScore`, lines 353–359, documented as "returning zero rather than dividing by a zero SD". `getZScore` prefers a stored z over recomputation (lines 43–48).

**Executed results** (`support/oe_probe.out`; mean 100, SD 2 unless stated):

| Case | Result |
| --- | --- |
| 1₃ₛ at z = +3.00 / +2.99 | violation / none |
| 1₃ₛ, value 200, SD = 0 or SD = null | **none** |
| 10ₓ, current 50, nine history values 300, SD = 0 | **violation "below side of mean"** |
| 10ₓ, current at the mean, nine values below / above | violation / none |
| R₄ₛ, previous z = +3.0, current z = −1.0 | **violation** (the published form would not reject: −1.0 is not beyond −2s) |
| R₄ₛ, +2.1 then −2.1 | violation |
| 2₂ₛ with empty history / null statistics | `evaluated=false`, not violated |
| 1₃ₛ, stored z = 0.5, value 200 | none (stored z wins) |
| `canEvaluate` with config code `"1-3s"` / `"1₃ₛ"` | false / true |

**Service layer.** `WestgardRuleEvaluationServiceImpl.java`:
- **No enabled rules** (lines 77–83) or **no statistics** (86–91): return an empty list.
- **Exceptions** (105–109): become `cannotEvaluate`.
- **Rejection test** (`hasRejectionViolation`, 126–128): requires `isViolated() && "REJECTION"`.
- **Unmatched codes:** a configured rule whose code does not exactly equal an evaluator's Unicode code is silently skipped (`findEvaluator`, 133–135; `canEvaluate`, base line 18).
- **History** is the latest 15 results of the control lot excluding the current one, ordered by run time (140–146). It is not restricted to results that precede the current one.
- **When evaluation runs:** only for lots in `ACTIVE` status with a non-null z (`QCResultServiceImpl.java:341–345`). Lots in establishment are never evaluated.

**Specification adequacy of the upstream tests.** `RuleR_4sEvaluatorTest.java:142–151` asserts the non-standard form. Under the comment "Both on same side but far apart - can still violate", previous z = +4.0 and current z = 0 must violate. The tests check the code against its own specification, not against the published rule. (Basis: source + execution)

### 6. Toy-model rule performance

All results here come from a toy model with z ~ N(SE, 1) and two control levels per run (`support/lab_qc_sim.out`, seed 20261121).

| Procedure | P(reject first run), SE = 0 / 1 / 2 / 3 | Mean run length, SE = 0 (capped at 200) / 1 / 2 |
| --- | --- | --- |
| 1₃ₛ | 0.0053 / 0.045 / 0.290 / 0.759 | 118.3 / 22.1 / 3.35 |
| 1₂ₛ | 0.0880 / 0.303 / 0.749 / 0.973 | 10.8 / 3.42 / 1.29 |
| Multirule, 1₂ₛ-gated (classic) | 0.0070 / 0.069 / 0.413 / 0.875 | 100.7 / 9.97 / 2.13 |
| Multirule, ungated | 0.0088 / 0.078 / 0.418 / 0.871 | 83.8 / 6.99 / 1.98 |
| OpenELIS-style rule forms (per lot, `≥`, R₄ₛ range across runs) | 0.0227 / 0.083 / 0.369 / 0.779 | 56.2 / 6.99 / 2.14 |

**Validation of the simulator against analytic values.**
- P(1₂ₛ, N = 2) = 0.0889 analytically versus 0.0880 simulated.
- P(1₃ₛ) = 0.0054 versus 0.0053.
- These match the ~9% and ~1% figures quoted by Westgard QC.

**Analytic R₄ₛ for an independent standard-normal pair.**
- Published form `P(z₁ > 2 ∧ z₂ < −2) + P(z₁ < −2 ∧ z₂ > 2) = 2·(1 − Φ(2))² = 0.00104`.
- Range form `P(|z₁ − z₂| ≥ 4) = 2·(1 − Φ(4/√2)) = 0.00468`, which is 4.5× higher.

**Approximate decomposition of the in-control rate of the OpenELIS-style forms.** Each rule runs once per lot and there are two lots:
- 1₃ₛ: 0.0054;
- R₄ₛ: 2 × 0.00468 = 0.0094;
- 2₂ₛ: 2 × 2·0.02275² = 0.0021;
- 4₁ₛ: 2 × 2·0.1587⁴ = 0.0025;
- 10ₓ: 2 × 2·0.5¹⁰ = 0.0039.

The sum is about 0.023, against 0.0227 simulated. The range-form R₄ₛ is the largest single contributor. (Basis: derived)

**Rolling-window absorption** (toy model of `RollingCalculator`).
- **The upstream rule.** Window `initialRunsCount`, default 20 (`RollingCalculator.java:18,28–29`). `recalculateRollingStatistics` runs after each insert into a `ROLLING` lot (`QCResultServiceImpl.java:156–160`), over every result of the lot with no status filter.
- **Setup.** The toy uses one series and freezes or rolls the mean and SD. The z-score of each result uses the statistics in force before it.

| Persistent shift | Statistics | P(detected by run 5) | by run 10 | by run 40 | mean z, runs 26–30, if undetected |
| --- | --- | --- | --- | --- | --- |
| 0 | fixed | 0.058 | 0.114 | 0.351 | +0.01 |
| 0 | rolling | 0.047 | 0.101 | 0.418 | +0.02 |
| +1 SD | fixed | 0.274 | 0.549 | 0.940 | +0.69 |
| +1 SD | rolling | 0.223 | 0.359 | **0.584** | **+0.03** |
| +1.5 SD | fixed | 0.579 | 0.865 | 0.998 | +0.87 |
| +1.5 SD | rolling | 0.446 | 0.646 | 0.784 | +0.07 |
| +2 SD | fixed | 0.818 | 0.985 | 1.000 | n/a |
| +2 SD | rolling | 0.695 | 0.865 | 0.917 | +0.06 |

The cumulative false-rejection probability at SE = 0 over 40 runs (0.35–0.42) reflects per-run evaluation of ≥-threshold rules. It is not a deployed figure. (Basis: execution, toy model)

### 7. Delta checks and reference change values

- **The RCV formula.** Fraser (2012) gives `RCV = 2^½ · Z · (CV_A² + CV_I²)^½`. Here CV_A is analytical imprecision, CV_I is within-subject biological variation (described as generally constant over time, geography, method, health and stable chronic disease), and Z is chosen to match the intended probability statement.
  - A log-normal transformation gives unidirectional, asymmetric RCVs.
  - RCVs can drive delta checks and autoverification in LIMS.
  - Example with CV_A = 2% and CV_I = 5%: symmetric RCV 14.93% at Z = 1.96; log-normal +16.09% / −13.86%; at Z = 2.58, 19.65% and +21.70% / −17.83%.

  (Basis: documentation + derived)
- **Calculation modes.** Randell & Yenice (2019) describe absolute change, percentage change and rate of change. The yield of identified errors is usually small compared with the number of alerts. Analytes with low indices of individuality perform better. Multivariate approaches look more useful but are hard to deploy in LIS and middleware. Clinically meaningful uses include acute kidney injury (creatinine), rapid sodium changes and high-sensitivity troponin. (Basis: documentation)
- **Simulation on historical data.** Strathmann et al. (2011) sampled specimen pairs from the same patient or from different patients. Mean corpuscular volume had the highest PPV for mislabelling. Several thresholds in use, notably for potassium and the anion gap, had predicted yields that were "extremely low". Rule performance was inconsistent between two inpatient populations, so rules may not generalise across institutions. (Basis: documentation)
- **Toy model.** Set points are lognormal with CV_G, results add N(0, √(CV_I² + CV_A²)), and a mix-up takes the second result from a different patient. Here n = 200,000 pairs:

| II = CV_I/CV_G | Z | False flags (same patient) | Mix-up sensitivity | PPV at 0.1% / 1% mix-up prevalence | Detection of a 10% / 20% analytical shift |
| --- | --- | --- | --- | --- | --- |
| 0.2 | 1.96 | 0.052 | 0.673 | 0.013 / 0.116 | 0.28 / 0.71 |
| 0.2 | 3.29 | 0.0018 | 0.474 | 0.206 / 0.724 | 0.05 / 0.29 |
| 0.5 | 1.96 | 0.052 | 0.350 | 0.007 / 0.063 | 0.28 / 0.71 |
| 1.0 | 1.96 | 0.052 | 0.150 | 0.003 / 0.028 | 0.28 / 0.71 |
| 1.0 | 3.29 | 0.0020 | 0.019 | 0.009 / 0.088 | 0.05 / 0.29 |

  The false-flag rate depends only on Z, because RCV is calibrated to within-person noise. Mix-up sensitivity depends on II. Shift detection does not depend on II. (Basis: execution, toy model; PPV derived by Bayes' rule from the simulated rates)
- **Neither open system examined has a delta check in the code inspected.** No file in the OpenELIS main source tree has a name referring to delta checks. A GitHub code search for `delta` in the repository's Java sources (default-branch index at observation) returned 17 files, none in a result-validation, result-limit or QC main-source package. SENAITE's `is_out_of_range` has no patient-history input. Other SENAITE packages were **not examined**. (Basis: source, scoped)

### 8. Patient-based real-time QC

- **Components and optimisation.** Badrick et al. (2019) define the components of patient-based real-time QC as the calculation algorithm, block size, truncation limits and control limits. They call for optimisation with each laboratory's own patient data, so that systematic errors are detected reliably with few false alarms. They restrict the term to population parameters such as moving means and medians; delta checks are within-patient. (Basis: documentation)
- **Validation tools.** van Rossum & Kemperman (2017) introduced bias detection curves, which plot the median number of results needed for detection against the introduced bias. They also introduced moving-average validation charts (minimum, median and maximum), demonstrated for sodium, potassium and albumin. (Basis: documentation)
- **Toy bias detection curve.** The synthetic sodium-like stream mixes 90% N(140, 2.5) with 10% N(133, 6). Results are truncated to 130–150 and averaged with a simple moving average. Limits are calibrated to about 1 false alarm per 10,000 results. The table gives the median and 95th percentile of patient results to detection, censored at 6000.

| Block N | bias 0.5 | bias 1.0 | bias 2.0 | bias 3.0 |
| --- | --- | --- | --- | --- |
| 20 | median censored (≥ 6000) | 569 / 2067 | 41 / 137 | 21 / 43 |
| 50 | 5448 / censored | 335 / 1282 | 52 / 92 | 51 / 53 |
| 100 | 1576 / censored | 150 / 479 | 102 / 105 | 102 / 104 |

  Larger blocks detect small biases sooner but cannot detect anything in fewer than N results. This trade-off is what bias detection curves expose. (Basis: execution, toy model)
- **Open systems.** No moving-average or patient-based QC evaluator was found in the examined OpenELIS packages; this is **not examined** elsewhere.

### 9. SENAITE result-range semantics

`src/bika/lims/api/analysis.py`, `is_out_of_range(brain_or_object, result)`, returns `(out_of_range, out_of_shoulders)`:
- **Empty result** (lines 65–67): `if result in [None, '']: return False, False`.
- **Non-floatable, non-JSON-list result** (93–98): `(False, False)`, commented "There is no chance to know if the result is out-of-range". Multi-select results (100–114) are out of range only if no numeric sub-result is in range.
- **No range** (127–130): `(False, False)`. Registered `IResultOutOfRange` adapters can override (133–142).
- **Missing bounds** (146–149): `specs_min = api.to_float(result_range.min, result)`, and likewise max. A missing or non-numeric bound defaults to the result itself, so that side is "in range".
- **Operators** (151–163): `geq`/`leq` give inclusive bounds; anything else is exclusive.
- **Shoulders** (169–175): bounds `warn_min`/`warn_max` default to the specification bounds.

`api.is_floatable` (`api/__init__.py:2051–2062`) is `float(value)` within a `try`. Python's `float` accepts `"nan"` and `"inf"`, so a `"nan"` result reaches the comparisons. Every comparison with NaN is false, so that result is out of range and out of shoulders (derived from Python semantics; not executed). The module imports `Mapping` from `collections`, which Python 3.10 removed, so it was not executed under the probe interpreter. (Basis: source + derived)

**Contrast with OpenELIS.** SENAITE treats "unknowable" as in range (no flag). OpenELIS treats it as not clear (hold) for release purposes. These are different questions, flagging versus releasing. A system that reuses a flagging predicate as a release gate inherits a fail-open default. (Basis: derived)

### 10. Performance and resource footprint

| Level | Measurement | Value | Basis |
| --- | --- | --- | --- |
| L1 authoring | Size of rule code | OpenELIS: eight rule-evaluator classes of 62–96 lines each plus a 94-line abstract base; `ValidationSignals` 359 lines; `ResultLimitServiceImpl` 888. SENAITE `api/analysis.py` 470. Person-time and LLM-token cost: **not measured**. | measured (`wc -l`) |
| L2 build | Full OpenELIS or SENAITE build | **not measured**. Probe: fetch and compile 11 upstream classes plus stubs and run, 2.73 s wall, 121 MB RSS (OpenJDK 27.0.1). | measured |
| L3 latency | Rule evaluation latency in a running LIS | **not measured** | — |
| L4 execution | Evaluator or `resultFlag` throughput | **not measured**. Toy simulations: 22.9 s wall in total, 63.5 MB RSS (Python 3.13, numpy 2.3.5). | measured (toy only) |
| L5 verification | Upstream test-suite runtime | **not measured** (tests not run) | — |
| L6 footprint | Repository size | OpenELIS tree 14,561 files; SENAITE 4,610 files (GitHub tree API at the pinned commits). Database and runtime memory: **not measured**. | measured |

Host: 96-vCPU Intel Xeon @ 2.60 GHz VM.

### 11. Comprehensibility and model refinement (C1, C2)

**C1, human comprehension.**
- **The clearance rule is legible.** It is one 8-term conjunction stated once and shared by the queue, bulk release and entry-time automation. A reviewer can audit it locally.
- **The failure semantics are not legible.** They are spread across parse helpers, value-holder defaults (±∞ sentinels; `lowCritical` defaults to +∞), service early returns and the z-score convention.
- **Diagnostics.** A QC evaluation that silently returns an empty list (no rules or no statistics) is indistinguishable in `hasRejectionViolation` from "in control". The 10ₓ message "Ten consecutive results on below side of mean" under zero SD names a cause that is false.
- **The R₄ₛ name invites a wrong mental model.** A person who knows the published rule would expect within-run, opposite-side behaviour. (Basis: derived)

**C2, simplicity.** One idea would make the exceptions ordinary: give every check a three-valued result, PASS/FAIL/UNKNOWN, carrying a reason, plus a single declared policy table mapping UNKNOWN to hold or release per check.
- **Zero SD.** The z-score would then be `Optional`, with UNKNOWN for a zero or null SD, instead of 0. That removes both the silent 1₃ₛ pass and the spurious 10ₓ, without moving complexity into callers: they already handle `cannotEvaluate`.
- **Already partly implemented.** OpenELIS already has three-valued QC status and `cannotEvaluate`. The refinement extends the same mechanism to statistics, parse failures, revision tokens and empty rule sets.
- **Rule semantics as data.** R₄ₛ and 2₂ₛ need a "run" concept: a group of control observations from one analytical run, across levels. Without it, within-run rules are approximated by across-run comparisons. Adding a run identifier to QC results would make the published rule definitions expressible directly.
- **SENAITE.** The same three-valued idea applies. Its `(False, False)` for unknowable results conflates "in range" with "cannot judge". (Basis: derived)

### 12. Validation coverage (V1–V4)

- **V1, specification adequacy.**
  - Upstream unit tests exist for the evaluators, result-limit selection and `ValidationSignals` (`ValidationSignalsTest`, 503 lines). They were not run here.
  - The R₄ₛ tests encode the non-standard form, so a mutant restoring the published definition would *fail* the suite. The tests validate the implementation, not the specification.
  - The conformance probe here is a hand-written boundary suite, not mutation testing.
- **V2, differential testing.** The probe compares published and implemented rule forms (§6), analytically and by simulation. Cross-LIS differential testing on shared inputs was **not performed**, because SENAITE was not executed.
- **V3, concurrency and crash.** OpenELIS has an optimistic stale-page guard (`isStale`, lines 317–326) whose missing-token path proceeds. Concurrent validation and crash behaviour were **not examined**.
- **V4, field validation.**
  - Field evidence is literature only: Krasowski's 13-year autoverification experience, Strathmann's historical-data simulations, Ladenson's 22-month delta-check experience and van Rossum's bias detection curves on laboratory data.
  - Laboratory validation of autoverification rules is described in CLSI AUTO10/AUTO15, which were **not examined**.
  - Human-reviewer comprehension studies were **not examined**.

## Boundaries

- **Not examined.**
  - CLSI AUTO10, AUTO15, EP33 and C24, and ISO 15189 (content not available).
  - Westgard 1981 full text (rule definitions taken from the author's site); Westgard & Groth 1979 power-function paper, Hoffmann & Waid 1965 average-of-normals, Harris & Yasaka 1983 RCV, Fokkema 2006 log-normal RCV (metadata verified only).
  - OpenELIS `RunQcService`, `NceSpecimenService`, analyzer import, critical-callback workflow, the frontend, and packages outside those listed.
  - SENAITE workflow guards, auto-verification and self-verification settings, detection-limit operands, and reference-sample QC charts.
  - Running either LIS end to end.
- **Unknown.**
  - Whether deployed OpenELIS sites configure `ROLLING` statistics, enable 10ₓ, or set `qcFailBlocksValidation`.
  - How often zero-SD statistics arise in practice. One route is `MANUFACTURER_FIXED` with SD 0, since only a null mean or SD is rejected (`ManufacturerFixedCalculator.java:26`; `QCControlLotValidator.java:103`); integer-valued controls are another.
- **Known not to apply.**
  - The toy-model rates are not error rates of OpenELIS, SENAITE or any laboratory.
  - The RCV example values are synthetic.
  - The 99.5% autoverification rate is one institution's chemistry laboratory.
- **Unsupported.**
  - OpenELIS's evaluators have no within-run, across-level QC form (no run grouping in the evaluator inputs).
  - SENAITE's `is_out_of_range` cannot judge non-numeric single results.
- **Stronger conclusions not established.**
  - No patient-impacting incident is shown.
  - The zero-SD behaviour requires a statistics record with SD 0 or null to exist for an `ACTIVE` lot. Rolling and initial-run calculators produce SD 0 only for identical values.
  - The default `qcFailBlocksValidation=false` still requires acknowledgment, so "QC failures do not block release" is a statement about blocking, not about review.

## Evidence

**Observation date.** All evidence was gathered on 2026-11-21 (UTC).

**Repositories.** Revisions were resolved through the GitHub API. Files were fetched from `raw.githubusercontent.com` at the pinned SHAs.
- **OpenELIS** (`DIGI-UW/OpenELIS-Global-2` @ `2865b4cfec53a0334d3f5a33e14e350e8ee64e55`), under `src/main/java/org/openelisglobal/`:
  - `qc/service/evaluator/{AbstractWestgardRuleEvaluator,Rule1_2s,Rule1_3s,Rule2_2s,RuleR_4s,Rule4_1s,Rule10_x,Rule3_1s,Rule7_t}Evaluator.java`;
  - `qc/service/{WestgardRuleEvaluationServiceImpl,QCResultServiceImpl,QcHoldServiceImpl,QCControlLotValidator}.java`;
  - `qc/service/calculator/{RollingCalculator,InitialRunsCalculator,ManufacturerFixedCalculator,SampleStatistics}.java`;
  - `resultvalidation/util/{ValidationSignals,ResultsValidationUtility}.java`;
  - `resultvalidation/service/ResultValidationServiceImpl.java`;
  - `resultlimit/service/ResultLimitServiceImpl.java`;
  - `resultlimits/valueholder/ResultLimit.java`;
  - `common/util/{StringUtil,ConfigurationProperties}.java`.

  Also `src/main/resources/liquibase/qc/010-manual-rdt-qc.xml` and `src/test/java/org/openelisglobal/qc/service/evaluator/RuleR_4sEvaluatorTest.java`. SHA-256 values of the 11 executed files are recorded in `support/oe_probe.out`.
- **SENAITE** (`senaite/senaite.core` @ `4ba33292398c337a47c058a51a99799494829648`): `src/bika/lims/api/analysis.py`, `src/bika/lims/api/__init__.py` and `setup.py`.

**Literature.**
- **Crossref:** every DOI in `REPORT.json` was resolved through the Crossref REST API.
- **Europe PMC or PubMed abstracts:** PMIDs 16729864, 21958344, 30632840, 1164795, 27522620, 9267312, 17525103, 21782806, 24843824, 31263035.
- **Metadata only:** the Westgard 1981 abstract was unavailable through the tools used, so its rule definitions come from `https://www.westgard.com/mltirule.htm` (retrieved 2026-11-21).
- **CLSI editions:** from CLSI and ANSI catalogue pages found by web search, not from the documents.

**Execution.** All under `support/`:
- **`oe_java/build_and_run.sh`.** It downloads the 11 upstream classes at the pinned SHA, compiles them with the stubs in `oe_java/stubs/` and `oe_java/Probe.java`, and runs the probe. It needs curl and JDK 17 or later. Output: `oe_probe.out`, from OpenJDK 27.0.1.
- **What the stubs are.** Annotations, data holders and copied helpers only. `StringUtil` contains `getActualNumericValue`, `normalizeScientificNotation`, its helpers and `isNumeric`, copied verbatim from upstream. `GenericValidator.isBlankOrNull` reproduces commons-validator's null-or-blank test.
- **`lab_qc_sim.py`.** Python 3.10+ and numpy, run with `python3 lab_qc_sim.py 20261121`. Output: `lab_qc_sim.out`. These are toy models.

## Revalidation

1. **OpenELIS rules.** Rerun `support/oe_java/build_and_run.sh` after changing `SHA=` to the new commit, and diff against `support/oe_probe.out`. Any change in cases W3–W8, W15, or in the value table rows for `7×10⁰`, `Infinity`, `<0.5` and the upper-only limit is material.
2. **Targeted source diffs.**
   - `AbstractWestgardRuleEvaluator.calculateZScore` and `isPositiveSide`.
   - The comparison line in `RuleR_4sEvaluator`.
   - The early returns in `WestgardRuleEvaluationServiceImpl.evaluateAllRules`.
   - `ValidationSignals.isClear` and `isClearAtEntry`.
   - `RollingCalculator.calculate` (does it filter rejected results?).
   - The `qcFailBlocksValidation` default in the Liquibase changelog.
3. **SENAITE.** Diff `is_out_of_range` lines 62–175 at the new revision.
4. **Literature claims.** Re-read the cited abstracts. For CLSI positions, obtain the current AUTO10/AUTO15/EP33 editions before relying on any statement attributed to them.
5. **Scope of a passing rerun.** It confirms only the probed boundary behaviour. It does not validate clinical performance.
