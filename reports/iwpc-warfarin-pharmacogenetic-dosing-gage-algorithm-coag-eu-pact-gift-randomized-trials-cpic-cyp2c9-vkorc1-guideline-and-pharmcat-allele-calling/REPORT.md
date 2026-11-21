# Pharmacogenetic warfarin dosing: IWPC and Gage equations, COAG/EU-PACT/GIFT trials, CPIC 2017 guidance, and PharmCAT CYP2C9/VKORC1 allele calling

This report describes algorithms, software behaviour, trial results and guideline text. It contains no dosing advice.

## Summary

- **Two equations, two error shapes.** IWPC 2009 fits ordinary least squares to the square root of weekly dose (4,043 derivation, 1,009 validation patients). Gage 2008 fits regression to log daily dose. A reimplementation on 72 synthetic inputs shows that they agree for common genotypes (41.9 versus 42.5 mg/week) but reach a Gage/IWPC ratio of 4.493 where several dose-lowering factors combine. Decade-index age and separate "unknown" genotype categories also shift IWPC outputs.
- **Ancestry.** Both equations explain less dose variance in African-American patients (Gage validation R² 40% versus 55%; Limdi 2015, 29.3% versus 51.4%), and some per-allele effects differ significantly by race (CYP2C9 `*2`: −20.6% versus +3.0%).
- **The trials are not interchangeable.** COAG compared genotype-guided dosing with a clinical algorithm and found no overall PTTR difference, with worse control in Black participants. EU-PACT compared it with fixed loading doses in a 98.5% white population and found +7.0 points. GIFT used 11 days of guidance that included CYP4F2 and found RR 0.73 on a composite driven mainly by INR ≥4.
- **TTR is a family of computations.** In a toy probe, changing the window start, target band, interpolation rule or gap rule shifts per-patient TTR by 1.51 to 16.77 points on average.
- **CPIC 2017** gates pharmacogenetic dosing by ancestry. It adds `*5/*6/*8/*11`, CYP4F2 and `rs12777823` as percentage adjustments after an algorithm that encodes only `*2`, `*3` and VKORC1.
- **PharmCAT v3.4.0 computes no dose.** When the only evidence for CYP2C9 `*3` is absent, it returns a confident-looking `*1/*1` Normal Metabolizer with score 174 instead of 176. Cis-phased `*2` plus `*3` gives no call. Its AMP Tier 1 missing-position note cannot fire, because `hasAmp1Positions()` returns `m_amp1Positions.isEmpty()`.

## Applicability

- **Documents.** The equations, trials, guideline and TTR studies were read as published text (author manuscripts, publisher text or abstracts; see Evidence). No patient-level data were examined.
- **CPIC.** Statements refer to the CPIC 2017 warfarin update (author manuscript) only, not to any later CPIC revision.
- **PharmCAT.** Two revisions of `PharmGKB/PharmCAT` were examined. The source was read at `8e6f81b9372da54f9281d452cd171253c6a8974f` (HEAD on 2026-11-21). The v3.4.0 release jar, whose tag commit is `41f21b71886b961b24a00344ef2dad2387aaa0c9`, was executed. Behaviour is claimed for the pinned source only for code paths that the compare in section 5 shows to be unchanged; that extension is derived, not executed. Execution used single-sample GRCh38 VCFs, the default options (combination mode and partial-allele calls off) and JSON output.
- **Execution scope.** The equation and TTR probes are reimplementations on synthetic inputs. They characterise the published formulas and rules, not a clinical system or the trial data. No output here is a dose recommendation.
- **Relationship.** PharmCAT's calls are read against the inputs CPIC 2017 needs, the trials against the equations they used, and the TTR endpoints against the rules that define them.

## Findings

### 1. Dose-prediction equations: derivation, form and coefficients

Basis: documentation + execution. The documentation is the IWPC 2009 author manuscript and its Supplementary Appendix 1 (sections S1e and S1f), the Gage 2008 author manuscript, and the CPIC 2017 supplement, which reproduces both pharmacogenetic equations. The execution is a reimplementation of the equations run on synthetic inputs.

**IWPC 2009 cohort.** 21 research groups in 9 countries on 4 continents contributed data. The analysis used 5,052 patients with a target INR of 2 to 3, split by random 80/20 stratified sampling into 4,043 derivation and 1,009 validation patients. Validation data were withheld from the modellers until the final model had been chosen.

Race (derivation / validation):

| Group | Derivation | Validation |
|---|---|---|
| White | 55.2% | 55.7% |
| Asian | 30.4% | 29.7% |
| Black | 8.7% | 9.6% |
| Mixed or missing | 5.6% | 5.0% |

The outcome was the stable therapeutic dose. Sites defined that dose differently; Supplementary Appendix 1, section S2, lists the per-site definitions.

**Gage 2008 cohort.** 1,015 derivation patients from three US anticoagulation services and the PREVENT trial; the PREVENT participants had a target INR of 1.5 to 2.0. Validation used 292 prospectively dosed patients, most of whom (77%) had undergone joint replacement. Race (derivation / validation): Caucasian 83% / 83%; African American 15% / 15%. Therapeutic dose was defined as a dose unchanged for at least 6 days with an INR within 70% to 130% of target.


**Model forms and coefficients (IWPC from a copy of the supplement plus, for the pharmacogenetic equation only, the CPIC 2017 supplement; Gage from the CPIC 2017 supplement, consistent with the paper's per-variable effects).** IWPC fitted ordinary least squares to the square root of weekly dose; it beat support-vector regression, trees, MARS, LARS and Lasso on 10-fold cross-validated MAE. Gage fitted stepwise regression to log daily dose with additive allele counts.

```text
IWPC pharmacogenetic: sqrt(mg/week) = 5.6044 - 0.2614*age_decades + 0.0087*height_cm + 0.0128*weight_kg - 0.8677*vk_AG - 1.6974*vk_AA - 0.4854*vk_unknown - 0.5211*c_12 - 0.9357*c_13 - 1.0616*c_22 - 1.9206*c_23 - 2.3312*c_33 - 0.2188*c_unknown - 0.1092*asian - 0.276*black - 0.1032*mixed + 1.1816*inducer - 0.5503*amiodarone
IWPC clinical:        sqrt(mg/week) = 4.0376 - 0.2546*age_decades + 0.0118*height_cm + 0.0134*weight_kg - 0.6752*asian + 0.406*black + 0.0443*mixed + 1.2799*inducer - 0.5695*amiodarone
Gage pharmacogenetic: ln(mg/day)    = 0.9751 - 0.3238*vk_1639A + 0.4317*bsa - 0.4008*c3 - 0.00745*age_years - 0.2066*c2 + 0.2029*target_inr - 0.2538*amiodarone + 0.0922*smokes - 0.0901*aa_race + 0.0664*dvt_pe
```

Variable coding. IWPC age is the decade index (1 for ages 10 to 19, 2 for 20 to 29, and so on), not age/10. VKORC1 refers to `rs9923231`. CYP2C9 diplotypes involve only `*2` and `*3`. White, VKORC1 G/G and CYP2C9 `*1/*1` form the reference category; this is inferred from the indicator set. Missing VKORC1 was imputed from race plus `rs2359612`, `rs9934438` or `rs8050894` by a published decision list. Imputation was not applied for Black or missing/mixed race at two of the three SNPs, because linkage disequilibrium differs: R² for `rs2359612` was 0.463 in African Americans versus 0.981 in Caucasians. Gage codes allele counts 0/1/2 for VKORC1 −1639A, CYP2C9`*3` and CYP2C9`*2`. BSA is in m², age in years, and race is 1 if African American. Gage's clinical-only equation was not verified (it is printed as an image).


**Reported accuracy.** IWPC validation results:

| Metric | IWPC pharmacogenetic | IWPC clinical | Fixed 35 mg/week |
|---|---|---|---|
| MAE, mg/week | 8.5 | 9.9 | 13.0 |
| R² | 43% | 26% | 0 |

In the same validation cohort, the pharmacogenetic equation correctly identified 49.4% of patients needing 21 mg/week or less (clinical equation: 33.3%) and 24.8% of patients needing 49 mg/week or more (clinical: 7.2%). Across all 5,052 patients, the share of predictions within 20% of the actual dose was 46.0% (pharmacogenetic), 38.4% (clinical) and 29.4% (fixed dose); these percentages are derived arithmetic from the supplement's S10 counts.


Gage 2008 reported R² of 53.1% in derivation and 54% in validation for the pharmacogenetic equation, against 21.5% and 17% for a clinical-only equation.
Its validation median absolute error was 1.0 mg/day for the pharmacogenetic equation, against 1.5 mg/day for the clinical-only equation.


**Accuracy by ancestry (documentation).** In the Gage 2008 derivation cohort, R² was 57% among 838 Caucasian patients and 31% among 153 African-American patients. In the validation cohort it was 55% (n=242) and 40% (n=45) respectively.
IWPC 2009 states that a race-adjusted general model outperformed race-specific models and "performed well for each of the three major ethnic groups". The per-race R² and MAE are in a supplement figure (S9b) that was not machine-readable, so they are not reproduced here.
Limdi et al. 2015 followed an inception cohort of 1,357 patients (595 African American, 762 European American) and fitted log-dose regressions on the COAG algorithm predictors. Total R² was 51.4% in European Americans and 29.3% in African Americans, and the genetic component was 34.1% and 7.0% respectively (both P<.001).
Adding CKD, CYP4F2, CYP2C9 `*5/*6/*11` and `rs12777823` raised total R² to 54.0% in European Americans and 33.9% in African Americans. Per-allele dose changes differed significantly by race for three variants:
- **CYP2C9 `*2`:** −20.6% in European Americans versus +3.0% (n.s.) in African Americans; interaction P<.001.
- **VKORC1:** −28.9% versus −20.0%; interaction P=.003.
- **`rs12777823`:** −2.3% (n.s.) versus −12.3%; interaction P=.006.
For CYP2C9 `*3` the effect was similar in both groups (−34.1% versus −37.8%; interaction P=.52). Carriage of at least one minor allele, European American versus African American: `*2` 25.6% vs 4.9%, `*3` 12.6% vs 2.3%, `*8` 1.1% vs 13.9%, `*5/*6/*11` 0.0% vs 3.4%, VKORC1 60.2% vs 18.5%, `rs12777823` 30.6% vs 42.1%. Black patients made up about 9% of the IWPC derivation cohort and 15% of the Gage derivation cohort.


**Divergence probe (execution; a reimplementation of the published equations, not a dosing tool).** `support/dosing_equations_probe.py` evaluates the IWPC and Gage pharmacogenetic equations on 72 synthetic inputs: 4 clinical profiles × 3 VKORC1 genotypes × 6 CYP2C9 diplotypes. Gage requires target INR, smoking and DVT/PE; these were fixed at 2.5, no and no.
The Gage/IWPC ratio ranged from 0.915 to 4.493. In 19 of the 72 rows the two predictions differed by more than 20%. For common genotypes they agree: the 65-year-old White profile at VKORC1 G/G and CYP2C9 `*1/*1` gives 41.9 mg/week (IWPC) versus 42.5 mg/week (Gage).
The largest divergences occur where several dose-lowering factors combine. For an 80-year-old profile taking amiodarone with VKORC1 A/A and CYP2C9 `*3/*3`, IWPC predicts 1.4 mg/week and Gage predicts 6.5. For the 65-year-old profile with A/A and `*3/*3`, the predictions are 6.0 and 10.0.
Derived explanation: IWPC is additive on the square-root scale. Subtracting several genotype terms therefore drives the root toward zero, and squaring the result gives a steep fall in dose. Gage is additive on the log scale, so the same factors multiply, and the dose shrinks in proportion without approaching zero. The two forms agree near the centre of the data and diverge in the sparse low-dose tail. IWPC itself reports correctly identifying only 49.4% of patients needing 21 mg/week or less.
The way inputs are coded changes the IWPC output for the same 65-year-old person with VKORC1 A/G. With CYP2C9 coded `*1/*1` the prediction is 31.4 mg/week; coded "unknown", 29.0; coded `*1/*2`, 25.9. A CYP2C9`*8` carrier is not representable in IWPC, so the output depends on how the implementer codes that allele. For VKORC1 at CYP2C9 `*1/*1`: G/G gives 41.9, unknown gives 35.9 and A/A gives 22.8.
The two equations also code age differently. IWPC uses a decade index, so its prediction drops by 8.7% between ages 59 and 60 (34.44 to 31.44 mg/week) and then stays flat to age 69. Gage uses age in years, so its prediction falls smoothly, from 32.12 at 59 to 29.81 at 69.

### 2. Randomized trials of genotype-guided dosing

Basis: documentation. Sources: the COAG author manuscript and design paper; the EU-PACT publisher text as hosted on a third-party site, plus the PubMed and registry records; the GIFT PMC full text and design paper.

| | COAG (Kimmel 2013) | EU-PACT (Pirmohamed 2013) | GIFT (Gage 2017) |
|---|---|---|---|
| Design | double-blind (encapsulated doses); 18 US centres | single-blind (patients); 3 UK and 2 Swedish centres | 2×2 factorial with target INR 1.8 versus 2.5; arm and genotype blinded, doses open; 6 US centres |
| n randomized (analysed) | 1,015 (955) | 455 (427 with at least 13 days of INR data) | 1,650 (1,597 mITT) |
| Genotype arm | Gage 2008 pharmacogenetic equation on days 1–3, then the Lenzini 2010 INR-based revision on days 4–5 | loading-dose algorithm built on a modified IWPC equation (days 1–3), then the Lenzini revision using the day-4 INR | warfarindosing.org on days 1–11, including CYP4F2 |
| Comparator | clinical algorithm (the same sources, using clinical variables only) | 10/5/5 mg loading (age ≤75; 5/5/5 mg if older), then usual care | clinical algorithm in the same web application |
| Variants | CYP2C9 `*2`, `*3`; VKORC1 −1639 | CYP2C9 `*2`, `*3`; VKORC1 −1639 (point-of-care assay, about 2 h) | CYP2C9 `*2`, `*3`; VKORC1 −1639; CYP4F2 V433M |
| Black participants | 27% in each arm | 1.1% | 6.4% and 6.3% |
| Primary endpoint | PTTR (INR 2–3) from day 4 or 5 to day 28, by linear interpolation | PTTR (INR 2.0–3.0) over 12 weeks, by the Rosendaal method | composite of major bleeding, INR ≥4 or death within 30 days, or VTE within 60 days |
| Primary result | 45.2% vs 45.4%; adjusted difference −0.2 (95% CI −3.4 to 3.1); P=0.91 | 67.4% vs 60.3%; +7.0 (3.3 to 10.6); P<0.001 | 10.8% vs 14.7%; RR 0.73 (0.56 to 0.95); P=.02 |
| Black subgroup | 35.2% vs 43.5%; −8.3 (−15.0 to −2.0); P=0.01; interaction P=0.003 | not reported (n=5) | PTTR 50.9 vs 50.7 (P=.96); composite interaction P=.74 |
| Other outcomes | INR ≥4, major bleeding or thromboembolism: 20% vs 21%; HR 1.01 | INR ≥4: 27.0% vs 36.6%, OR 0.63; median days to therapeutic INR 21 vs 29 | PTTR (days 4–28) 54.7% vs 51.3% (+3.4, P=.004); INR ≥4 6.9% vs 9.8% |


Derived reading: the three trials differ in comparator, in how long genotype guided dosing (4–5 days versus 11), in variant panel and in ancestry mix. COAG compared genotype-guided dosing with a clinical algorithm and found no overall difference. In Black patients, genotype-guided dosing gave worse anticoagulation control; their variant panel lacked `*5/*6/*8/*11` and `rs12777823`.
EU-PACT's 7-point gain was measured against fixed loading doses, not against a clinical algorithm, in a population that was 98.5% white. GIFT's composite benefit came mainly from fewer INR values of 4 or more, as the authors themselves note. None of the three trials was powered for bleeding or thromboembolism alone.

### 3. Time in therapeutic range (TTR)

Basis: documentation (Rosendaal 1993 abstract; Siddiqui 2018 full text; Schmitt 2003 abstract) + execution (a toy computation, `support/ttr_probe.py`).

The Rosendaal method computes person-time at each INR value "with the assumption of a linear increase or decrease between two consecutive INR determinations". Its original purpose was INR-specific incidence rates of events. TTR is the share of this interpolated time that falls inside the target band. All three trials cite Rosendaal for their PTTR endpoint.
The Rosendaal abstract does not say how to treat window edges, values exactly on a boundary, interrupted therapy or long gaps between measurements. A commonly quoted cutoff of no interpolation across gaps longer than 56 days was not verified against a primary source.

There are two alternative methods. The "traditional" method takes the fraction of INR tests in range. The "cross-sectional" method takes the share of patients whose last INR before a chosen date is in range.
Siddiqui 2018 (612 patients, 21 weeks, Tables 1–2) gives these mean TTRs:

| Method | Mean TTR |
|---|---|
| Rosendaal | 55.1% |
| Traditional | 56.5% (paired p=0.137 versus Rosendaal) |
| Traditional with ±0.2 tolerance | 71.4% |
| Traditional with ±0.5 tolerance | 85.7% |
| Cross-sectional | 66.0% |

The paper's abstract gives different numbers from its own tables.
Schmitt 2003, from its abstract only, reports that linear interpolation "yielded significantly shorter time-in-range" than the other two methods. The two studies therefore agree only that the choice of method and tolerance band changes the result. They do not agree on the size of the gap between linear interpolation and the fraction of tests in range.


**Toy probe (execution; synthetic INR series, not trial data).** The probe uses linear interpolation integrated exactly at range crossings. It was run on four hand-built series and a seeded cohort of 500 simulated patients.
Cohort mean TTR was 57.05% under Rosendaal with range 2–3 over days 4–28. Starting the window at day 0 gave 51.98%, a mean absolute per-patient change of 6.42 points; 22.8% of patients moved by more than 10 points.
Widening the range to 1.8–3.2 gave 73.83%: a mean change of 16.77 points, with 52.4% of patients moving by more than 10 points. Using the fraction of tests in range gave 59.36%: a mean change of 10.21 points, with 44.4% of patients moving by more than 10 points. Excluding gaps longer than 14 days gave 58.02%, a mean change of 1.51 points. Carrying the last value forward to day 28 changed nothing, because every series has a day-28 measurement.
Single series show the same effects. A sparse series with a 29-day gap between INR 2.5 and INR 2.6 scores 98.6% under interpolation but 50.0% by fraction of tests; excluding gaps longer than 14 days gives 83.3%. A series hovering just outside 2–3 scores 44.2% under interpolation and 16.7% by fraction of tests, but 100% with the 1.8–3.2 band.
Derived implication: trial PTTRs are comparable only when they share the window, the target band, the interpolation rule and any gap rule. COAG measured from day 4 or 5 to day 28 and EU-PACT over 12 weeks. GIFT used two different target bands, 2.0–3.0 and 1.5–2.1. Its 54.7% therefore mixes two definitions of the range.

### 4. CPIC 2017: recommendations by ancestry

Basis: normative (CPIC 2017 author manuscript: the prose and the Figure 2 footnotes; the box text inside the Figure 2 image was not readable).

| Population | Guideline statement (abridged; quoted terms as published) | Strength | Effect on the algorithm |
|---|---|---|---|
| Non-African ancestry | Use a published pharmacogenetic algorithm (Gage or IWPC) with VKORC1 −1639 and CYP2C9 `*2`/`*3`. For CYP2C9 poor metabolism, or for VKORC1 A/A combined with poor metabolism, an alternative agent "might be considered". | STRONG | algorithm inputs |
| Non-African | If CYP2C9 `*5`, `*6`, `*8` or `*11` is detected, "decrease calculated dose by 15-30% per variant allele"; larger reductions (20–40%) may be needed for two variant alleles | OPTIONAL | percentage applied to the computed dose |
| Non-African | CYP4F2`*3`: "increase the dose by 5-10%" | OPTIONAL | percentage applied to the computed dose |
| Non-African | `rs12777823` "should not be considered" | not graded | none |
| African ancestry | If CYP2C9 `*5/*6/*8/*11` have not been tested, "dose clinically without consideration for genotype". If they are known, apply the algorithm, then reduce the dose 15–30% (20–40% for two variant alleles). In African Americans, also reduce by 10–25% for `rs12777823` A/G or A/A. | MODERATE | percentage applied to the computed dose |
| African ancestry | CPIC "recommends against pharmacogenetic dosing of warfarin in blacks when only CYP2C9*2 and *3 genotype results are available"; makes no CYP4F2 recommendation | — | gating |
| All | Genetic loading dose by the EU-PACT algorithm | OPTIONAL | initiation |


Structurally, CPIC adds `*5/*6/*8/*11`, CYP4F2 and `rs12777823` as percentage multipliers applied after an algorithm that encodes only `*2`, `*3` and VKORC1. They are not new regression inputs. This reading is derived from the text: "these algorithms do not include CYP4F2, CYP2C9*5, *6, *8, or *11 or rs12777823".
The guideline wording is internally inconsistent. The non-African prose says "per variant allele", but the African-ancestry prose omits it. The poor-metabolism example in Figure 2 footnote e repeats `*3/*3` and lists VKORC1 A/G as well as A/A, while the prose names only A/A. CPIC's REST API returns no genotype-to-recommendation rows for warfarin. Its usage note says the recommendation "does not follow simple diplotype to phenotype translation".
The guideline names the "wild-type by default" risk: rare or untested variants may be reported as `*1`. PharmCAT shows this behaviour concretely: an untested or missing site gives a `*1` call (section 5).

### 5. PharmCAT: allele definitions, phenotype mapping, and calling behaviour

Basis: source (pinned `PharmGKB/PharmCAT` revision) + execution (release v3.4.0 jar) + documentation (`docs/methods/NamedAlleleMatcher-101.md`).

**Release versus pinned source.** Execution used the v3.4.0 release jar, whose tag commit is `41f21b71886b961b24a00344ef2dad2387aaa0c9`. The pinned source revision `8e6f81b9372da54f9281d452cd171253c6a8974f` is 14 commits ahead of that tag. The GitHub compare of the two revisions shows no change to any allele-definition JSON, `NamedAlleleMatcher.java`, `MatchData.java`, `DiplotypeMatcher.java`, `ResultBuilder.java`, `DefinitionExemption.java` or `Phenotyper.java`. Only three `src/main` files changed:
- `Env.java` and `MessageHelper.java`: an unknown message key now throws instead of returning null;
- `CliUtils.java`: a distribution property was added.

The execution results below are therefore attributed to both revisions for the code paths exercised. This attribution is derived from the diff; the pinned revision was not executed separately.


**Definitions.** The files live under `src/main/resources/org/pharmgkb/pharmcat/definition/alleles/`. Both carry `"source": "CLINPGX"`, `"version": "2026-07-13-11-40"` and GRCh38.p14 coordinates.

| Item | `VKORC1_translation.json` | `CYP2C9_translation.json` |
|---|---|---|
| Positions | 1: chr16:31096368, `rs9923231`, `g.31096368C>T`. This is the guideline's −1639G>A; VKORC1 lies on the minus strand. | 88 on chr10; 10 have no rsID |
| Named alleles | `rs9923231 reference (C)` and `rs9923231 variant (T)` | 94 (`*1`…`*94`). `*1` is the reference row, with all 88 positions filled. |
| Alleles named by the guideline | — | `*2` `rs1799853` g.94942290C>T; `*3` `rs1057910` g.94981296A>C; `*5` `rs28371686` g.94981301C>G; `*6` `rs9332131` (VCF `GA>G`, 1-bp deletion); `*8` `rs7900194` g.94942309G>A; `*11` `rs28371685` g.94981224C>T |
| Shared position | — | `*27` is the other alternate allele (`G>T`) at the `*8` position |
| Multi-position alleles | — | Only 7 non-reference alleles use more than one position (`*18`, `*35`, `*36`, `*61`, `*68`, `*71`, `*92`) |

`exemptions.json` adds `rs12777823` (chr10:94645745 G>A, in the CYP2C cluster) as an `extraPositions` entry under CYP2C9. That position is reported as a "variant of interest" and does not change the CYP2C9 call; `docs/FAQs.md` says the same.


**Phenotype mapping (`src/main/resources/org/pharmgkb/pharmcat/phenotype/CYP2C9.json`).** Each allele carries an activity value:

| Activity value | Function label | Number of alleles |
|---|---|---|
| 1.0 | Normal function | 2 (`*1`, `*9`) |
| 0.5 | Decreased function | 21 (includes `*2`, `*5`, `*8`, `*11`) |
| 0.0 | No function | 13 (includes `*3`, `*6`) |
| `n/a` | Uncertain or Unknown function | 39 (includes `*27`) |

The diplotype activity score is the sum of the two allele values. The mapping from score to phenotype is:

| Activity score | Phenotype |
|---|---|
| 2.0 | Normal Metabolizer |
| 1.5 or 1.0 | Intermediate Metabolizer |
| 0.5 or 0.0 | Poor Metabolizer |
| `n/a` | Indeterminate |

The file lists 2,850 diplotypes. It contains 75 alleles, so 19 alleles that the translation file can call (`*76`–`*94`) have no entry. Case 16 in the probe below shows what PharmCAT reports for one of them.

VKORC1 has no phenotype. CPIC uses the `rs9923231` genotype directly.


**Calling algorithm (source + documentation).**
- Each named allele's score is the number of positions it defines. A diplotype's score is the sum of its two allele scores.
- For unphased data, the matcher enumerates the genotype permutations and keeps every allele pair that is consistent with them. By default it reports only the top-scoring pairs. The documentation states that, with unphased data, the score "is as arbitrary as sorting them alphabetically"; it is a tie-breaker, not a likelihood.
- Missing positions are handled in `MatchData.marshallHaplotypes`. The matcher copies each allele without the missing positions and keeps the copy only `if (newHap.getScore() > 0)`. So an allele defined solely at a missing position silently drops out of the candidate set.
- A partial genotype has one known and one unknown allele. If the known allele is the reference (`0/.`), the position is treated as missing. If it is an alternate allele (`./1`), the matcher accepts it as is, and the gene cannot be called unless combination mode is enabled.
- By default, combination calls and partial-allele calls are off.

**Warfarin output (execution).** PharmCAT does **not** compute a warfarin dose. For CPIC, the report lists two messages:
- `pcat-cpic-warfarin-1-flowchart`: "Please follow the flow chart in figure 2 of the CPIC warfarin guideline to determine the appropriate dosing recommendation";
- `pcat-cpic-warfarin-2-vkorc1`, which explains that CPIC considers only `rs9923231`.

When CYP2C9 positions are missing, the report adds `missing-variants`: "Some position data used to define CYP2C9 alleles is missing which may change the matched genotype." The FDA-label entry quotes the label's dose-range table for the called genotypes.


**Probe: 16 synthetic single-sample VCFs (execution).** Each VCF starts from the release's all-reference `pharmcat_positions_3.4.0.vcf`, restricted to the CYP2C9, VKORC1 and CYP4F2 positions plus `rs12777823`, with the edits listed below. The script is `support/pharmcat_probe.py` and the raw summary is `support/pharmcat_probe_summary.json`.

| Case | CYP2C9 call (score) | CYP2C9 phenotype (activity score) | Other observation |
|---|---|---|---|
| all reference | `*1/*1` (176) | Normal (2.0) | VKORC1 ref/ref; `rs12777823` G/G |
| `*2` and `*3` het, unphased | `*2/*3` (2) | Poor (0.5) | — |
| `*2`, `*3` phased in trans | `*2/*3` (2) | Poor (0.5) | — |
| `*2`, `*3` phased **in cis** (`0\|1`, `0\|1`) | **no call** | No Result | without combination mode |
| `*3` het, **row deleted** | **`*1/*1` (174)** | **Normal (2.0)** | `missingPositions=[rs1057910]`; drug-level `missing-variants` note; `missingAmp1Positions=[]` |
| `*3` GT `./.` | `*1/*1` (174) | Normal (2.0) | same as row deleted |
| `*3` GT `0/.` | `*1/*1` (174) | Normal (2.0) | same as row deleted |
| `*3` GT `./1` | no call | No Result | `missing-variants` note |
| `*2` het + second `*18` SNV het, unphased | no call | No Result | documentation shows a combination-mode call |
| `*2` hom + `*3` het, unphased | no call | No Result | documentation shows `*2/[*2 + *3]` in combination mode |
| `*8` het (`G>A`) | `*1/*8` (89) | Intermediate (1.5) | — |
| `*27` het (`G>T`, same position) | `*1/*27` (89) | Indeterminate (`n/a`) | — |
| `*2` + `*5` het, unphased | `*2/*5` (2) | Intermediate (1.0) | — |
| `*80` het (no phenotype-file entry) | `*1/*80` (89) | Indeterminate (`n/a`) | — |
| VKORC1 T/T, CYP4F2 `*3` het, `rs12777823` G/A | `*1/*1` (176) | Normal (2.0) | VKORC1 variant/variant; CYP4F2 `*1/*3`; `rs12777823` G/A |
| VKORC1 row deleted | `*1/*1` | Normal | VKORC1 not called; **no** `missing-variants` warfarin note |

The safety-relevant behaviour is the following. When the only evidence for a no-function allele is absent, whether by row deletion, `./.` or `0/.`, the result is a confident-looking `*1/*1` Normal Metabolizer. The only differences are a score two points lower (174 versus 176) and a generic drug-level note. The CYP2C9 gene-level `warnings` list is empty in these cases, and no note specific to AMP Tier 1 appears. The next paragraph explains why.


**Upstream defect: the AMP Tier 1 missing-position note cannot fire (source + execution).** `exemptions.json` lists six CYP2C9 `amp1Positions`: 94942290, 94942309, 94949281, 94981224, 94981296 and 94981301. These are the `*2`, `*8`, `*6`, `*11`, `*3` and `*5` sites. VKORC1's list is `[31096368]`. The intended behaviour is to warn when one of these positions is absent. At the pinned revision, `src/main/java/org/pharmgkb/pharmcat/definition/model/DefinitionExemption.java` has two methods with opposite polarity:

```java
85:   public boolean hasRequiredPositions() {
86:     return !m_requiredPositions.isEmpty();
...
178:   public boolean hasAmp1Positions() {
179:     return m_amp1Positions.isEmpty();
```

`src/main/java/org/pharmgkb/pharmcat/haplotype/MatchData.java` collects the missing AMP positions only when that predicate is true:

```java
151:       if (exemption.hasAmp1Positions()) {
152:         for (VariantLocus missing : m_missingPositions) {
153:           if (exemption.isAmp1Position(missing.getPosition())) {
154:             m_missingAmp1Positions.add(missing.getVcfChrPosition());
```

For every gene that has a non-empty `amp1Positions` list, `hasAmp1Positions()` returns false, so `missingAmp1Positions` stays empty. For a gene with an empty list, the predicate returns true, but `isAmp1Position` can never match. Either way the list is always empty.

`src/main/java/org/pharmgkb/pharmcat/haplotype/ResultBuilder.java` emits the `missing-amp1-position` note only when that list is non-empty. Even if the note were reached, it would print the wrong list:

```java
200:     if (!matchData.getMissingAmp1Positions().isEmpty()) {
...
205:       builder.append(" required to meet AMP Tier 1 requirements:  ")
206:           .append(String.join(", ", matchData.getMissingRequiredPositions()))
```

CYP2C9 has `requiredPositions: []`, so the note would list no positions. Execution agrees with the source reading: with the `*3` site (94981296) absent, the match JSON has `"missingAmp1Positions": []` and no AMP note appears.

A patched rebuild, which would confirm that fixing line 179 restores the note, was **not** performed. A search of the repository's GitHub issues for "amp1" on the observation date returned 0 results. The file is unchanged between v3.4.0 and the pinned revision.

### 6. Performance and resource footprint (L1–L6)

Basis: execution (measured on the host below).

Host: x86-64 Linux VM, 96 logical CPUs; the JVM was capped at 8 CPUs and a 2 GiB heap; every run used `timeout 60` and was run sequentially.

| Level | Measurement |
|---|---|
| L1 authoring | not measured |
| L2 toolchain build | not measured (no source build; the release jar was used) |
| L3 latency | PharmCAT full pipeline (matcher, phenotyper, reporter; JSON output) on a 110-row VCF: 2.60–3.42 s wall per run over 16 runs, mostly JVM start-up. User CPU 8.15 s on the reference case. |
| L4 execution | Python equation probe: 72 predictions in 0.02 s wall; TTR probe, 504 series: 0.03 s |
| L5 verification | not measured |
| L6 footprint | PharmCAT peak RSS 749,208–1,192,688 KB over 16 runs; release jar 32,292,707 bytes; per run, about 2 MB of JSON output |

### 7. Comprehensibility, model refinement and validation (C1–C2, V1–V4)

C1, derived. A clinician-facing pharmacogenetic result passes through four representations, each with its own vocabulary:
- VCF genotype;
- star-allele diplotype with a tie-breaking score;
- activity score and phenotype;
- algorithm inputs, then percentage adjustments.
The hazards sit at the boundaries between these steps. The score drop from 176 to 174 is the only sign at the diplotype level that the `*3` site is missing. "Unknown" genotype codes in IWPC are separate regression categories with their own coefficients, not imputations. VKORC1 is reported as C/T on the forward strand, but CPIC writes −1639G>A.

C2 (derived) proposes a single mechanism. The genotype call should carry an explicit set of the allele-defining positions that are untested or missing, and the dosing layer should refuse or widen its output whenever any of them is decision-relevant.
That one rule would cover three separate cases at once: CPIC's "dose clinically if `*5/*6/*8/*11` not tested", the AMP Tier 1 note, and the IWPC "unknown" category. Today they are handled by three different mechanisms.

V1: the 2020 PharmCAT paper reports 59/59 concordance against reference materials for CYP2C9 and for VKORC1.
The missing-position and cis-phase cases in section 5 were not among the asserted behaviours examined. V2: no differential testing against another allele caller was performed.
V3 is not applicable to these subjects; no concurrency or hardware behaviour is involved. V4 is clinical validation, which here means the randomized trials. Their endpoints are surrogates (PTTR, INR ≥4) or a composite driven by a surrogate, and in COAG the effect varied by ancestry.

## Boundaries

**Not examined:**
- the Gage 2008 clinical-only equation's coefficients (printed as an image);
- IWPC per-race R² and MAE (supplement figure S9b) and the IWPC erratum (NEJM 361:1613);
- COAG supplement tables S2–S6, EU-PACT Table S1 (the modified-IWPC loading coefficients), and GIFT's composite by race, target-INR main effect, 2018 correction and protocol;
- CPIC Figure 2 and Figure 3 box text, the paediatric strength grade, and any CPIC revision after 2017;
- Rosendaal 1993 beyond its abstract (the publisher page showed a bot challenge, which was not attempted), Schmitt 2003's numbers, and the current WarfarinDosing.org equations;
- for PharmCAT: a patched rebuild of `hasAmp1Positions()`; execution of the pinned revision; combination mode and partial-allele calls; multi-sample, structural-variant and copy-number inputs; the HTML report; and the JVM version, which was not recorded.

**Unknown:**
- The "no interpolation across gaps over 56 days" convention has no primary source in this investigation.
- Siddiqui 2018's abstract (65.97 / 58.12 / 51.55; traditional "significantly higher") disagrees with its Tables 1–3 (66.0 / 55.1 / 56.5; paired p=0.137). Section 3 uses the tables.
- The clinical consequence of the AMP Tier 1 defect is unknown; only the missing note was observed.

**Known not to apply:**
- PharmCAT does not compute or adjust a warfarin dose; it points to CPIC Figure 2.
- IWPC and Gage cannot represent CYP2C9 `*5/*6/*8/*11`, CYP4F2 or `rs12777823` as inputs.

**Stronger conclusions not established:**
- Whether genotype-guided dosing "works" in general. The trials differ in comparator, duration, panel and ancestry, so their results are not poolable here.
- That the probe's Gage/IWPC ratios measure clinical accuracy. They show only where the formulas disagree.
- That the toy TTR shifts describe the trials' data.
- That PharmCAT's 59/59 concordance covers missing-position or cis-phase behaviour; it does not test either.

**Performance.** L1, L2 and L5 were not measured.

## Evidence

All evidence was acquired on 2026-11-21.

**PharmCAT** (`PharmGKB/PharmCAT`):
- Source pin `8e6f81b9372da54f9281d452cd171253c6a8974f`. Read: the `definition/alleles/` JSON files and `phenotype/CYP2C9.json` named in section 5; `DefinitionExemption.java` lines 85–86 and 178–179, `MatchData.java` lines 151–154 and `ResultBuilder.java` lines 200–206; `docs/methods/NamedAlleleMatcher-101.md` and `docs/FAQs.md`.
- Release v3.4.0, tag commit `41f21b71886b961b24a00344ef2dad2387aaa0c9`; executed `pharmcat-3.4.0-all.jar` (32,292,707 bytes, sha256 `9317ef632bf6c9786ff0d9d455d4c9f6d2882ebd66ad7256b4ae958ddf454741`) with the release's `pharmcat_positions_3.4.0.vcf` as template. Release-to-pin differences: GitHub compare of the two commits.

**Papers.** DOIs and metadata were checked against Crossref `/works/<DOI>`.

| Work | DOI | Venue (Crossref) | Text read |
|---|---|---|---|
| IWPC 2009 | 10.1056/NEJMoa0809329 | NEJM 360(8):753–764 | PMC2722908; Supplementary Appendix 1 via a third-party copy (stanford.edu gene210 reading); pharmacogenetic equation cross-checked against the CPIC 2017 supplement (files.cpicpgx.org `28198005-supplement.pdf`), clinical equation only against the docmath.ca calculator |
| Gage 2008 | 10.1038/clpt.2008.10 | Clin Pharmacol Ther 84(3):326–331 | PMC2683977; coefficients from the CPIC 2017 supplement and Schelleman 2008 (10.1038/clpt.2008.101, PMC2538606) |
| Limdi 2015 | 10.1182/blood-2015-02-627042 | Blood 126(4):539–545 | PMC4513254. Tables 3–4. Table 3 gives VKORC1 −19.99% in African Americans; the text prints 19.9%. |
| COAG (Kimmel 2013) | 10.1056/NEJMoa1310669 | NEJM 369(24):2283–2293 | PMC3942158; design paper 10.1016/j.ahj.2013.04.009 (PMC4415273); Lenzini 2010 10.1038/clpt.2010.13 |
| EU-PACT (Pirmohamed 2013) | 10.1056/NEJMoa1311386 | NEJM 369(24):2294–2303 | publisher PDF as hosted on ResearchGate; PubMed 24251363; ClinicalTrials.gov NCT01119300 |
| GIFT (Gage 2017) | 10.1001/jama.2017.11469 | JAMA 318(12):1115 (Crossref has no end page) | PMC5818817; design paper 10.1038/tpj.2011.18 (PMC3175019) |
| CPIC 2017 | 10.1002/cpt.668 | Clin Pharmacol Ther 102(3):397–404 | PMC5546947; CPIC API `api.cpicpgx.org/v1/recommendation?drugid=eq.RxNorm:11289` returned `[]`; guideline record `id=eq.100425` holds the usage note |
| Rosendaal 1993 | 10.1055/s-0038-1651587 | Thromb Haemost 69(3):236–239 | abstract via Europe PMC |
| Siddiqui 2018 | 10.19102/icrm.2018.091203 | J Innov Card Rhythm Manag 9(12):3428–3434 | PMC7252856, Tables 1–3 |
| Schmitt 2003 | 10.1023/b:thro.0000011377.78585.63 | J Thromb Thrombolysis 15(3):213–216 | abstract only |
| PharmCAT (Sangkuhl 2020) | 10.1002/cpt.1568 | Clin Pharmacol Ther 107(1):203–210 | PMC6977333, Table 1 |

**Execution** (synthetic inputs only; package material in `support/`):

```text
python3 support/dosing_equations_probe.py > dosing_equations_probe.out.json
python3 support/ttr_probe.py > ttr_probe.out.json
python3 support/pharmcat_probe.py pharmcat-3.4.0-all.jar pharmcat_positions_3.4.0.vcf /tmp/pharmcat_probe_work
```

- Each PharmCAT run used `timeout 60 /usr/bin/time -v java -Xmx2g -XX:ActiveProcessorCount=8 -jar ...`, sequentially.
- Preserved outputs: `dosing_equations_probe.out.json`, `ttr_probe.out.json`, `pharmcat_probe_summary.json`, plus `*.time` files with wall time and peak RSS.
- The TTR cohort uses `random.Random(20261121)`.

## Revalidation

- **Equations.** Rerun `support/dosing_equations_probe.py` and diff against the preserved JSON. The 65-year-old White, G/G, `*1/*1` row should give 41.9 (IWPC) versus 42.5 (Gage); the 80-year-old amiodarone, A/A, `*3/*3` row, 1.4 versus 6.5.
- **PharmCAT AMP defect.** At a new revision, read `DefinitionExemption.hasAmp1Positions()` and the guard at `MatchData.java` around line 151. If it still returns `isEmpty()`, the defect persists. Then rerun probe case `05_s1_s3_row_deleted` and check for `missingAmp1Positions` and an AMP note.
- **PharmCAT calling.** Rerun cases 05–08 (missing `*3`) and 04 (cis phase), and compare their calls and scores with section 5. Check the `CYP2C9_translation.json` `version` field and whether `CYP2C9.json` still lacks `*76`–`*94`.
- **CPIC.** Check the CPIC warfarin guideline page for a revision after 2017, and check whether the API still returns no warfarin recommendation rows.
- **TTR.** Rerun `support/ttr_probe.py`. Its output is deterministic.
- **Trials.** No cheap check exists; corrections or reanalyses require rereading the publications.
