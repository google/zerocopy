# Pulse-oximeter saturation algorithms, accuracy testing (ISO 80601-2-61, FDA guidance), reported skin-pigmentation bias, and the BOLD oximetry–blood-gas pipeline

## Summary

- **Scope and data policy.** This is a technical and regulatory reference. It contains no diagnostic or treatment advice. No patient or volunteer records were accessed: the linked dataset needs credentialed access and was not requested, and every execution used synthetic signals or synthetic numbers.
- **Measurement and calibration.** A pulse oximeter estimates functional arterial saturation (SpO2) from the ratio of ratios `R = (AC_red/DC_red)/(AC_ir/DC_ir)` of a red and an infrared photoplethysmogram, followed by an empirical calibration curve `SpO2 = f(R)`.
  - Two open microcontroller implementations at `aromring/MAX30102_by_RF@553ba61952012ad6e895532bb2bfda0e790a3beb` share one curve, `f(R) = −45.060R² + 30.354R + 94.845`, but estimate AC and DC differently. One is the vendor reference algorithm with a documented bug fix; the other is an independently designed replacement.
  - On noiseless synthetic signals both recover `f(R)` within 0.35 SpO2 points. They diverge sharply under noise, drift, low perfusion and high perfusion (execution on the unmodified upstream code).
  - The curve itself is non-monotonic below `R ≈ 0.337` and crosses zero at `R ≈ 1.826`. The replacement algorithm's validity window `0.02 < R < 1.84` therefore admits negative SpO2 values flagged valid, which execution confirmed.
- **Accuracy metric.** Accuracy is specified as `Arms`, the root-mean-square of `SpO2 − SaO2` against CO-oximetry of arterial blood in controlled-desaturation studies. Over a sample, `Arms² = bias² + SD²` (population SD), so a pooled `Arms` cannot reveal a subgroup bias that is confined to a minority of subjects or to low saturations.
- **US FDA 2013 guidance (final, March 4, 2013).**
  - Design: ≥10 healthy subjects, ≥200 pairs, 70–100%.
  - Pigmentation: "at least 2 darkly pigmented subjects or 15% of your subject pool, whichever is larger", with no scale named.
  - Typical `Arms`: ≤3.0% for transmittance and ≤3.5% for ear-clip and reflectance sensors.
  - It references ISO 80601-2-61:2011.
- **FDA draft guidance (January 7, 2025; marked "Not for Implementation" when fetched).**
  - Design: ≥150 participants and ≥3,000 pairs.
  - Skin tone: forehead Monk Skin Tone (MST) groups 1–4, 5–7 and 8–10, each ≥25%, plus colorimetric Individual Typology Angle (ITA). At least half of MST 8–10 must have ITA ≤ −50°.
  - Acceptance: `Arms < 3%`, plus a maximum between-group bias difference of <3.5% (SaO2 70–85%) and <1.5% (>85–100%).
- **ISO 80601-2-61 editions.**
  - The 2017 second edition was only partly recognized by FDA (recognition 1-139): its accuracy-specification clause was excluded because it conflicts with the 2013 table.
  - A third edition dated 2026-04 states that it increases participant number and diversity, reduces the maximum permissible `Arms`, and requires differential-bias determination. Its numbers were **not examined** (paywalled).
- **Reported bias.**
  - **Laboratory study:** at SaO2 60–70%, three oximeters overestimated by +3.56 ± 2.45% in darkly pigmented subjects against +0.37 ± 3.20% in lightly pigmented ones (Bickler 2005).
  - **Retrospective cohorts:** occult hypoxemia (SaO2 < 88% despite SpO2 92–96%) was found in the following shares of measurements (Sjoding 2020):

    | Cohort | Black patients | White patients |
    |---|---|---|
    | University of Michigan | 11.7% | 3.6% |
    | Multicenter | 17.0% | 6.2% |

  - **Treatment eligibility:** among COVID-19 patients, 451 of 1,903 (23.7%) whose predicted SaO2 was ≤94% never had treatment eligibility recognized; 54.8% of them were Black (Fawzy 2022).
- **Oxygen-titration targets** are expressed in SpO2:
  - 92% in white vs 95% in Black ventilated patients (Jubran–Tobin 1990);
  - 94–98%, or 88–92% where hypercapnic failure is a risk (British Thoracic Society, BTS);
  - "no more than 96%" upper limit (BMJ 2018).

  A relative overestimation of 1–2 points therefore shifts the arterial saturation that a fixed SpO2 threshold corresponds to.
- **BOLD.** The open BOLD pipeline at `joamats/pulse-ox-dataset@3d1bf60cef708148742ee13f06025994a073b6df` links SpO2 to arterial blood gases.
  - **Dataset rule:** the nearest SpO2 at or before each arterial sample within 90 min is joined with a backward `merge_asof`. It is then filtered to SpO2 ≤ 5 min before the sample, values in 70–100%, and the first pair per admission.
  - **Size:** 49,099 pairs from MIMIC-III, MIMIC-IV and eICU-CRD.
  - **Technical validation:** Bland–Altman analysis over 5/15/30/60-min windows, split by race-ethnicity.

## Applicability

- **Subjects and their relation.**
  - **Algorithms.** `aromring/MAX30102_by_RF` at the pinned revision provides two SpO2 routines for the MAX30102 optical sensor. `algorithm.cpp` holds `maxim_heart_rate_and_oxygen_saturation`, derived from the vendor's public reference design MAXREFDES117 and modified by the repository author. `algorithm_by_RF.cpp` holds `rf_heart_rate_and_oxygen_saturation`. These are hobbyist/reference firmware, not cleared medical devices. Their behaviour illustrates the signal-processing degrees of freedom that a regulated device's validation must cover. It is **not** evidence about any cleared oximeter.
  - **Dataset pipeline.** `joamats/pulse-ox-dataset` at the pinned revision is the curation pipeline for the BOLD dataset (Matos et al. 2024), consisting of notebooks and BigQuery SQL. The dataset itself is hosted on PhysioNet as a credentialed database (DOI 10.13026/phvt-3277 resolves to `physionet.org/content/blood-gas-oximetry/1.0/`) and was not accessed.
  - **Clinical studies, standard and guidance.** These are examined as published documents. The studies measure bias against self-reported race and ethnicity (Sjoding, Wong, Fawzy, Jubran) or against pigmentation categories (Bickler, Feiner; classification method not examined). Neither is an objective skin-tone measurement. The FDA 2025 draft explicitly states MST "is not a proxy for racial and ethnic diversity".
- **Versions.**
  - **FDA 2013 guidance:** final, issued March 4, 2013; docket FDA-2007-D-0205.
  - **FDA draft:** January 7, 2025, docket FDA-2023-N-4976, still marked draft on the page fetched (page "Content current as of 01/06/2025"). Whether it has since been finalized is **unknown**; a web search found no final version.
  - **ISO 80601-2-61:2017:** second edition 2017-12, corrected 2018-02. Only front matter, FDA's recognition record and FDA's quotations were examined.
  - **ISO 80601-2-61:2026:** third edition 2026-04; front matter and a reseller/BSI listing only.
- **Execution scope.** Synthetic signals were run through the unmodified upstream C++ on an x86-64 Linux host, compiled with `g++ -O2 -fwrapv` and a two-line Arduino header shim. The firmware's target, an ARM Cortex-M0 with an Arduino toolchain, was not used, and integer-overflow behaviour may differ there.
- **Not advice.** Target ranges and thresholds are reported as published statements, only so that their dependence on measurement bias can be analyzed.

## Findings

### 1. Measurement principle and what the code computes

Basis: source + derived. The Mendelson–Ochs 1988 reflectance paper was **not examined** beyond bibliographic metadata.

- **Common structure.** Both routines take 100 samples per channel (`FS = 25` Hz × 4 s), estimate a pulsatile (AC) and a steady (DC) component per wavelength, form a ratio of ratios, and map it to SpO2 with the same quadratic.

  The ISO 2017 front matter defines the reference as "functional saturation of arterial blood, SaO2, which PULSE OXIMETER EQUIPMENT estimates and reports as SpO2". FDA's 2013 scope covers oximeters "based on the amount of transmitted, reflected and scattered light". FDA lists separate typical `Arms` values for transmittance (≤3.0%) and reflectance (≤3.5%) sensors.

- **Maxim reference** (`algorithm.cpp` l.107–209).
  1. Subtract the IR mean, invert, and apply a 4-point moving average (l.113–119; the README states a fix for the averaged length).
  2. Set the valley-detection threshold to the mean of the inverted signal, clamped to `[30, 60]` ADC counts (l.120–127), and call `maxim_find_peaks` with minimum distance 4 and at most 15 (l.131).
  3. For each valley pair at least 4 samples apart, take the raw maxima of red and IR between the valleys as "DC". The AC is the maximum minus the linearly interpolated valley baseline (l.168–181).
  4. Form `ratio = (n_y_ac·n_x_dc_max)/(n_x_ac·n_y_dc_max)` ×100 in `int32` arithmetic (l.182–186) and take a median of up to 5 ratios (l.192–198).
  5. Look the result up in a 184-entry float table equal to `f(i/100)` (`algorithm.h` l.86–101). The result is valid only if `2 < ratio < 184`.
- **Replacement routine** (`algorithm_by_RF.cpp` l.37–127).
  1. DC is the mean (l.64–71). It removes the mean and a least-squares linear trend; `sum_X2 = 83325` equals `2·Σ_{j=0}^{49}(j+½)²` (derived).
  2. AC is the RMS of each detrended channel (l.88–89).
  3. Quality gate: Pearson correlation of red and IR ≥ 0.8 (l.92–95; `min_pearson_correlation` in the header, l.59). The autocorrelation-based heart-rate periodicity must have a peak ≥ 0.5 of lag 0 (`min_autocorrelation_ratio`, l.56), with heart rate in 40–180 bpm (header l.52–53). Otherwise SpO2 is −999 and invalid (l.106–116).
  4. `xy_ratio = (rms_red·mean_ir)/(rms_ir·mean_red)` (l.119). SpO2 is `f(xy_ratio)` if `0.02 < xy_ratio < 1.84` (l.120–121).
- **Properties of the shared curve (derived arithmetic).**
  - **Maximum:** 99.957% at `R = 30.354/(2·45.060) = 0.3368`.
  - **Non-monotonic region:** `f(0.02) = 95.43`. Every value in (95.43, 99.96) has two preimages, one in (0.02, 0.337) and one in (0.337, 0.654). An unphysically small R is thus reported as a normal-range saturation.
  - **Zero crossing:** `f(R) = 0` at `R = 1.8262`, so the window up to 1.84 admits negative outputs.
  - **Table resolution:** the integer `ratio×100` gives 0.6-point steps near R = 1.0 (`table[100] = 80.139`, `table[101] = 79.537`).
  - **Provenance:** the curve's calibration population and data are **not documented** in the repository (only "approximated as" comments).
- **Source-level defects.** Exact lines at the pinned revision:
  - **Mismatched index.** `algorithm.cpp` l.179–181:

    ```c
    n_x_ac= (an_x[an_ir_valley_locs[k+1]] - an_x[an_ir_valley_locs[k] ] )*(n_x_dc_max_idx -an_ir_valley_locs[k]); // ir
    n_x_ac=  an_x[an_ir_valley_locs[k]] + n_x_ac/ (an_ir_valley_locs[k+1] - an_ir_valley_locs[k]);
    n_x_ac=  an_x[n_y_dc_max_idx] - n_x_ac;      // subracting linear DC compoenents from raw
    ```

    The IR AC subtracts a baseline interpolated at the *IR* maximum index from the IR sample at the *red* maximum index (`n_y_dc_max_idx`).
  - **Median logic.** `algorithm.cpp` l.193–198:

    ```c
    n_middle_idx= n_i_ratio_count/2;
    if (n_middle_idx >1)
      n_ratio_average =( an_ratio[n_middle_idx-1] +an_ratio[n_middle_idx])/2; // use median
    else
      n_ratio_average = an_ratio[n_middle_idx ];
    ```

    The branch tests `n_middle_idx > 1` instead of parity. For 5 ratios it averages the 2nd and 3rd smallest rather than taking the 3rd; for 2 ratios it takes the larger rather than the mean (derived from the code).
  - **32-bit overflow.** `algorithm.cpp` l.182–183, `n_nume=( n_y_ac *n_x_dc_max)>>7 ;` and its IR twin, form a 32-bit product before shifting. Execution (`-fwrapv`) with IR DC 230,000 counts rejected every batch at a perfusion index of 7% or more, while 3–5% passed. This is consistent with the product exceeding 2³¹−1: at 7% the red AC is about 10,100 counts and the IR maximum about 230,000.
  - **Negative valid output.** `algorithm_by_RF.cpp` l.120–121 (`if(xy_ratio>0.02 && xy_ratio<1.84)` then the quadratic) returned SpO2 = −0.602 and −1.281 with the valid flag set for synthetic `R = 1.815` and `1.82`.

### 2. Synthetic-PPG execution of both routines

Basis: execution of the unmodified upstream functions on synthetic inputs

- **Signal model.** `IR = DC_ir·(1 − PI·p(t))` and `red = DC_red·(1 − R·PI·p(t))`. Here `p` is a normalized pulse with a second harmonic and the heart rate is 72 bpm. The DCs are 131,500 and 118,545 counts, taken from the first row of the repository's `ExpectedGoodQualitySignals.csv`.
- **Optional impairments.** Gaussian noise (SD in counts) and a 0.3 Hz drift whose amplitude is a multiple of the IR AC can be added.
- **Reference and metrics.** The reference is `f(R)`, so the test checks computational fidelity, not physiological truth. Each condition runs 20–50 consecutive 4-s batches. MAE is computed over batches flagged valid.

| Condition | Maxim valid | Maxim MAE (points) | Replacement valid | Replacement MAE (points) |
|---|---|---|---|---|
| R 0.5 / 0.7 / 1.0 / 1.3; PI 2%; noiseless | 20/20 each | 0.14 / 0.32 / 0.24 / 0.17 | 20/20 each | 0.04 / 0.07 / 0.001 / 0.35 |
| R 0.7; PI 0.5% / 0.1%; noiseless | 20/20 | 0.32 / 0.19 | 20/20 | 0.02 / 0.02 |
| R 0.7; PI 0.03%; noiseless | **0/20** | — | 20/20 | 0.13 |
| R 0.7; PI 2%; noise SD 20 / 100 | 50/50 | 0.29 / 1.66 | 50/50 | 0.11 / 0.36 |
| R 0.7; PI 0.5%; noise SD 100 | **50/50** | **13.1** | 1/50 | 3.7 |
| R 0.7; PI 0.1%; noise SD 20 | **50/50** | **11.3** | 4/50 | 3.8 |
| R 0.7; drift 2× AC | **50/50** | **6.4** | 0/50 | — |
| R 0.7; drift 10× AC | 0/50 | — | 0/50 | — |
| R 0.7 / 1.0; PI 10%; IR DC 230,000 | **0/20** | — | 20/20 | 0.35 / 0.0002 |
| R 1.815 / 1.82; PI 2% | 5/5 | 0.66 / 0.27 | 5/5, **all negative** | 2.0 |

- **Pattern (for these synthetic conditions only).**
  - The reference routine keeps reporting valid values while its error grows to 6–13 points under noise and drift.
  - The replacement's correlation and periodicity gates reject those batches, at the cost of availability.
  - At very low perfusion the reference routine's fixed `[30, 60]`-count valley threshold rejects everything.
  - Heart rates of 45 and 150 bpm did not change validity for either routine.

### 3. Reported bias by skin pigmentation and by race or ethnicity

Basis: documentation. Abstract-level where marked.

| Study | Design and reference | Population and pairing | Definition | Reported result (as published) |
|---|---|---|---|---|
| Bickler, Feiner, Severinghaus 2005 (abstract) | Controlled desaturation, 2–3 min SaO2 plateaus 60–100%; CO-oximeter Radiometer OSM3; Nellcor N-595, Novametrix 513, Nonin Onyx | 11 darkly vs 10 lightly pigmented volunteers | bias = SpO2 − SaO2 | At 60–70%: +3.56 ± 2.45% (dark, n=29) vs +0.37 ± 3.20% (light, n=58). Device differences 2.35–4.30 points. Bias grew "approximately in proportion to desaturation"; its SD was not greater in dark skin |
| Feiner, Severinghaus, Bickler 2007 (abstract) | Same method; clip vs adhesive probes on Masimo Radical, Nellcor N-595, Nonin 9700 | 36 subjects (19 M, 17 F), range of skin tones | bias at 70–80% | From −1.58% (Masimo disposable) to +3.6% (Nellcor disposable). Adhesive probes showed more bias. Up to 10% inter-instrument differences in dark skin at low SaO2. SaO2, sensor, skin colour and gender predicted error |
| Jubran, Tobin 1990 (abstract) | Ventilated ICU patients; arterial SaO2 | 54 patients | ">4%" SpO2–SaO2 difference = inaccurate | 27% (black) vs 11% (white) inaccurate. Target SpO2 92% adequate in white patients; 95% needed in black patients (PaO2 as low as 49 mm Hg at 92%) |
| Sjoding et al. 2020 | Retrospective; arterial blood gases with COHb and MetHb (co-oximetry) | University of Michigan (Jan–Jul 2020): 10,789 pairs, 276 Black and 1,333 White patients. 178 hospitals (2014–2015): 37,308 pairs, 1,050 Black and 7,342 White patients. SpO2 within 10 min | Occult hypoxemia: SaO2 < 88% with SpO2 92–96% | Michigan: 88/749 (11.7%) vs 99/2,778 (3.6%). Multicenter: 160/939 (17.0%) vs 546/8,795 (6.2%). "Nearly three times". A published correction exists (not examined) |
| Wong et al. 2021 (abstract) | eICU-CRD, MIMIC-III/IV, Emory, Grady; 215 hospitals | 87,971 encounters; first ABG; SpO2 ≥ 88% within 5 min before | Hidden hypoxemia: SpO2 ≥ 88% and SaO2 < 88% | 5.5% overall: Black 6.8%, Hispanic 6.0%, Asian 4.8%, White 4.9%. SOFA 24 h later 7.2 vs 6.29. In-hospital mortality among Black patients 21.1% vs 15.0%. The abstract's women percentage (42.9% for 27,713/87,971) is internally inconsistent |
| Fawzy et al. 2022 | Johns Hopkins, 5 hospitals, COVID-19 (Mar 2020–Nov 2021); Radiometer ABL co-oximetry | 1,216 patients, 32,282 pairs; closest SpO2 within ±10 min | Sjoding's definition; eligibility = SpO2 ≤ 94% or supplemental O2 | Adjusted overestimation vs White: Asian 1.7%, Black 1.2%, non-Black Hispanic 1.1%. Unrecognized eligibility 451/1,903 (23.7%), 54.8% of them Black. Hazard ratio for recognition: Black 0.71. Median delay +1.0 h. A correction exists (not examined) |

- **Pairing windows.** Windows differ between studies and change measured agreement: ±10 min in Sjoding and Fawzy, and ≤5 min before the blood gas in Wong and BOLD. BOLD's validation reports RMSE rising sharply with window width for Asian, Black and Hispanic patients, "most pronounced for a time delta of 60 minutes or more".
- **Definitions.** "Occult" (SpO2 92–96%) and "hidden" (SpO2 ≥ 88%) hypoxemia are different conditioning events, so their rates are not comparable. The BOLD paper's Background states "SaO2 > 88% but SpO2 ≥ 88%", which contradicts its Methods (SpO2 ≥ 88%, SaO2 < 88%).

### 4. Accuracy specification and what it can detect

Basis: normative and documentation (FDA guidance, ISO front matter, FDA recognition record) + derived + execution (toy model)

- **`Arms` and its decomposition.** `Arms = √(mean((SpO2−SaO2)²))`. FDA's 2013 guidance defers the formula to clause 201.12.1.101.2.2 of the 2011 edition. The ISO front matter places the calculation method in 201.12.1.101.2 (2017) and 201.12.1.101.4 (2026). **Identity (derived):** `Arms² = (mean d)² + SD_pop(d)²`. A Bland–Altman bias of 2 with SD 2 gives `Arms` 2.83; synthetic check: 2.8257 by both formulas.

  FDA's 2023 discussion paper quotes FDA's 2021 communication: an `Arms` of 2–3% means "about 66% of SpO2 values were within 2 or 3% … and about 95% … within 4 to 6%". That is a one-SD and two-SD reading, which holds only for unbiased, normally distributed errors (derived).
- **2013 vs draft design** (normative content of the guidance documents):

| Item | FDA 2013 (final) | FDA 2025 draft |
|---|---|---|
| Standard referenced | ISO 80601-2-61:2011 | ISO 80601-2-61:2017 (corrected 2018), Annex EE |
| Participants | ≥10 healthy; vary in age and sex | ≥150 healthy; ≥40% male and ≥40% female per MST group |
| Pairs | ≥200, per Annex EE.2.3.4(g) | ≥3,000; 17–30 per participant (average 20–24); ≥30% per MST group and per SaO2 band 70–<80, 80–<90, 90–100 |
| Pigmentation | "at least 2 darkly pigmented subjects or 15% of your subject pool, whichever is larger"; no scale named | MST 1–4, 5–7, 8–10, each ≥25%; ITA = (180/π)·arctan((L*−50)/b*) at forehead and emitter site; ≥50% of MST 8–10 with ITA ≤ −50°; uneven tone excluded |
| Analysis population | Bland–Altman multiple-observation method (μ0, between- and within-subject variance, 95% limits of agreement) | Intention-to-diagnose: all enrolled participants and pairs, including invalid or missing |
| Acceptance | Typical `Arms` (70–100%): ≤3.0% transmittance; ≤3.5% ear clip and reflectance | `Arms` < 3% for all sensor types (2-sided 95% CI upper limit < 3%). Largest pairwise MST-group bias difference < 3.5% (SaO2 70–85%) and < 1.5% (>85–100%). Same limits per 100-point ITA change. 1-sided α = 2.5% |
| Labeling | Overall 70–100% spec plus 70–80/80–90/90–100 table and error plot | Adds demographics, MST and ITA; bias by MST and ITA; a non-disparate-performance statement; a pigmentation warning; and new data for already-cleared devices |

- **ISO interplay.**
  - FDA recognized ISO 80601-2-61:2017 partially (recognition 1-139, entered 2018-09-17). Clause 201.12.1.101.1, the SpO2 accuracy *specification*, "is not recognized" because it conflicts with the 2013 guidance's Table 3.
  - The 2017 numeric limit was **not examined**, and no examined document states it.
  - The 2026 third edition's foreword lists "increased the required number of participants … and their diversity", "reduced the maximum permissible Arms", and "required differential bias determination". Its numbers and its FDA recognition status were **not examined**.
- **What a pooled `Arms` test can detect** (toy model: synthetic SaO2 uniform on 70–100%, base error SD `s`, extra bias `D` only below 80% in a subgroup fraction `q`):
  - **Analytic:** pooled `Arms² = s² + q·D²/3`, while the subgroup's is `s² + D²/3`. Monte Carlo agreed to ≤0.006.
  - **Worked case, `s = 2`, `q = 0.15`:**

    | Extra bias `D` (points) | Pooled `Arms` | Subgroup `Arms` | Subgroup bias in the 70–80 band |
    |---|---|---|---|
    | 4 | 2.19 | 3.06 | 4.0 |
    | 6 | 2.41 | 4.00 | 6.0 |

  - **Derived reading.** The 2013-style pooled criterion (≤3.0%) passes both cases. The draft's between-group bias-difference criterion (<3.5% at 70–85%) targets exactly this structure.
  - **Low-saturation effects fall outside the band.** Bickler's largest effect is at 60–70% SaO2, which lies outside the 70–100% `Arms` band.
  - **Small groups cannot estimate subgroup bias.** With 2 darkly pigmented subjects, a subgroup bias estimate is dominated by between-subject variance. A formal power calculation was **not done**.
- **Occult-hypoxemia sensitivity to bias** (toy model). With synthetic SaO2 ~ N(93, 4) truncated to 70–100, the fraction `P(SaO2 < 88 | 92 ≤ SpO2 ≤ 96)` changes with bias as follows:

  | Error SD | Bias 0 | Bias 1 | Bias 2 | Bias 3 |
  |---|---|---|---|---|
  | 1.5 | 0.0005 | 0.0025 | 0.0106 | 0.0332 |
  | 3.0 | 0.0146 | 0.0258 | 0.0432 | 0.0685 |

  These are properties of the synthetic distribution only. They show that a few points of bias can multiply occult-hypoxemia rates severalfold, and that the multiplier depends on the error SD and the SaO2 case mix.

### 5. Oxygen-titration targets and their dependence on bias

Basis: documentation + derived. Reported targets, not recommendations.

| Source | SpO2 target statement |
|---|---|
| Jubran–Tobin 1990 (abstract) | 92% "reliable" in white patients; 95% "required" in black patients, aiming for PaO2 ≥ 60 mm Hg |
| BTS guideline group summary (BMJ Open Respir Res 2017, doi 10.1136/bmjresp-2016-000170) | "94–98% for most acutely ill patients or 88–92% … for those at risk of hypercapnic respiratory failure" |
| Siemieniuk et al., BMJ 2018 | Strong recommendation for "no more than 96%" upper limit; "90-94% seems reasonable for most" |
| Fawzy et al. 2022 | Eligibility threshold "94% or less or use of supplemental oxygen" (dexamethasone and remdesivir eligibility) |

- **Derived.** If SpO2 overestimates SaO2 by `b` points more in one group, then a fixed SpO2 threshold `T` corresponds on average to arterial saturation `T − b` lower in that group. Fawzy's adjusted relative overestimation of 1.1–1.7 points has this form.
- **Comparable magnitude.** Jubran–Tobin's 3-point target difference (92 vs 95) and Bickler's 3.2-point laboratory difference at 60–70% (3.56 vs 0.37) are of the same order. They come from different devices, eras and saturation ranges, so this is a comparison of magnitudes, not a validation.
- **Calibration defects shift thresholds the same way.** The algorithm defects in §1, such as the non-monotonic curve region and noise-tolerant valid flags, act on the same thresholds. In the synthetic tests, an unchecked 6–13-point error under noise or drift is far larger than the bias differences in §3.

### 6. BOLD linked-dataset pipeline

Basis: source (`notebooks/*.ipynb` at the pinned revision) + documentation (Matos et al. 2024)

- **Parameters.** `notebooks/1_dataset.ipynb` cell 3 sets `lower_SO2 = 70`, `upper_SO2 = 100`, `lenient_time_window = 90` and `strict_time_window = 5`. Cell 0 states the two outputs.

  | Output | Window | Saturation range | Pairs kept |
  |---|---|---|---|
  | Shared `final_df` | 5 min | 70–100% | First per hospital admission |
  | Validation `merged_pairs_big` | 90 min | none | All |

- **MIMIC-IV pairing** (MIMIC-III repeats the steps in cells 30–42).
  1. Arterial samples are lab events in the "Blood Gas" category (cell 9) and must have pH, pCO2, pO2 and SaO2 all non-null (cell 11).
  2. SpO2 comes from the chart event "O2 saturation pulseoxymetry" (cells 14–16).
  3. `pd.merge_asof(..., tolerance = 90 min, direction = 'backward')` attaches the latest SpO2 at or before the sample time (cell 23).
  4. `delta_SpO2 = (t_SpO2 − t_SaO2)` in minutes is filtered to `≥ −5` (cell 24).
  5. Both values must lie in 70–100% (cell 25).
  6. `groupby(hadm_id).first()` keeps one pair per admission (cell 26).
- **eICU-CRD pairing.** The SpO2 column comes from `vitalperiodic.sao2`, with the in-code comment "really spo2, since it's taken with the vitals" (cell 50). A BigQuery cross join keeps vitals with `observationoffset ≤ labresultoffset` and takes the last one per (stay, lab time) via `ROW_NUMBER()` (cell 52). It then filters `labresultoffset − observationoffset ≤ 90` (cell 53).
- **Paper-reported results.**
  - 49,099 first pairs: eICU-CRD 43,438, MIMIC-IV 4,921, MIMIC-III 740. Minority racial and ethnic groups make up about 25%.
  - Race and ethnicity were harmonized to 8 categories but "none of the databases are able to distinguish between race … and ethnicity".
  - Exclusion criteria over-represented White and male patients in MIMIC.
  - Possible MIMIC-III/IV patient overlap from 2008 to 2012.
  - No objective skin-tone data.
- **Technical validation code** (`4_technical_validation.ipynb`).
  - Cell 33's `bland_altman_plot` uses `md = mean(SpO2 − SaO2)`, `sd = np.std(diff)` (population SD) and limits `md ± 1.96·sd`, and marks SaO2 < 70%.
  - Cells 35–37 and 42 repeat this over windows of 5, 15, 30 and 60 min.
  - Cells 39 and 44 split "White Group" vs "Racial-Ethnic Group".
  - With `sd` as population SD, the plotted `md` and `sd` give `Arms = √(md² + sd²)` exactly (derived).
  - `5_missingness.ipynb` plots missingness overall and for Asian, Black, "Hispanic OR Latino" and White subsets.
- **Reanalysis on synthetic records (specified, not run).** The steps would be:
  1. Generate synthetic tables with the same columns: `hadm_id`, `charttime_abg`, `SaO2`, `pH`, `pCO2`, `pO2`; `charttime_vitals`, `SpO2`; `race_ethnicity`.
  2. Apply cells 23–26 verbatim.
  3. Check that the resulting `delta_SpO2 ∈ [−5, 0]` holds, along with the value ranges and one pair per `hadm_id`.
  4. Recompute `md`, `sd` and `Arms` by group for 5- and 30-min windows.

  A run of the real pipeline needs PhysioNet credentialing and a BigQuery project; it was **not attempted**.

### 7. Performance, comprehensibility and validation coverage (L1–L6, C1–C2, V1–V4)

| Level | Known | Basis |
|---|---|---|
| L1 authoring | **not measured** | — |
| L2 build | Host build of probe plus both routines: 1.25 s wall, 94 MB peak RSS (`g++ 15.2 -O2`) | execution |
| L3 latency | **not measured** per call. The 32-bit Cortex-M0 at 48 MHz is the README's recommended board; the README warns lesser MCUs "may have serious problems … especially in terms of sufficient memory" | documentation |
| L4 throughput | Host: 20 conditions × 20–50 batches in 0.12 s total wall (both routines); not representative of the MCU | execution |
| L5 checking | not applicable | — |
| L6 memory | Replacement routine: two `float[100]` stack arrays. Maxim routine: two `int32_t[100]` plus a 184-float table, about 736 B (derived from declarations). Probe peak RSS 4.0 MB; toy model 137 MB (numpy) | source + execution |

- **C1 (comprehensibility).**
  - The ratio-of-ratios principle is two lines. Neither routine's calibration curve has documented provenance, which is the part that carries population dependence.
  - The reference routine's single `valid` flag hides large errors under noise.
  - The regulator's 2013 pigmentation criterion ("darkly pigmented") has no operational definition. The draft's MST/ITA rules are auditable but add two scales with different failure modes: subjective rating vs site-dependent colorimetry.
- **C2 (simplicity).** One invariant, that the error distribution must not depend on pigmentation across the SaO2 range, is enforced by three mechanisms: pooled `Arms`, a decile table, and in the draft a pairwise bias difference with significance. The bias-difference criterion is the one that directly encodes the invariant. `Arms` mixes bias and spread.
- **V1 (property validation).** Controlled desaturation against CO-oximetry is the reference test. The synthetic-PPG probe checks only computational fidelity to `f(R)` and gating behaviour.
- **V2 (implementation vs specification).** No differential testing of firmware against a reference implementation exists in the repository. The probe compared the two routines on identical inputs.
- **V3 (physical validation).** Physical effects were **not examined**: motion, perfusion, nail polish, carboxyhemoglobin and LED wavelength drift.
- **V4 (field validation).** The retrospective cohorts (§3) and BOLD's window and RMSE analysis are field evidence. FDA's draft allows "real-world data" for already-cleared devices.

## Boundaries

- **Not examined:**
  - The full texts of ISO 80601-2-61:2011, 2017 and 2026, including the numeric `Arms` limits, the formula text and Annex EE details.
  - The Mendelson–Ochs 1988 abstract and results; reflectance-specific optics are therefore not reported.
  - The full texts of Bickler 2005 (70–80% and 80–100% bands), Feiner 2007 (gender-effect direction) and Wong 2021.
  - The correction notices for Sjoding and Fawzy.
  - The full BTS guideline in Thorax (doi 10.1136/thoraxjnl-2016-209729); its targets come from the guideline group's BMJ Open Respir Res summary.
  - The original February 19, 2021 FDA safety communication page; FDA's later documents quoting it were used.
  - The BOLD data, its supplemental tables and Figures 4–5 values.
  - Firmware behaviour on the Cortex-M0 target.
- **Unknown:**
  - Whether the 2025 FDA draft has been finalized.
  - The calibration population behind `f(R)`.
  - Whether the reference routine's index mismatch (l.181) changes outputs materially on real sensor data. On synthetic signals, where both maxima coincide, the effect is small.
- **Known not to apply:**
  - The synthetic-PPG results do not measure any cleared oximeter's accuracy, any pigmentation effect (the model has no skin optics), or physiological truth.
  - The toy accuracy model is not a power analysis of either FDA design.
- **Unsupported:** the repository routines are not medical devices, and their licences disclaim warranty.
- **Not established by this evidence:**
  - That self-reported race is equivalent to skin pigmentation; the studies and FDA say it is not.
  - That the published bias magnitudes transfer to other devices, sites or saturation ranges.
  - That the 2025 draft criteria guarantee non-disparate performance in clinical populations; they concern healthy volunteers in a laboratory.
- **Scale limits.** Probes were bounded by 60 s, one thread and 4 GiB. No credentialed or clinical data was requested or used; all inputs were public documents or synthetic.

## Evidence

All observations were made on 2026-11-21 (UTC).

- **Firmware source** (`aromring/MAX30102_by_RF@553ba61952012ad6e895532bb2bfda0e790a3beb`):
  - `algorithm.cpp` l.69–209; quoted l.179–183 and l.193–198.
  - `algorithm.h` l.68–71 and l.86–101 (float table).
  - `algorithm_by_RF.cpp` l.37–127 and l.215–302; quoted l.120–121.
  - `algorithm_by_RF.h` l.44–70.
  - `README.md` (provenance from MAXREFDES117 and the bug fix in item 3).
  - `ExpectedGoodQualitySignals.csv` row 0.
- **Pipeline source** (`joamats/pulse-ox-dataset@3d1bf60cef708148742ee13f06025994a073b6df`):
  - `notebooks/1_dataset.ipynb` cells 0, 3, 9–26 (MIMIC-IV), 30–42 (MIMIC-III), 50–53 (eICU-CRD).
  - `notebooks/4_technical_validation.ipynb` cells 33–44.
  - `notebooks/5_missingness.ipynb` cells 8–20.
  - `README.md`.
- **Regulatory documents:**
  - FDA, "Pulse Oximeters – Premarket Notification Submissions [510(k)s]", March 4, 2013 (fda.gov/media/72470/download and HTML page).
  - FDA draft "Pulse Oximeters for Medical Purposes – Non-Clinical and Clinical Performance Testing, Labeling, and Premarket Submission Recommendations", January 7, 2025 (fda.gov/media/184896/download), with the January 6, 2025 press release.
  - FDA discussion paper, November 16, 2023 (fda.gov/media/173905/download).
  - FDA recognized-consensus-standards record 1-139 (ISO 80601-2-61:2017).
  - ISO 80601-2-61:2017 and :2026 public front matter (reseller-hosted samples) and the BSI listing (2026 edition published 10 Apr 2026).
- **Literature.** All DOIs were verified against Crossref metadata on 2026-11-21. The PhysioNet dataset DOI was verified through the doi.org handle API.
  - Sjoding et al., NEJM 383(25):2477–2478, doi:10.1056/NEJMc2029240, read via the PMC author manuscript PMC7808260.
  - Wong et al., JAMA Netw Open 4(11):e2131674, doi:10.1001/jamanetworkopen.2021.31674 (PubMed abstract).
  - Fawzy et al., JAMA Intern Med 182(7):730, doi:10.1001/jamainternmed.2022.1906 (PMC9257583).
  - Bickler et al., Anesthesiology 102(4):715–719, doi:10.1097/00000542-200504000-00004 (abstract).
  - Feiner et al., Anesth Analg 105(6):S18–S23, doi:10.1213/01.ane.0000285988.35174.d9 (abstract).
  - Jubran and Tobin, Chest 97(6):1420–1425, doi:10.1378/chest.97.6.1420 (abstract).
  - Mendelson and Ochs, IEEE TBME 35(10):798–805, doi:10.1109/10.7286 (metadata only).
  - O'Driscoll et al., BMJ Open Respir Res 4:e000170, doi:10.1136/bmjresp-2016-000170; Thorax 72 Suppl 1, doi:10.1136/thoraxjnl-2016-209729 (identity only).
  - Siemieniuk et al., BMJ 363:k4169, doi:10.1136/bmj.k4169 (article page).
  - Matos et al., Sci Data 11:535, doi:10.1038/s41597-024-03225-z (nature.com full text). Dataset DOI 10.13026/phvt-3277.
- **Execution.** The host was x86-64 Linux with an Intel Xeon at 2.60 GHz, g++ 15.2 and Python 3.13 with numpy 2.3.5. Runs used `ulimit -v 4194304` and `timeout 60`, single-threaded. Files are in `support/`:
  - `ppg/fetch_upstream.sh` downloads the four pinned files, checks their SHA-256 and builds `ppg_probe`. A rebuild from these scripts reproduced `out/ppg_sweep.txt` byte for byte.
  - `ppg/run_sweep.sh` produces `out/ppg_sweep.txt`. The edge cases in `out/ppg_sweep2.txt` use the command lines listed in the script.
  - `python3 pox_toy_model.py 5` produces `out/pox_toy.txt`.

## Revalidation

- **Firmware defects.** Diff `algorithm.cpp` l.168–198 and `algorithm_by_RF.cpp` l.119–126 at any new revision. If `n_y_dc_max_idx` on l.181, the `n_middle_idx > 1` test, the `int32` products, or the `< 1.84` window change, rerun `support/ppg` and compare with `out/ppg_sweep*.txt`.
- **Guidance status.** Re-fetch the FDA draft page and check whether a final guidance has superseded it. If so, re-extract the participant counts, MST/ITA rules and acceptance criteria.
- **ISO editions.** Check FDA's recognized-standards database for ISO 80601-2-61:2026 and whether clause 201.12.1.101.x is recognized.
- **BOLD pipeline.** Diff `notebooks/1_dataset.ipynb` cells 3 and 21–26 for window or range changes. Check the PhysioNet version, currently 1.0.
- **Clinical numbers.** The clinical numbers are fixed publications. Re-verify the DOIs and check the correction notices before reusing the Sjoding and Fawzy figures.
