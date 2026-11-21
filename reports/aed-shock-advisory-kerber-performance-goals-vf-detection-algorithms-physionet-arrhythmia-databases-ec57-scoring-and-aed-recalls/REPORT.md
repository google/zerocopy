# AED shock-advisory rhythm analysis: Kerber performance goals, VF-detection algorithms, PhysioNet arrhythmia databases, EC57-style annotation scoring, and recall and field evidence

## Summary

- **A shock-advisory sensitivity or specificity is defined by test-set composition and scoring rules as much as by the classifier.** The 1997 AHA statement (Kerber et al.) fixes rhythm categories, minimum sample sizes and goals, reproduced in FDA PMA P160033: coarse VF n=200, sensitivity >90% (one-sided 90% lower confidence limit, LCL, 87%); rapid VT 50, >75% (67%); NSR 100, specificity >99% (97%); AF/SB/SVT/heart block/idioventricular/PVCs 30, >95% (88%); asystole 100, >95% (92%); fine VF and other VT 25 each, report only. A 2025 AHA symposium summary says FDA review still follows this table and recommends updating it.
- **The published LCLs are not exactly reproducible.** Wald, Wilson, Agresti–Coull and Clopper–Pearson constructions at the goal reproduce at most 4/5 rows. The best fit is Wald at the goal, truncated, which misses only n=30 (89.90 vs printed 88) (`Basis: derived`; statistical recomputation, not a device measurement).
- **The WFDB reference EC38/EC57 comparators (`bxb`, `epicmp`, `sumstats` in `bemoody/wfdb@de6b1d3981d69060e6a4d1b4e86375fb0d3ed2d1`) embed conventions that move results by tens of points.** Defaults:
  - a 150 ms match window that includes its endpoint;
  - a 5-minute learning period excluded from scoring;
  - test beats inside reference VF neither credited nor penalized;
  - VF episodes detected by any overlap, but not by touching;
  - "gross" (pooled) and "average" (per-record) aggregates side by side.

  On synthetic timelines, one pair of annotation files scored 80.00% (150 ms) vs 40.00% (100 ms). The learning period hid 290 missed beats (100.00% vs 17.38%), and gross vs average sensitivity was 93.94% vs 74.17% (`Basis: source + execution`).
- **wfdb-python's `Comparitor` (`MIT-LCP/wfdb-python@cc9f94fcc8bc938c6fb6cb40fb61c85b33e9404e`) matches only |Δ| < `window_width`, though its docstring calls that the "maximum absolute difference ... permitted".** Its MIT-BIH benchmark helper also departs from EC57-style scoring: `int(0.1*fs)` (36 samples at 360 Hz), only the first reference annotation removed, per-record `np.mean` aggregation, no learning period. `window_width=55` (not 54) reproduces `bxb` exactly, including on 110,000 beats (`Basis: source + execution`).
- **Protocol dominates published VF-detector numbers.** Threshold-crossing intervals (TCI) are reported at:
  - 53% sensitivity and 93% specificity on preselected 4-s extracts (Clayton 1993);
  - 75.1% / 84.4% in continuous, unpreselected analysis (Amann 2005);
  - as one of 30 features in learned classifiers reaching mean 96.6% / 98.8% on public Holter data vs 94.7% / 96.5% on OHCA data after the AHA-framework exclusions (Figuera 2016).

  Figuera et al.'s paper describes a patient-wise test bootstrap. Their released code splits patient-wise but bootstraps segments (`bootstraping.m:175`) (`Basis: documentation + source`).
- **Compression artefact and field failures sit outside bench benchmarks.**
  - CPR artefact: sensitivity mostly >90% but specificity rarely >85% (Ruiz de Gauna 2014).
  - Field audit: coarse-VF sensitivity 99%, non-shockable specificity 98% over 3,310 analysis periods; incorrect shock advice in 4% of shock advices, mostly operator- or circumstance-related (Zijlstra 2017).
  - MAUDE fatality reports: 252 failures to complete analysis, 524 failures to deliver an advised shock (DeLuca 2012).
  - FDA's 2015 final order made AED systems PMA devices, citing >40 class I/II recalls affecting >2 million AEDs after January 2011, mostly from design, purchasing and receiving controls rather than rhythm algorithms.

## Applicability

**Scope.** In scope:

- AED shock-advisory classification (shockable vs non-shockable on surface ECG);
- goals and rhythm categories;
- device, algorithm-testing and regulatory documents;
- classical and learned VF/VT detectors and their evaluation protocols;
- chest-compression artefact;
- public annotated databases;
- annotation-comparison tooling;
- field, failure-report and recall evidence.

Out of scope (see **Boundaries**): defibrillation waveforms and energy, paediatric attenuation, implantable defibrillators, human-factors design, and AED logistics.

**How each subject was examined:**

- **WFDB C package 10.7.0 (`de6b1d39…`).** Built from the pinned tarball; `bxb`, `epicmp`, `sumstats` and `wrann` were executed on synthetic WFDB records (zero-signal headers plus text-generated annotations). Host: x86-64 Linux VM, Intel Xeon @ 2.60 GHz, 96 logical CPUs, GCC 15.2.0 with `-std=gnu89`. Results characterize the tools' scoring rules, not any detector.
- **wfdb-python (`cc9f94fc…`).** `src/wfdb/processing/evaluate.py` was executed unmodified (Python 3.13.15, numpy 2.3.5), with inert stand-ins for its three unused `wfdb.io` imports (`support/comparitor_probe.py`). `qrs.py` was read only, because it needs scipy, which the host lacks.
- **py-ecg-detectors (`f39354cb…`).** Read only; needs scipy and PyWavelets.
- **ohca-vs-public-dbs (`4d799e93…`).** MATLAB source read, not run. A Python port of `calculate_TCI.m` was run on synthetic signals (`support/tci_toy.py`): a toy model of the TCI formula, not the original code and not ECG.
- **Kerber 1997.** The full text was not retrievable; the PubMed abstract was. The goal table was read via FDA SSED P160033 Table 5, and category definitions only where a secondary source attributes them to Kerber.
- **Standards.** Editions were identified from publisher and regulator pages. Only freely available parts were read: eCFR text, the govinfo copy of the final order, IEC sample pages and EC57 preview pages.
- **Literature.** PubMed abstracts, plus full text for the open-access papers (Amann, Figuera, Ruiz de Gauna, the 2025 AHA summary). Shah–Maisel only via a press release and a newspaper report.
- **Not used.** No PhysioNet signals were downloaded and no device was tested; detector numbers are quoted from their sources.

## Findings

### 1. Performance goals, rhythm categories and test-set composition

`Basis: documentation` (Kerber 1997 as reproduced in FDA SSED P160033, Table 5: "The Performance Goals and Lower Confidence Limit Goals are from the Kerber recommendation"; PubMed 9118556).

| Class | Rhythm | Min. samples | Goal | 90% one-sided LCL goal |
| --- | --- | --- | --- | --- |
| Shockable | Coarse VF | 200 | >90% sensitivity | >87% |
| Shockable | Rapid VT | 50 | >75% sensitivity | >67% |
| Non-shockable | NSR | 100 | >99% specificity | >97% |
| Non-shockable | AF, SB, SVT, heart block, idioventricular, PVCs ("other" added in SSED) | 30 | >95% specificity | >88% |
| Non-shockable | Asystole | 100 | >95% specificity | >92% |
| Intermediate | Fine VF; Other VT | 25 each | report only | N/A |

- **Category boundaries (secondary attribution).** Figuera et al. attribute to Kerber that VF <200 µV peak-to-peak is fine VF and that VT <150 bpm is intermediate. They also summarize the framework's requirement that test segments "must be artefact-free and contain a single rhythm". Jekova and Krasteva describe AEDs that shock "to terminate ventricular fibrillation or tachycardia above 180 bpm". Sources thus disagree on the VT rate boundary (150 vs 180 bpm); Kerber's own wording was not examined.
- **The 1997 table still governs FDA review, per a 2025 AHA source.** The AHA AED Symposium summary (JAHA 2025;14:e039291) says the 1997 paper "continues to guide industry and FDA standards". Problems it lists:
  - the coarse/fine VF distinction;
  - specificity requirements for rhythms "rarely seen during cardiac arrest, ie, NSR";
  - small regulatory sample sizes;
  - no paediatric criteria;
  - "30–45 s required for rhythm identification".

  It recommends updating the paper, sample sizes and rhythms-per-patient, limiting tests to arrest rhythms, faster algorithms, paediatric validation and artefact detection during compressions.
- **Field audits reuse the table.** In the SSED post-market audit (RhythmX; rescues December 1999 to December 2016; 5,522 analysis periods), "Other VT" had 9 samples against a goal of 25. The Fine VF row prints an observed 56% beside a "90% CI" value of 66%, which cannot be a lower bound on 56%.

**LCL recomputation** (`support/kerber_lcl.py`, stdlib only; `Basis: derived`):

| Row (n, goal) | Printed | Wald@goal | Wilson | Clopper–Pearson x=⌈goal·n⌉ | Agresti–Coull |
| --- | --- | --- | --- | --- | --- |
| Coarse VF (200, .90) | 87 | 87.28 | 86.95 | 86.72 | 86.93 |
| Rapid VT (50, .75) | 67 | 67.15 | 66.44 | 66.53 | 66.40 |
| NSR (100, .99) | 97 | 97.72 | 96.72 | 96.17 | 96.52 |
| Other non-shockable (30, .95) | 88 | 89.90 | 87.18 | 87.64 | 86.72 |
| Asystole (100, .95) | 92 | 92.21 | 91.41 | 90.92 | 91.32 |

Rows reproduced (rounded / truncated): Wald@goal 3/5 and 4/5; Clopper–Pearson x=⌈goal·n⌉ 3/5 and 0/5; Wilson 2/5 and 0/5; Agresti–Coull 2/5 and 0/5. The script also tests x=⌊goal·n⌋ and a continuous-count Clopper–Pearson; neither does better. No construction reproduces all rows. The best fit, truncated Wald at the goal, fails only the n=30 row, whose implied count (28.5) is non-integer. At n=30, the exact limit for 29/30 is 87.64, so a device that just meets the 95% goal there has quite uncertain specificity.

### 2. Device standards, testing standard and regulation

- **21 CFR 870.5310** (`Basis: normative`; read via the eCFR versioner API because the eCFR web page served a CAPTCHA). An AED system "analyzes the patient's electrocardiogram, interprets the cardiac rhythm, and automatically delivers an electrical shock (fully automated AED), or advises the user to deliver the shock (semi-automated or shock advisory AED)". It is Class III (premarket approval). PMAs were due by April 29, 2015 for pre-1976 AEDs and accessories and for devices found substantially equivalent to them; all others need an approved PMA before distribution. Citation: [68 FR 61344, Oct. 28, 2003; 69 FR 10615, Mar. 8, 2004, as amended at 80 FR 5682, Feb. 3, 2015].
- **Final order** (`Basis: normative`; FederalRegister.gov API metadata, govinfo text): 80 FR 4783 (FR Doc 2015-01619, Jan. 29, 2015), republished in full as 80 FR 5674 (FR Doc 2015-02049, Feb. 3, 2015); Docket FDA-2013-N-0234. It states:
  - "over 40 additional class I or class II recalls ... have impacted over 2 million distributed AEDs", with "design controls, purchasing controls, and receiving acceptance activities being the most common" root causes;
  - models may share one PMA "because shock advisory algorithms and defibrillation waveforms will likely be common across various models";
  - PMA review "will also involve a review of software documentation";
  - AEDs "analyze and interpret ECG data to produce an assessment", which FDA treats as diagnostic functions.
- **IEC 60601-2-4:2010+AMD1:2018 CSV** (edition 3.1, 2018-02-28, 327 pages, ISBN 9782832254134; `Basis: normative`, sample pages only). 201.3.201 defines an AED as a defibrillator that "analyses the ECG obtained from electrodes placed on the patient's skin identifies shockable cardiac rhythms, and automatically operates the DEFIBRILLATOR when a shockable rhythm is detected". The contents list "201.107 Requirements for RHYTHM RECOGNITION DETECTOR" and "Table 201.102 – RHYTHM RECOGNITION DETECTOR categories"; these clauses were not examined. A consolidated edition 3.2 with AMD2:2026 is listed by the IEC and SIS stores and was not examined.
- **ANSI/AAMI EC57:2012/(R)2020** (DOI 10.2345/9781570204784; `Basis: normative`, preview only). Scope 1.1:
  - beat-by-beat comparison is used for QRS, VEB and SVEB detection, and run-by-run comparison for runs;
  - "Detection of ventricular flutter, atrial flutter, ventricular fibrillation, and atrial fibrillation are addressed";
  - "developed for testing algorithms, not entire systems. It is not a performance standard";
  - results are "uncertain indicators of performance in clinical settings".

  The 2012 revision "makes minor changes to the 1998 standard". The contents include "4.5 VF and AF comparisons" and "Table A.5—Example of VF performance report". EC57's scoring clauses were not read; the rules in §3 come from the reference implementation, which says it implements "AAMI/ANSI EC38:1998 ... and ... AAMI EC57:1998" (`bxb.c:25-30`).

### 3. Reference annotation-comparison implementations

#### 3.1 `bxb` (`bemoody/wfdb@de6b1d39…`, `app/bxb.c`)

`Basis: source + execution`.

| Rule | Source | Behavior |
| --- | --- | --- |
| Window | `:814-817` `match_dt = (int)strtim(".15"); /* 150 milliseconds */` | 54 samples at 360 Hz (`strtim` rounds `x*f + 0.5`) |
| Inclusive | `:183-184` `if (T-t <= match_dt && (T-t < abs(T-tprime) \|\| abs(Tprime-tprime) < abs(T-tprime)))`; mirror `:199-200` | \|Δ\| = window matches |
| Learning period | `:830-831` `start = strtim("5:0"); /* 5 minutes */` | beats before 5:00 not tallied |
| Nonstandard flags | `:800-802` | `-f/-t/-w` warn "nonstandard comparison selected" |
| Reference VF | `:308-324` skip VFON..VFOFF; `rpann` `:430-434` returns `'*'`: "test beat labels during reference-marked VF are not to be counted" | extra detections in VF are neither TP nor FP |
| Class map | `amap` `:574-611` | SVEB classes become N unless SVEB output (`-C/-L/-S`) is requested; paced beats become Q |
| Statistics | `:1035-1050` | QRS Se = QTP/(QTP+QFN); +P = QTP/(QTP+QFP); VEB Se, +P, FPR |

Executed checks (`support/annotation_scoring_probe.sh` → `.out.txt`):

- **Window.** 60 reference beats at 1 s (360 Hz), test offsets cycling {0, 20, 35, 36, 53, 54, 55, −53, −54, −55} samples: QRS Se = +P = 80.00% (48/60), with only ±55 unmatched. With `-w 0.1`: 40.00% (24/60), offsets ≤36 matched.
- **Reference VF.** VFON..VFOFF from 319.5 to 330.5 s with 11 test beats inside: 100.00% (39/39).
- **Learning period.** A detector missing every beat before 300 s: 100.00% (61/61) by default, 17.38% (61/351) with `-f 0`.
- **Aggregation.** Records at 59/60 and 3/6 via `bxb -l` and `sumstats`: Gross 93.94, Average 74.17 (`sumstats.c:169-181`).

#### 3.2 `epicmp` (`app/epicmp.c`)

`Basis: source + execution`.

- **Episode delimiters.** VF episodes are only VFON..VFOFF; "RHYTHM annotations are ignored in this context" (`doc/wag-src/epicmp.1:90-94`; `:308-313`, `:354-358`).
- **Match rule.** Any overlap matches (`:238-243` `if ((overlap = find_overlap(b, type)) > 0L) { ... case VFE: match++;`). ST needs ≥50% overlap or the extremum (`:244-261`). An episode starting exactly at the reference end gives `o_end - o_start = 0` (`:499`), i.e. a mismatch (`:266-267`).
- **Learning period.** Default start 5 min (`:966-967`); episodes ending earlier are skipped (`:161-163`) and earlier starts clipped (`:170`).
- **Statistics.** Episode Se/+P count episodes; duration Se/+P weight overlap time (`:798-801`).

On reference episodes 310–330 s and 400–420 s vs test episodes 329.9–335, 420–425 and 500–502 s:

- default: episode Se 50% (1/2), +P 33% (1/3), duration Se "0%" (0.103 of 40 s), duration +P 1%;
- with `-I 3`: episode +P 50% (1/2).

A 0.1-s overlap is a full episode detection. Percentages print as integers.

#### 3.3 wfdb-python `Comparitor` (`cc9f94fc…`, `src/wfdb/processing/evaluate.py`)

`Basis: source + execution`.

- **Window semantics.** The docstring (`:413-415`) defines `window_width` as "The maximum absolute difference in sample numbers that is permitted for matching annotations". The code tests `if smallest_samp_diff < self.window_width:` (`:205`, `:219`). On the 60-beat timeline, tp = 18, 36 and 48 for widths 36, 54 and 55; only 55 reproduces `bxb`.
- **Greedy matching.** One use per test annotation (`last_matched_test_num`, `:165`); FP = n_test − tp (`:113-118`).
- **Benchmark helper.** `benchmark_mitdb_record` uses `window_width=int(0.1 * fields["fs"])` (`:549`), i.e. |Δ| ≤ 35 samples (97.2 ms). It passes `ann_ref.sample[1:]` (`:547`); a TODO reads "remove non-qrs detections from reference annotations" (`:479-481`). `benchmark_mitdb` returns `np.mean` of per-record statistics (`:503-504`). No learning period.
- **Agreement with `bxb`.** On the two-record case, the per-record mean Se is 0.7417 vs pooled 0.9394. On 110,000 synthetic beats, `Comparitor(55)` and `bxb` agree exactly (97,120 matched, 12,880 missed, 12,252 extra); `Comparitor(54)` gives 95,287.

#### 3.4 QRS detectors are not VF detectors

`Basis: source`.

- **XQRS.** Defaults `hr_max=200`, `ref_period=0.2` s (`qrs.py:112`, `:117`); detection requires `i - self.last_qrs_ind > self.ref_period` (`:465`).
- **py-ecg-detectors.** `panPeakDetect` accepts a peak only if `(peak-signal_peaks[-1])>0.3*fs` (`ecgdetectors.py:666`), capping acceptance near 200/min. Pan–Tompkins uses a first-order 5–15 Hz band-pass (`:471-475`).
- **Consequence.** These are QRS benchmarking tools, and their refractory logic cannot count VF/VT complexes. Amann et al. measured a Pan–Tompkins-based "TOMP" detector at 92.5% sensitivity and 40.6% specificity and conclude QRS detectors "are not suitable for VF detection".

### 4. VF/VT detection algorithms and evaluation protocols

`Basis: documentation`; code rows add source, the toy rows add execution.

| Study | Method | Data and protocol | Reported result |
| --- | --- | --- | --- |
| Thakor 1990 | TCI on 1-s stages, then sequential hypothesis test (VT vs VF) | per Amann: threshold 20% of stage max; TCI ≥ 400 ms → SR | original not examined |
| Clayton 1993 | TCI, ACF, VF-filter, spectrum | CCU recordings; 70 VF extracts × 4 s; 40 VF-like | TCI Se 53% / Sp 93%; VF filter 77% / 55%; "overall" TCI 93% / 60% |
| Jekova–Krasteva 2004 | integer band-pass filter plus a wave-detection branch | AHA and MIT records | Se 95.93%, Sp 94.38% |
| Amann 2005 | 5 old and 5 new VF algorithms + 2 QRS detectors | no preselection; 1-s steps; 8-s window, decision at window end; VF/no-VF; MIT 48×2 ch×1805 s, CU 35×508 s, AHA 7001–8210 40×2×1800 s | TCI(8 s) 75.1/84.4; SCA 71.2/98.5; VF filter(8 s) 18.8/100; at Sp 95/99: SCA Se 79.0/66.4, TCI(8 s) 25.3/1.3 |
| Figuera 2016 | 30 features; L1-LR, RF, bagging, boosting, SVM | 4-/8-s segments; noise, transitions, slow VT, fine VF and asystole excluded; vfdb 22, cudb 35, AHA 8201–8210 (10), channel 1, 250 Hz; OHCA 260 patients, 10-s artefact-free; 80/20 patient split | public Se 96.6, Sp 98.8, BER 2.2; OHCA 94.7, 96.5, 4.4; 6 vs 3 features; 4 vs 8 s ΔBER <0.5 |

- **Amann's decision count is reproducible.** 2·48·(1805−7) + 35·(508−7) + 2·40·(1800−7) = 172,608 + 17,535 + 143,440 = 333,583 (`Basis: derived`).
- **Prevalence controls positive predictivity.** Amann's TCI(8 s) +P is 0.8% on MIT DB vs 54.4% on AHA DB.
- **TCI formula** (`calculate_TCI.m:103`): `tci6(j+1) = 1000/((N-1)+(t2/(t1+t2))+(t3/(t3+t4)));`. N is the pulse count in the middle second, t1–t4 are boundary gap times, and the threshold is `0.2*max` of each mean-subtracted 1-s stage (`:46-51`).
- **Toy-model results** (Python port, `support/tci_toy.py`; `Basis: execution`, not ECG):
  - Narrow Gaussian pulse trains give TCI equal to the period: 1000, 600.1, 400.0 and 333.3 ms at 60, 100, 150 and 180/min. So the 400 ms threshold is a 150/min rate test, and a regular narrow-complex rhythm at 180/min enters the VF/VT branch.
  - Sinusoids at non-integer cycles per second deviate from 1000/f: 1.5 Hz gives 503.6 vs 666.7 ms; 2.5 Hz gives 334.1 vs 400 ms. The gap correction assumes narrow pulses.
  - A flat segment fails: the original evaluates `pulses(1)` unconditionally at `:68`, after `index = find(aux(wl+1:2*wl))` at `:64`, and MATLAB raises an index error on an empty array (not run in MATLAB).
- **Figuera's code vs paper** (`Basis: documentation + source`). The paper says the test-metric distribution was "estimated using patient-wise bootstrap resampling on the test set ... by randomnly selecting N patients with replacement". In `bootstraping.m`, the patient split is drawn once (`:56-96`, after `rng(2)` at `:32`), and then for `B = 500` (`:166`), `:175` `idx_test = datasample(1:length(idx_val), length(idx_val));` resamples held-out segments. `suplementary materials/bootstraping_per_ddbb.m:87` is the same. Feature selection does resample patients (`feature_selection.m:69-77`). The paper's `ecg parameters computation/process_data.m` returns HTTP 404 at the pin.

### 5. Chest-compression artefact

`Basis: documentation` (Ruiz de Gauna 2014).

- **Why CPR pauses for analysis.** "CPR must be interrupted for a reliable automated rhythm analysis because chest compressions induce artifacts in the ECG." Methods either adaptively filter the artefact or analyse the corrupted ECG directly. To find compression-free intervals, the review names compression-depth or force channels, or thoracic impedance.
- **Typical performance.** "Most studies report sensitivities above 90% ... However, the specificity rarely exceeds 85%." Table 1 (OHCA data, Se/Sp): MC-RAMP 96.7/79.9; Kalman 90.1/80.4; LMS 95.4/86.3; ART 92.1/90.5; Li direct 93.3/88.6; Krasteva direct 90.1/86.1.
- **Proposed evaluation.** The review proposes the probability of interrupting CPR over time, estimated by Kaplan–Meier on 242 shockable and 634 non-shockable long OHCA segments. It also describes analysis during ventilation pauses with 3-s windows; the median real pause is 7 s.
- **Table 1's interval labels** (`support/interval_label_check.py`; `Basis: derived`). The caption says "Wald's interval", but with counts reconstructed as round(estimate·n):
  - only 3 of 12 printed intervals are symmetric;
  - Wald reproduces 2 of 12 within ±0.15 points, Wilson 4 and Clopper–Pearson 1;
  - the MC-RAMP sensitivity interval (87.6–98.0) matches no construction.

### 6. Annotated databases and seams with the scoring tools

`Basis: documentation` (PhysioNet pages; DataCite DOI metadata).

| Database | Contents | Annotation caveat |
| --- | --- | --- |
| `mitdb` (10.13026/C2F305) | 48 two-channel ~30-min records from 47 subjects; 360 Hz, 11-bit, 10 mV; 23 random + 25 selected; ~110,000 beat labels | records 201 and 202 come from one subject and "should be assigned to the same partition"; selection skews prevalence |
| `vfdb` (10.13026/C22P44) | 22 half-hour records | ".atr files contain only rhythm labels (no beat labels)"; VF appears as aux strings `VF`/`VFIB`, `VFL`, `VT` |
| `cudb` (10.13026/C2X59M) | 35 eight-minute records, 250 Hz, 12-bit | annotations "in no sense definitive. All beats are labelled normal"; VF onset approximate, mean 5:47 (SD 2:01); 5 paced records; 3 .atr files revised in 2006 |
| AHA DB | not freely distributed | not examined |

`Basis: derived` from §3.2:

- `epicmp` sees VF only via VFON/VFOFF, so `vfdb` rhythm labels must be converted first, and results depend on the conversion.
- The 5-minute default clips or drops early `cudb` VF episodes, so results depend on `-f`.
- Splitting `mitdb` by record, as Amann's "48 files" does, separates the 201/202 subject.

### 7. Field, failure-report and recall evidence vs bench choices

`Basis: documentation`; derived where marked.

- **Zijlstra 2017.** January 2012 to December 2014; 1,114 recordings and 3,310 analysis periods (1,091 shock advices, 2,219 no-shock advices).
  - coarse-VF sensitivity 99%; non-shockable specificity 98%;
  - incorrect shock advice: 4% (44/1,091) — 15 device-related, 28 operator-related, 1 unknown; only 2 shocks changed the rhythm;
  - incorrect no-shock advice: 1% (26/2,219) — 20 device-related, 6 operator-related;
  - no shock after advice: 5% (59/1,091) — 33 operator failures, 17 removals, 8 off-button presses, 1 other;
  - 67 of 1,073 shockable periods (6%) unshocked.

  The abstract's "72% caused by the operator or circumstances" equals (28+6+59)/(44+26+59) = 93/129 = 72.1% when all non-deliveries count as operator or circumstance (`Basis: derived`).
- **DeLuca 2012 (MAUDE, fatal events, June 1993 to October 2008).** 1,284 events, including 1,150 failed defibrillation attempts:
  - 37 never powered on;
  - 252 failed to complete rhythm analysis;
  - 524 failed to deliver a recommended shock;
  - 149 operator disagreements with the analysis;
  - 54 low-battery warnings and 110 unexpected power-offs.

  Inter-rater agreement on "most likely cause" was 55.9%.
- **Shah–Maisel 2006** (via a Harvard Gazette release of May 19, 2006 and an Arizona Daily Star report of August 9, 2006). Weekly FDA enforcement reports for 1996–2005 contained 52 advisories affecting 385,922 devices, "more than one in five AEDs". The newspaper adds ~164,000 AEDs and ~222,000 accessories, and "370 deaths among the 801 adverse events". The paper's cause breakdown was not examined.
- **Bench vs field** (`Basis: derived`). Kerber- and EC57-style tests score artefact-free single-rhythm segments. They cannot see powering on, completing analysis, batteries, delivery after advice, operator overrides or compressions. Only incorrect advice is comparable, and in Zijlstra's data device-related incorrect advice was 35 of 3,310 periods (1.06%).

### 8. Performance and footprint across levels

| Level | Quantity | Value | Basis |
| --- | --- | --- | --- |
| L1 | reference-tool source size (proxy, not velocity) | `bxb.c` 1,305 lines; `epicmp.c` 1,040; `sumstats.c` 563; `evaluate.py` 553; `qrs.py` 1,808; `ecgdetectors.py` 703; `calculate_TCI.m` 142 | measured (`wc -l`) |
| L1 | effort to build or validate a shock-advisory algorithm | not measured; no source found | — |
| L2 | WFDB library build+install; 5 applications | 1.83 s; 0.84 s wall | measured |
| L2 | Python package installs | not measured | — |
| L3 | AED time to decision | "30–45 s" (2025 AHA); 4/8-s segments (Figuera); 3-s ventilation-pause windows (Ruiz de Gauna) | documentation |
| L4 | detector compute, % of real time (MATLAB, Power Mac G5 2 GHz, CU DB) | TCI 2.1; VF filter 1.9; SCA 5.9; WVL2 40; LI 15; TOMP 0.84 | documentation (Amann Table 2) |
| L4 | AED firmware latency, CPU and energy | not measured | — |
| L5 | `bxb` on 110,000 beats, including process start | median 7.9 ms of 20 runs (min 7.5; earlier run 7.6); ~14 M beats/s | measured + derived |
| L5 | `Comparitor`, same beats | 0.22 s best of 3; ~0.5 M beats/s | measured |
| L5 | recomputation scripts | `kerber_lcl.py` 0.04 s; `interval_label_check.py` 0.55 s | measured |
| L6 | peak RSS: `bxb`; Python+numpy+`Comparitor` | ~1.6 MB; 52.4 MB | measured |
| L6 | MIT-format annotations | 220,044 B per 110,000 beats (~2 B each) | measured |
| L6 | binaries (static, `-g`) | `bxb` 329,512 B (text 109,895); `epicmp` 312,832 B | measured |
| L6 | device ROM/RAM/battery | not measured | — |

### 9. Comprehensibility and conceptual simplicity

- **C1: human comprehension.** "Sensitivity 95%" hides at least eleven parameters:
  - window width and endpoint inclusivity;
  - learning period;
  - reference VF and shutdown handling;
  - class folding;
  - pooled vs per-record aggregation;
  - episode-overlap rule;
  - segment length and transition exclusion;
  - preselection;
  - patient-disjoint splits;
  - interval construction.

  Legible behavior: `bxb -v` lists mismatches, `sumstats` prints both aggregates, and nonstandard options warn. Illegible behavior: `Comparitor`'s strict `<` contradicts its docstring; Figuera's code resamples a different unit than the paper says; and interval labels in the literature do not match the numbers. Running the tools is easy for an agent; knowing which convention a number embodies requires reading source.
- **C2: simplicity and orthogonality.** Every statistic is f(reference events, test events, matching relation, inclusion mask, aggregation unit). The conventions reduce to four orthogonal parameters:
  - matching relation: inclusive or exclusive window, or overlap >0 or ≥50%;
  - inclusion mask: learning period, VF, shutdown, artefact, transitions;
  - class map;
  - aggregation and resampling unit: beat, episode, segment, record or patient.

  One declarative scoring specification, consumed directly by code rather than through adapters, would make `bxb`, `epicmp`, `Comparitor` and segment-level ML evaluation ordinary instances. No examined tool shares such a specification (`Basis: derived`).

### 10. Validation coverage

- **V1: specification adequacy.** Kerber's table is the operative specification. Its LCLs are not reproducible by one construction, and the 2025 AHA summary disputes its NSR requirement and sample sizes. Boundary offsets 53/54/55 act as specification mutants that "kill" `Comparitor`'s documentation/implementation off-by-one. Mutation testing of detectors was not examined.
- **V2: differential checking.** `bxb` and `Comparitor` agree exactly at width 55 on 60- and 110,000-beat timelines and disagree at 54 (`Basis: execution`). Fuzzing and an independent re-implementation of `epicmp` were not examined.
- **V3: crash and physical faults.** Not applicable to the scoring tools. Device field reports show battery and power-off failures (DeLuca); fault injection was not examined.
- **V4: field replay and operators.** OHCA vs Holter data under one pipeline (Figuera: BER 4.4 vs 2.2); field audits (Zijlstra, SSED). Operator models appear only as counts (28 operator-caused incorrect shock advices, 149 disagreements, 8 off-button presses). Simulator/HIL testing was not examined.

## Boundaries

- **Not examined:**
  - full texts of Kerber, Thakor and Shah–Maisel;
  - IEC 60601-2-4 201.107 and Table 201.102, and the AMD2:2026 edition;
  - EC57:2012 clauses 3–4 and Annex A, including any CU-DB learning-period rule;
  - EC38, AAMI DF80/DF39 and FDA AED PMA guidance;
  - the AHA database and any PhysioNet signal data;
  - execution of `qrs.py`, `ecgdetectors.py` and MATLAB code;
  - re-evaluation of published features on `vfdb`/`cudb` under alternative segmentations and splits (design in **Revalidation**);
  - waveforms, paediatrics, human factors and logistics.
- **Unknown:**
  - the construction behind Kerber's LCLs (truncated Wald is a hypothesis that fails at n=30);
  - what the SSED Fine VF "90% CI" denotes;
  - whether Figuera's published results came from this code revision;
  - the interval method actually used in each Ruiz de Gauna Table 1 row;
  - whether EC57:2012 changed rules that `bxb`/`epicmp` take from 1998;
  - how many `cudb` episodes the 5-minute default affects.
- **Known not to apply:**
  - `bxb` beat statistics to `vfdb` (no beat labels);
  - Kerber goals as algorithm-only thresholds (EC57 is "not a performance standard"; Amann separates algorithm values from recommendations for whole systems);
  - QRS detectors as VF detectors.
- **Not established:**
  - that any commercial AED meets or misses the goals;
  - that the `Comparitor` behavior changed any published result;
  - that Figuera's segment-level resampling changes its conclusions (it typically narrows intervals, but this was not measured);
  - any software share of AED recalls.

## Evidence

All evidence was gathered 2026-11-21 (UTC); GitHub HEADs were resolved via the API that day.

- **`bemoody/wfdb@de6b1d3981d69060e6a4d1b4e86375fb0d3ed2d1`** (10.7.0; tarball sha256 `8fbcc215b4ecb6b15c0d2588658a1f7b3ab1629b3e0a7f189b823a7571397df5`):
  - `app/bxb.c` lines 25–35, 100–113, 177–211, 308–324, 427–455, 574–611, 800–852 and 1035–1050;
  - `app/epicmp.c` lines 160–285, 290–407, 455–523 and 947–983;
  - `app/sumstats.c` lines 156–184;
  - `doc/wag-src/epicmp.1` lines 71–94;
  - `lib/signal.c` `fstrtim`.
- **`MIT-LCP/wfdb-python@cc9f94fcc8bc938c6fb6cb40fb61c85b33e9404e`:** `evaluate.py` lines 47–278 and 402–553 (sha256 printed by the probe); `qrs.py` lines 108–137 and 460–468.
- **`berndporr/py-ecg-detectors@f39354cb686710f8e243e214b94fda0914fff656`:** `ecgdetectors.py` lines 45–55, 463–490 and 641–690.
- **`FelipeURJC/ohca-vs-public-dbs@4d799e936fea095db4aba3d08bfdc0aabffc29be`:**
  - `calculate_TCI.m` lines 27–142;
  - `bootstraping.m` lines 30–221;
  - `feature_selection.m` lines 55–77;
  - `bootstraping_per_ddbb.m` line 87;
  - `process_data.m` absent (HTTP 404).
- **DOIs verified against Crossref** (title, authors, venue, year, volume): 10.1161/01.CIR.95.6.1677; 10.1109/10.58594; 10.1007/BF02446668; 10.1088/0967-3334/25/5/007; 10.1186/1475-925X-4-60; 10.1371/journal.pone.0159654; 10.1155/2014/386010; 10.1016/j.resuscitation.2017.05.017; 10.1016/j.annemergmed.2011.07.022; 10.1001/jama.296.6.655; 10.1161/01.CIR.101.23.e215; 10.1109/51.932724; 10.1161/JAHA.124.039291; 10.2345/9781570204784. Verified against DataCite instead: 10.13026/C2F305, 10.13026/C22P44, 10.13026/C2X59M.
- **Regulatory and standards sources:**
  - eCFR versioner API (21 CFR 870.5310);
  - FederalRegister.gov API (FR Docs 2015-01619 and 2015-02049) and the govinfo text;
  - FDA SSED P160033 (`accessdata.fda.gov/cdrh_docs/pdf16/P160033b.pdf`);
  - IEC webstore publication 62752;
  - IEC 60601-2-4 sample pages;
  - ANSI EC57 preview pages.
- **Execution.** Scripts and recorded outputs are in `support/` (see `support/README.md`):
  - `build_wfdb.sh`;
  - `annotation_scoring_probe.sh` with `make_annotations.py`;
  - `comparitor_probe.py`;
  - `timing_probe.sh` with `make_big_record.py`;
  - `kerber_lcl.py`;
  - `interval_label_check.py`;
  - `tci_toy.py`.

## Revalidation

- **WFDB.** Diff `bxb.c` lines 177–211 and 814–831 and `epicmp.c` lines 238–267 and 966–967, then rerun `support/annotation_scoring_probe.sh`. Expect 48/60; 24/60 with `-w 0.1`; 61/61 vs 61/351; Gross 93.94 vs Average 74.17; episode Se 1/2 with +P 1/3.
- **wfdb-python.** Grep for `smallest_samp_diff < self.window_width` and `int(0.1 * fields["fs"])`, then rerun `support/comparitor_probe.py`. Expect tp 18/36/48 at widths 36/54/55.
- **Kerber.** If the full text becomes available, compare its table with SSED Table 5 and rerun `support/kerber_lcl.py` with any stated method.
- **Figuera.** Check the `datasample` resampling unit; patient-level resampling would draw from `unique(patient_id(idx_val))`.
- **Recommended re-evaluation (not run).**
  1. Download `vfdb` and `cudb`.
  2. Convert rhythm labels to VFON/VFOFF.
  3. Compute one fixed feature (e.g. TCI) on 4- and 8-s windows.
  4. Score (a) every 1-s step, (b) artefact-free single-rhythm segments only, (c) record- vs patient-wise splits (`mitdb` 201/202 together), and (d) with and without the 5-minute learning period.
  5. Report how Se, Sp and episode Se move.
- **Regulation.** Re-query the FederalRegister.gov API (docket FDA-2013-N-0234), the eCFR versioner API (§870.5310) and the IEC webstore (AMD2:2026).
