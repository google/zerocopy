# US AQI breakpoints before and after the 2024 revision, PM and ozone NowCast, PurpleAir correction, Canada's AQHI, and differential testing of open AQI implementations

## Summary

- **Normative algorithm (EPA Technical Assistance Document, TAD).** Truncate the concentration to the pollutant's precision (O3 3 decimals in ppm; PM2.5 and CO 1 decimal; PM10, SO2, NO2 integers), find the band with `BP_Lo <= C <= BP_Hi`, interpolate `I = (I_Hi - I_Lo)/(BP_Hi - BP_Lo) * (C - BP_Lo) + I_Lo`, round to the nearest integer, and report the maximum over pollutants. The TAD does not say how to round exact `.5` ties; its own worked example (125.5 -> 126) is satisfied by both half-up and half-even.
- **2024 revision (TAD EPA-454/B-24-002, unchanged in EPA-403/B-26-003).** The PM2.5 breakpoints changed: Good now ends at 9.0 (was 12.0) µg/m³; Unhealthy ends at 125.4 (was 150.4); Very Unhealthy ends at 225.4 (was 250.4). All pollutants now share one Hazardous band, 301+, anchored at the concentration for AQI 500 (PM2.5 325.4 µg/m³, PM10 604, CO 50.4 ppm, SO2 1004 ppb, NO2 2049 ppb, 1-h O3 0.604 ppm). Values above 500 continue on the same slope. Daily reporting changed from "at least five days each week" to "seven days each week".
- **NowCast.** For PM, the NowCast is a 12-hour weighted mean whose weight factor is `max(1 - range/max, 0.5)`, and 2 of the last 3 hours must be valid. For ozone, the NowCast predicts the 8-hour mean centred on the current hour from the previous 96 hourly values, refitted every hour on a 336-hour window, with a decision tree of fallbacks. At the pinned `USEPA/O3-Nowcast` revision the shipped example does not run: `RunNowcast_local_v2.r` fails to parse, and the function file the example sources has a signature that `GetNowcast.r` cannot call. With the original function file, the "PLS" model uses all 96 components and is numerically identical to ordinary least squares (max difference 2.1e-13 on the example data).
- **Open implementations, tested at every breakpoint boundary** (29,956 inputs). `python-aqi` matches an exact TAD reference except at exact `.5` ties, where it rounds half-even (12 tie concentrations disagree with half-up). At CO 3.3 ppm it returns 37 rather than half-even 38 because the 28-digit `Decimal` division leaves 37.4999…. Under its 2024 table it raises on any value above AQI 500 unless the caller passes `extrapolate=True`. `con2aqi` encodes only the pre-2024 table, uses `ceiling` instead of rounding, and does not truncate, so concentrations in the gaps between bands are pushed into the next category. Its floating-point breakpoints put 0.070 ppm 8-h O3 at AQI 98 (reference 100) and 0.085 ppm at 149 (reference 150). It also returns 51–100 for 1-h O3 below 0.125 ppm, where the table is blank.
- **Fire and Smoke Map sensor/monitor category agreement code.** It bins NowCast PM2.5 with right-closed breaks `c(-Inf, 9.0, 35.5, 55.5, 125.5, 225.5, Inf)`, which puts exactly 35.5, 55.5, 125.5 and 225.5 one category too low. On the repository's PurpleAir example data this affects 109 of 5,806,623 sensor NowCast hours, including 82 of the 7,162 hours that the TAD places in USG, all at exactly 35.5. The example data include 58 sensors with NowCast values of 1,000 µg/m³ or more. The tutorial's published table shows exact category agreement of 81.1% for PurpleAir and 82.8% for Clarity, and agreement within ±1 category of 98.57% and 99.91% (derived from the published counts).
- **Sensor correction and index design.**
  - The US-wide PurpleAir correction is `PM2.5 = 0.524·PA_cf1 − 0.0862·RH + 5.75` (RMSE 8 → 3 µg/m³, fitted on 24-h data).
  - Its 2022 extension switches to `4.21e-4·PA² + 0.392·PA + 3.44` above raw 611 µg/m³, with a rounded linear blend over 570–611 that leaves jumps of about 0.5 µg/m³.
  - The Fire and Smoke Map displays the extension for PurpleAir sensors.
  - Canada's AQHI adds the excess mortality risks of NO2, O3 and PM2.5 (3-hour means) on a 1–10+ scale instead of taking a maximum.
  - Health-based multipollutant indices showed more consistent associations with respiratory emergency visits than the AQI in New York and California studies.
  - About 54% of surveyed US adults knew of AQI alerts, and about 15% changed behaviour.

## Applicability

The report covers these subjects together:

- the US AQI as defined by three TAD editions. The copies examined are PDFs archived in the `python-aqi` repository at the pinned revision, identified by SHA-256 in **Evidence**. The pre-2024 table is TAD EPA-454/B-18-007, Table 5; the 2024 table is TAD EPA-454/B-24-002, Table 6, identical to EPA-403/B-26-003, Table 6.
- the 2024 particulate-matter NAAQS final rule, 89 FR 16202;
- two open implementations, compared with the TAD and with each other: `hrbonz/python-aqi` 1.1.0 (classes `EPA_2015` and `EPA_2024`) and `cran/con2aqi` 0.1.0, a read-only GitHub mirror of the CRAN archive;
- EPA's ozone NowCast code and white paper, `USEPA/O3-Nowcast`;
- EPA's Fire and Smoke Map (FASM) sensor-acceptance analysis code and example data, `USEPA/FASM-sensor-AQI-analysis`, which uses the PM NowCast from `MazamaScience/AirMonitor` 0.4.7;
- the peer-reviewed literature on sensor correction, index design and health and awareness evaluation, identified by DOI.

Execution results apply to the pinned revisions only, run with CPython 3.13.15, R 4.4.3 (conda-forge build) and the R packages zoo 1.9.0, plyr 1.8.9, pls 2.9.0 and imputeTS 3.4. These runs used a Linux x86-64 workstation; each was limited to 60 s and well under 1 GiB RSS, with 4 BLAS/OpenMP threads. The FASM results cover only the sensor side. Reproducing the monitor side requires AirNow monitor archives downloaded at run time by `AirMonitor::monitor_load`; these were not available here (see **Boundaries**). Statements about AirNow's production systems are documentation-level unless stated otherwise.

## Findings

### 1. Normative computation and the two tables

Basis: normative (TAD 2018 Table 5; TAD 2024/2026 Table 6 and its footnotes; TAD section "Calculating the AQI").

| Pollutant (averaging, unit) | Good 0–50 | Moderate 51–100 | USG 101–150 | Unhealthy 151–200 | Very Unhealthy 201–300 | Hazardous (pre-2024: 301–400 / 401–500) | Hazardous (2024: 301–500, AQI-500 anchor) |
|---|---|---|---|---|---|---|---|
| PM2.5 (24-h, µg/m³), pre-2024 | 0.0–12.0 | 12.1–35.4 | 35.5–55.4 | 55.5–150.4 | 150.5–250.4 | 250.5–350.4 / 350.5–500.4 | — |
| PM2.5, 2024 | 0.0–9.0 | 9.1–35.4 | 35.5–55.4 | 55.5–125.4 | 125.5–225.4 | — | 225.5–325.4 |
| PM10 (24-h, µg/m³) | 0–54 | 55–154 | 155–254 | 255–354 | 355–424 | 425–504 / 505–604 | 425–604 |
| O3 8-h (ppm) | 0.000–0.054 | 0.055–0.070 | 0.071–0.085 | 0.086–0.105 | 0.106–0.200 | not defined (use 1-h) | not defined |
| O3 1-h (ppm) | blank | blank | 0.125–0.164 | 0.165–0.204 | 0.205–0.404 | 0.405–0.504 / 0.505–0.604 | 0.405–0.604 |
| CO (8-h, ppm) | 0.0–4.4 | 4.5–9.4 | 9.5–12.4 | 12.5–15.4 | 15.5–30.4 | 30.5–40.4 / 40.5–50.4 | 30.5–50.4 |
| SO2 (1-h, ppb; ≥200 uses 24-h) | 0–35 | 36–75 | 76–185 | 186–304 | 305–604 (24-h) | 605–804 / 805–1004 (24-h) | 605–1004 (24-h) |
| NO2 (1-h, ppb) | 0–53 | 54–100 | 101–360 | 361–649 | 650–1249 | 1250–1649 / 1650–2049 | 1250–2049 |

Rules that implementations must encode, quoted or paraphrased from the TAD:
- Truncation happens before table lookup: "Ozone (ppm) – truncate to 3 decimal places; PM2.5 (µg/m3) – truncate to 1 decimal place; PM10 – truncate to integer; CO – 1 decimal; SO2, NO2 – integer". After truncation no concentration falls into a gap between bands such as 12.0–12.1.
- "Round the index to the nearest integer." Tie handling is not specified.
- Blank cells must be disregarded: 1-h O3 below 0.125 ppm, and 8-h O3 above 0.200 ppm, where AQI ≥ 301 is computed from 1-h O3. Footnote 3 (2024) / 4 (2018) says that 1-h SO2 does not define AQI ≥ 200; the 24-h SO2 average is used there. A day with max 1-h SO2 ≥ 305 ppb but 24-h SO2 < 305 ppb is fixed at exactly 200.
- 2024 footnote 4 and Q&A: "AQI values above 500 [are] based on the same linear slope as the AQI values between 301 and 500". The 2024 regulatory text (Appendix G 3.4.c) says that above the highest breakpoint "the last two breakpoints … may be used".
- The 2026 TAD corrects a typo in the 2024 TAD's worked example, which printed `0.78 − 0.071` and `0.14` for `0.078 − 0.071` and `0.014`. The tables are unchanged (Basis: source diff of the two extracted PDF texts).

Basis for the revision's impact: derived, by exact rational evaluation of both tables on the 0.1 µg/m³ PM2.5 grid (support `aqi_diff/out_table_shift.txt`). The category changes for 30 grid points (9.1–12.0, Good→Moderate), 250 points (125.5–150.4, Unhealthy→Very Unhealthy) and 250 points (225.5–250.4, Very Unhealthy→Hazardous). Index values change sharply above 55.4: 125.4 µg/m³ is 187 (old) versus 200 (new); 225.5 is 275 versus 301; 325.4 is 375 versus 500; 500.4 is 500 versus 849. For PM10, collapsing the two Hazardous bands changes values inside the category, for example 504 µg/m³ is 400 (old) versus 389 (new), without changing any category.

### 2. PM NowCast

Basis: normative (TAD "How the NowCast is calculated") + source (`AirMonitor` `R/monitor_nowcast.R`; `python-aqi` `aqi/nowcast.py`) + execution.

Algorithm, TAD steps 1–7: over the last 12 hourly values, `w = 1 - (max - min)/max`, raised to at least 0.5; then `NowCast = Σ c_i w^i / Σ w^i`, where `i` is hours ago and only valid hours are summed. The result is valid only if 2 of the last 3 hours are valid. As `w` approaches 0.5 the NowCast approaches a 3-hour weighting; as `w` approaches 1 it approaches a 12-hour mean.

| Aspect | AirMonitor 0.4.7 `.nowcast` / `monitor_nowcast` | python-aqi 1.1.0 `nowcast()` |
|---|---|---|
| Output precision | `trunc(newData*10^digits)/10^digits`, 1 decimal for PM (line 124) | exact `Fraction` converted to `Decimal`; truncated later when converted to an index |
| Negative readings | accepted; a weight from `min < 0` is clamped to ≥ 0.5 | `OutOfRangeError` for any negative reading in the window |
| `max == 0` | `0/0 → NaN` is dropped by `min(w, 1, na.rm=TRUE)`, so `w = 1` | `w = 1` |
| Short records | `includeShortTerm=TRUE` starts at hour 2 | a shorter list is padded with missing hours |
| AirNow forum example (12 h, one missing) | 28.409801 (documented in the source) | 28.40980136763… (execution) |

The two implementations agree on the documented example. They diverge on negative readings. The FASM PurpleAir example has 130,426 negative hourly values (minimum −2.87 µg/m³) and 113,004 negative sensor NowCast hours; `python-aqi` would refuse every window containing a negative reading (Basis: execution, support `fasm_category/out_python_aqi_nowcast_check.txt`, `out_port_full.txt`).

### 3. Ozone NowCast: white paper versus code

Basis: documentation (`WhitePaper.pdf`, Reff, Mintz and Naess) + source + execution (support `o3_nowcast/`).

Model: `y_t` is the 8-hour mean centred on hour `t`, computed with `rollapply(..., list(-4:3), align='center')`, so offsets −4…+3, valid if at least 6 of the 8 hours are present. Each training row regresses `y_t` on the 96 hourly values ending at `t` (the "inner window"). The model is fitted with `pls::mvr` on the rows of the 336-hour outer window that have a non-missing `y`, and the prediction for the current hour is the last row. Missing 1-hour values in the predictors are imputed with `imputeTS::na.ma`, but not in the target.

Decision tree in `GetNowcast.r` (MethodID is the code's own label):

| Condition, in code order | Output | MethodID |
|---|---|---|
| no valid hours | NA | 8 |
| valid hours < 252 (75% of 336) | surrogate `0.85*c + 4.5` from the latest of the last 3 valid hours | 3/5/7 (8 if none) |
| longest missing run > 7 hours | surrogate | as above |
| > 25% of 8-hour means missing | surrogate | as above |
| all values 0 | 0 | 1 |
| current hour missing | previous hour's stored NowCast, read from the AirNow database when `op.mode=T` (NA in local mode), else the one from 2 hours ago, else NA | 4 / 6 / 8 |
| otherwise | PLS prediction; negative values are clamped to 0 | 2 (1 if clamped) |

Discrepancies between the white paper and the code (Basis: derived from the two texts):
- The white paper states the surrogate condition as "a sequence of missing 1-hour O3 concentrations longer than 8 hours". The code uses `get.max.na.stream(tdata$Value) > 7`, and the same white paper's imputation condition says "longer than 7 hours".
- White-paper condition 3, "The current and previous 2 hours must not be NA", is not a PLS precondition in the code. The code reaches the PLS branch whenever the current hour is present.

Execution of the pinned revision. The example data are 336 hourly values, 2019-04-16 08:00 to 2019-04-30 07:00, 3 missing, range 3–63 (ppb units implied by the magnitudes).
- `Rscript Example.r` stops with `RunNowcast_local_v2.r:18:2: unexpected ')'`. Lines 13–18 of that file reference an undefined `i` and close a `})` that was never opened.
- `RunNowcast_local_v2.r` line 11 parses timestamps with `format = "%m/%d/%Y %H:%M"`, but `ExampleData.csv` uses `2019-04-16 08:00:00`; 336 of 336 timestamps become NA.
- `Example.r` sources `NowcastFun_Upd.r`. In that file `pls.nowcast` has no `rolling.mean.data` parameter (lines 89–96: `function(data, rollwindow = 336, mean.conc.window = list(-4:3), pls.window = 96, what.2.get = 'pred', num.cores = 2, show.progress = F)`). Yet `GetNowcast.r` line 84 calls `pls.nowcast(tdata$Value[i:(i+335)],rolling.mean.data=rolling.mean.data,pls.window=pls.window)`. Execution: `unused argument (rolling.mean.data = rolling.mean.data)`.
- With `NowcastFun.r` instead, whose signature at lines 68–75 includes `rolling.mean.data`, `GetNowcast` returns NowCast 19.58449091 with MethodID 2. The call took 1.50 s elapsed; the whole R process peaked at 231 MiB RSS. The surrogate would have given 16.4.
- `pls.now.fun` hard-codes `pls.window=96;` (line 10 of `NowcastFun.r`, 11 of `NowcastFun_Upd.r`), overriding its argument.
- `mvr` is called without `ncomp`; on 238 training rows it used 96 components (`kernelpls`). The full-component prediction equals `lm()` to 2.06e-13. The model in production code is therefore OLS on 96 lags, not a regularised PLS. Limiting the components changes the example prediction to 30.12 (1 component), 23.08 (2), 21.55 (3), 20.95 (5), 19.77 (10) and 19.65 (20) (Basis: execution).
- `fill = 'NA'`, a character string, in `rollapply` still yields a numeric vector with 7 `NA`s under zoo 1.9.0, so it is not a defect (Basis: execution).

The TAD says the ozone NowCast was implemented on August 1, 2019 and points to this repository. Whether AirNow's production code matches the pinned revision is unknown.

### 4. Differential test of the open implementations

Basis: execution (support `aqi_diff/`); source for the quoted lines.

Grid: for each of 7 pollutant/averaging series, every precision-grid value from 0 to the highest breakpoint of either table; each value plus half a precision step and plus 0.99 of a step, to exercise truncation and the gaps; plus −1 step and three values above the top. That is 29,956 inputs. The reference evaluates both tables in exact rational arithmetic after `Decimal` truncation, rounds half-up, and flags exact `.5` ties.

| Comparison | Agree | Disagree (non-tie) | Tie-only differences | Refusals where the reference has a value |
|---|---|---|---|---|
| python-aqi `EPA_2015` vs pre-2024 reference | all non-tie integer outputs | 0 | 36 inputs (12 concentrations) | none in range; above 500 the reference is "Beyond the AQI" (no value), and `extrapolate=True` returns e.g. PM2.5 750.6 → 665 |
| python-aqi `EPA_2024` (default) vs 2024 reference | all in-range | 0 | 21 inputs (7 concentrations; no PM2.5 ties exist on the 2024 grid) | 5,253 PM2.5 inputs > 325.4 and 3 per other pollutant raise `OutOfRangeError` |
| python-aqi `EPA_2024(extrapolate=True)` vs 2024 reference | 15,018 / 15,019 PM2.5 (the remaining one is the negative input, refused by both) | 0 | 21 inputs | 0 |
| con2aqi vs pre-2024 reference, on-grid inputs | e.g. PM2.5 2,522 / 5,005 | PM2.5 2,483 (+1, from `ceiling`); 8-h O3 2 (−1 and −2) | — | values above the top raise a "confirm that the unit" error |
| con2aqi vs pre-2024 reference, off-grid inputs | PM2.5 4,283 / 10,008 | category flips: 10 per pollutant (5 for 8-h O3, 6 for 1-h O3) | — | — |

The defects behind these numbers, quoted at the pinned revisions:
- **python-aqi tie rule**, `aqi/algos/base.py`: `rounding = ROUND_HALF_EVEN` (line 126) and `value = (aqihi - aqilo) / (bphi - bplo) * (_cc - bplo) + aqilo` (line 194) under the default 28-digit `Decimal` context. Ties are rounded half-even: PM2.5 0.6, 3.0, 5.4, 7.8 and 10.2 (pre-2024), CO 1.1, and 8-h O3 0.072, 0.076, 0.080, 0.084 and 0.153 give the lower integer. For CO 3.3 the division `50/4.4` is rounded at 28 digits, so the computed index is 37.49999999999999999999999999 and the result is 37 where half-up and exact half-even both give 38. Other tie concentrations computed exactly. Concentrations are truncated with `cc_rounding = ROUND_DOWN` (line 129), which matches the TAD.
- **python-aqi beyond-500**: the `EPA_2024` docstring cites the TAD's linear extension, but `iaqi(..., extrapolate=False)` is the default and raises `OutOfRangeError`. In smoke episodes PM2.5 24-h values above 325.4 µg/m³ are therefore errors unless callers opt in.
- **con2aqi rounding and truncation**, `R/con2aqi.R` line 74: `aqi=ceiling((ih[rank]-il[rank])/(bph[rank]-bpl[rank])*(con-bpl[rank])+il[rank])`, with `rank=which(con<=bph)[1]` (line 73) and no truncation. So 12.05 µg/m³ gives 51 (reference 50, Good→Moderate), 35.45 gives 101 (reference 100), and every gap between bands of every pollutant produces a category flip.
- **con2aqi floating-point breakpoints**, line 19: `bph=c(bpl[-1]-0.001,0.2)`. `0.071-0.001` is not equal to the literal `0.070` in binary floating point (R reports FALSE for the 2nd and 3rd 8-h O3 upper breakpoints), so 0.070 ppm falls into the 101–150 band and gives `ceiling(97.5)` = 98. Likewise 0.085 gives 149. The PM2.5 and CO breakpoints built the same way compare equal.
- **con2aqi blank cells and invalid input**: line 25 `bpl=c(0,0,0.125,...)` gives `bph=c(-0.001,0.124,...)`, so 1-h O3 0 → 51 and 0.1 → 91, where the TAD table is blank. Negative inputs are accepted (PM2.5 −5 → −20). Omitting `type` for O3 fails with `argument is of length zero`. The NO2 range error says "Please confirm that the unit of SO2 is ppb!" (line 69).
- **Shared semantic gap.** Both libraries key SO2 ≥ 305 ppb on a 1-hour series (`so2_1h`, `"so2"`), whereas the TAD defines those bands on 24-hour SO2, with the special rule that fixes the AQI at 200. The caller must supply the right average (Basis: source + normative).

Performance (L4; host class as in **Applicability**). Evaluating 29,956 × 4 python-aqi calls took 0.46 s wall in total, 11.5 MiB RSS. 29,956 con2aqi calls took 1.83 s, 72.7 MiB RSS for the R process. The exact reference took 1.02 s.

### 5. Low-cost sensor correction and smoke

Basis: documentation (peer-reviewed papers; EPA web pages) — see the literature notes integrated below.

| Source | Equation (PA = PurpleAir cf_1, A/B mean, µg/m³; RH = sensor RH, %) | Fitting data | Reported accuracy | Stated limits |
|---|---|---|---|---|
| Barkjohn, Gantt & Clements 2021 (Eq. 10) | `PM2.5 = 0.524·PA − 0.0862·RH + 5.75` | 50 sensors, 39 sites, 16 states, 2017-09-28 to ~2020-01-13. About 12,000 collocated 24-h pairs; median 7 µg/m³, max 24-h 109; 3.8% above 20 µg/m³. A/B valid if the channels differ by < 5 µg/m³ or < 61% | RMSE 8 → 3 µg/m³. 24-h AQI category: correct 91%, one category low 3%, one high 6% (leave-one-state-out) | 24-h averages only; little high-concentration data; bias possible below −12 °C and above 60 µg/m³; dust underestimated |
| Barkjohn, Holder, Frederick & Clements 2022 (Eqs. 1–3) | PA < 570: Eq. 1 (as above). 570 ≤ PA < 611: `w·Eq3 + (1−w)·Eq1`, `w = 0.0244·PA − 13.9`. PA ≥ 611: `4.21e-4·PA² + 0.392·PA + 3.44` | 25 sensors (one passage says 27 withholding iterations), with 2020 smoke collocations and nearby pairs within ≈ 3 km. Only 5 sensors exceed 500 µg/m³. Hourly A/B valid if within 5 µg/m³ or < 70% | Hourly NowCast AQI category correct 94%; < 1% off by more than one category. Hazardous category underestimated 12% of the time | Raw sensor response is nonlinear above ≈ 300 µg/m³; above ≈ 750 µg/m³ only 3 sensors, all RH < 24% |
| Holder et al. 2020 (Table 6, PA cf_1) | `PM2.5 = 0.51·PA − 3.21` (smoke-specific) | 3 sensor types, 6 deployments in 2018–2019; max hourly 295 µg/m³ | NRMSE 143.3% → 16.9%; MAE 66.2 → 7.61 µg/m³ | PA linear only up to ≈ 200 µg/m³; possible saturation |

- The EPA FASM technical page (last updated 2026-08-14) says PurpleAir data are shown "using the extended U.S.-wide correction" and Clarity data using "calibration model V2.1". The page does not print the equations.
- Derived from the published coefficients (support `correction/`): the rounded blend weight is 0.008 at PA = 570 and 1.0084 at PA = 611, not 0 and 1. The 2022 correction therefore jumps by +0.49 to +0.53 µg/m³ at 570 and −0.64 to −0.68 µg/m³ at 611 (RH 20–80%), although the paper describes a linear transition. At PA = 1000 and RH 50%, the extended correction gives 816.4 µg/m³ against 525.4 from Eq. 1.
- Both correction papers set their targets against **pre-2024** PM2.5 breakpoints: Barkjohn 2022's NMBE target is checked "up to … 'Hazardous' (250.4 µg/m3)", and Holder 2020 uses 150.5–250.5. Their category-agreement percentages therefore cannot be carried over to the 2024 table without re-binning (Basis: derived).

### 6. Category-agreement method of the Fire and Smoke Map protocol code

Basis: source (`R/functions_for_AQI_barplots.R`, `R/template_for_sensor_vs_monitor.R`) + documentation (rendered `docs/tutorial.html`) + execution.

Pipeline:
1. `findAdjacentPairs` pairs each sensor with its nearest AirNow monitor and keeps pairs with `airnow_closestDistance <= radius`; the template passes 1000 m.
2. Both series go through `monitor_nowcast(includeShortTerm = TRUE)`.
3. `create_AQI_unlisted` bins each paired hour with `.bincode(x, c(-Inf, 9.0, 35.5, 55.5, 125.5, 225.5, Inf))` (lines 90–93; `.bincode` defaults to right-closed intervals). It drops NA pairs, and takes the monitor category from column 1 and the sensor category from column 2 of `AirMonitor::monitor_combine(airnow_mon, sensor_mon)`.
4. Plots and tables are drawn of `sensor − monitor` category differences, overall and by monitor category. Dashed threshold lines default to 5% (±1 category) and 1% (±2 or more) in the combined plot, and 30% and 1% in the per-category plots.

Breakpoint defect (Basis: source + execution). After `monitor_nowcast` truncation to 0.1, the values 35.5, 55.5, 125.5 and 225.5 are exactly representable and are binned into the lower category; the TAD puts them in the higher one. Every other value bins correctly (the first break, 9.0, is right for Good ≤ 9.0). On `data/purpleair_data.csv` (7,809 sensors × 888 hours, 2024-08-28 to 2024-10-03), sensor NowCast hours were computed with AirMonitor's own `.nowcast`, which ran in R on 300 sensors in 2.19 s. A vectorised Python port reproduced the R result on all 266,400 cells of those 300 sensors and computed all sensors in 9.8 s wall (409 MiB RSS). Results: 5,806,623 valid NowCast hours; FASM category ≠ TAD category for 109 of them (82 at 35.5, 24 at 55.5, 3 at 125.5). TAD category counts (1…6): 5,160,574; 618,915; 7,162; 4,064; 759; 15,149.

Example-data quality (Basis: execution). Hourly values range from −2.87 to 18,580.8 µg/m³. 14,853 hourly values are ≥ 1,000, and several sensors sit near 12,116 µg/m³ for every reported hour. 58 sensors reach a NowCast ≥ 1,000, and 14,841 NowCast hours are ≥ 1,000. The minimum −2.87 equals `5.75 − 0.0862 × 100`, the US-wide correction evaluated at 0 µg/m³ raw and 100% RH. This suggests, but does not establish, that the example data are already corrected (Basis: derived; see **Boundaries**).

Published tutorial results (Basis: documentation; percentages derived from the printed counts, rows = sensor category, columns = monitor category):

| Example | Paired hours | Exact agreement | Within ±1 | ≥ 2 categories apart | Note |
|---|---|---|---|---|---|
| Clarity, 2023-05-30 to 2023-09-29 | 31,361 | 25,966 (82.80%) | 31,333 (99.91%) | 28 (0.09%) | — |
| PurpleAir, 2024-08-28 to 2024-10-03 | 107,830 | 87,478 (81.12%) | 106,286 (98.57%) | 1,544 (1.43%) | 1,461 sensor-Hazardous hours, 1,412 of them while the monitor reads Good or Moderate |

The PurpleAir table includes one monitor hour in category 6, whereas the tutorial source comments that the maximum monitor category is Very Unhealthy. The two artifacts are inconsistent at the pinned revision.

### 7. Index designs and health/awareness evaluations

Basis: documentation (peer-reviewed papers; government pages).

- **US AQI design.** Each pollutant's sub-index is computed and the maximum is reported, so only the worst pollutant counts. Plaia and Ruggieri (2011; abstract only) classify indices into those that "consider the conjoint effect of pollutants" and those "only based on the actual most dangerous pollutant"; the US AQI belongs to the second class.
- **Canada AQHI.** Stieb et al. (2008; abstract only) describe the AQHI as the "sum of excess mortality risk associated with individual pollutants … adjusted to a 0-10 scale, … calculated hourly on the basis of trailing 3-hr average pollutant concentrations", using NO2, O3 and PM2.5 from single-pollutant mortality models. The numeric formula comes from secondary government sources (a 2010 British Columbia report, p. 3, and a 2013 Public Health Ontario review): `AQHI = (10/10.4)·100·[(e^(0.000871·NO2) − 1) + (e^(0.000537·O3) − 1) + (e^(0.000487·PM2.5) − 1)]`, with 3-hour means in ppb for the gases and µg/m³ for PM2.5. Federal ECCC pages give the 1–10+ scale and bands (low 1–3, moderate 4–6, high 7–10, very high 10+), and state that during wildfire smoke "we only use PM2.5" hourly. Derived examples: NO2 20 ppb, O3 30 ppb and PM2.5 10 µg/m³ give 3.72; the same PM2.5 alone at 150 µg/m³ gives 7.29. The AQHI is additive across pollutants and has no breakpoint table, so there are no truncation or tie rules to get wrong; it does need an exponent per pollutant and a 3-hour rolling mean.
- **Health association of index values.**
  - Perlmutt and Cromar (2019; abstract only) fitted coefficients on Bronx and Queens respiratory emergency-department visits in 2005–2010 and evaluated them in 2011–2013. A log-transformed multipollutant health-based index (NO2, O3, PM2.5, SO2) had RR 1.03 (95% CI 1.01–1.05) in both the high- and low-O3 seasons; the AQI was not significant in the high-O3 season (1.00, 0.99–1.02).
  - Cromar et al. (2020; full text, tables not rendered) studied 25 California counties (32,708,938 adults; 1,373,165 respiratory ED visits, 2012–2014). The AQI was positively associated in cooler months (average RR 1.03, 1.02–1.04, per IQR), when it is highly correlated with PM2.5 (Spearman 0.89–0.98). Warm-season results were mixed (Riverside 0.98, 0.96–0.99). In the South Coast AQMD a health-based index had RR 1.02 in both seasons against 1.00 (0.98–1.01) for the AQI. The authors note insufficient power to test AQI value groupings, so risk below AQI 100 was not resolved.
- **Awareness.** Mirabelli, Ebelt and Damon (2020; full text) surveyed 12,396 adults in the 2016–2018 SummerStyles waves: 53.9% were aware of AQI or alerts, 29.2% thought or were told air was bad in the past 12 months, and 14.7% changed behaviour. In counties with ≥ 15 days at AQI ≥ 101 per year the figures were 61.3%, 43.1% and 23.1%, against 49.9%, 21.4% and 10.2% with 0 days (adjusted prevalence ratio for behaviour change 2.27, 1.94–2.67). All data are self-reported.

### 8. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring/maintenance | size of the implementations | python-aqi `aqi/` 1,135 lines of Python; con2aqi 91 lines of R; O3-Nowcast `.r` files 464 lines (5 files); FASM `R/` 853 lines | measured (`wc -l`) |
| L1 | person-months, LLM effort | not measured | — |
| L2 toolchain build | R 4.4.3 + 4 packages (conda environment) | 1,490,492 KiB (≈1.42 GiB) on disk; build/install time not measured | measured (`du -sk`) |
| L3 latency | O3 NowCast for one hour (fit + predict on a 336-h window) | 1.50 s elapsed inside R; 2.11 s wall per process | measured |
| L3 | python-aqi import | 0.02 s, 10.8 MiB RSS | measured |
| L4 throughput | AQI per value: python-aqi | ≈ 3.8 µs (0.46 s / 119,824 calls) | derived from measurement |
| L4 | con2aqi per value | ≈ 61 µs (1.83 s / 29,956, including R startup) | derived from measurement |
| L4 | PM NowCast, all sensors (port) | 6.9 M sensor-hours in 9.8 s wall | measured |
| L5 proof/certificate checking | — | not applicable (no certificates in this domain) | — |
| L6 memory/disk | O3 NowCast R process peak RSS | 231 MiB | measured |
| L6 | FASM port peak RSS | 409 MiB (R subset run: 373 MiB) | measured |
| L6 | installed python-aqi | 120 KiB; example PurpleAir CSV 50,037,414 bytes | measured |

AirNow production latency, throughput and energy: not measured.

### 9. Comprehensibility and conceptual simplicity (C1–C2)

- **C1.** The TAD algorithm needs about 5 concepts: truncation precision, band lookup, linear interpolation, rounding, and the maximum over pollutants. Its hidden traps are specifically the ones the differential test exposed: tie rounding is unspecified; truncation creates gaps between bands that only matter if an implementation skips truncation; blank cells and the 1-h/24-h SO2 split change which input series is legal; and Hazardous values above 500 are extrapolated. A reader can audit each table cell locally. Readers cannot audit the ozone NowCast in the same way: it is a 96-coefficient regression refitted every hour, its numeric result has no closed form, and the shipped example does not run.
- **C2 (model refinement).** Every rule above is an instance of one monotone step function: `category(C) = max{k : BP_Lo[k] <= trunc(C)}` on half-open intervals `[BP_Lo[k], BP_Lo[k+1])`. Encoding the table as **lower bounds only**, with truncation applied once at input, makes the gap cases and the FASM `.bincode` mistake impossible by construction. Encoding upper bounds produced the FASM, con2aqi and float defects. The same representation also covers the 2024 single Hazardous band with its "beyond 500" slope: the last band simply has no upper bound. Blank cells become "no lower bound for this series", and the SO2 split becomes a different input series rather than a special case.

### 10. Validation coverage (V1–V4)

- **V1 specification adequacy.** No EPA-published test vectors were found beyond the TAD's 5 worked examples, and 2 of those (125.5 → 126) are ties that do not discriminate between rounding rules. `python-aqi` ships a legacy-regression JSON and version tests. The FASM code has no unit test of the break vector. `con2aqi` has no tests in the archive. The 29,956-point boundary grid used here is a reusable oracle (support `aqi_diff/`).
- **V2 differential testing.** `con2aqi` disagrees with the exact reference on 8,208 of 15,019 PM2.5 grid inputs, and so with `python-aqi`, which matches the reference outside ties. All of them are +1, which is what `ceiling` plus missing truncation predicts. Disagreements between `python-aqi` and the reference are confined to the 36 tie inputs (pre-2024 table).
- **V3.** Not applicable (no concurrency or hardware-leakage concern).
- **V4 field and human validation.** Sensor-versus-monitor category agreement is the deployed field check. Its thresholds and the published example tables are given in Finding 6. Health and awareness evaluations are in Finding 7.

## Boundaries

- **Not examined:** the monitor side of the FASM agreement analysis (needs AirNow archives fetched by `AirMonitor::monitor_load`); whether `MazamaTimeSeries::mts_combine`, called by `monitor_combine`, preserves argument order, on which the FASM code's column-1-monitor / column-2-sensor assumption relies; AirNow's production NowCast and AQI code; PM10 and ozone NowCast use on the FASM; `python-aqi` MEP (China) classes; the `clarity_data.csv` example.
- **Unknown:** whether `purpleair_data.csv` holds raw or corrected values. The −2.87 minimum is consistent with the US-wide correction at RH = 100%, but no file documents this. Also unknown: whether EPA intends half-up or half-even rounding of ties.
- **Known not to apply:** the PLS-equals-OLS identity holds only when `ncomp` is left at its default and there are at least as many training rows as predictors. It is not a statement about other `pls` settings.
- **Unsupported:** `con2aqi` does not support the 2024 table, values above AQI 500, or a `type` default for ozone. `python-aqi` does not implement the ozone NowCast.
- **Attractive but unsupported conclusions:** the 109 mis-binned sensor hours do not show that any FASM acceptance decision changed. The R/Python agreement on the NowCast covers 300 sensors, not all 7,809, in R. The differential grid covers single-pollutant sub-indices, not the multi-pollutant maximum or the SO2 200-fixing rule.

- **Literature access limits:**
  - Stieb et al. 2008, Plaia & Ruggieri 2011 and Perlmutt & Cromar 2019 were read as abstracts only.
  - The AQHI coefficients are taken from provincial and agency documents, not from the Stieb full text.
  - Tables 1–2 of Barkjohn 2021 and Tables 2–3 of Cromar 2020 did not render, so per-IQR values and AQI-unit risks were not examined.
  - The FASM Data Acceptance Protocol PDF (its file name suggests a 2026-06-16 version) could not be retrieved, so its Table 4 thresholds were **not examined directly**. The 5%/1% (overall) and 30%/1% (per category) values come from the repository tutorial, which calls them "proposed" and "aligned with … Table 4".
- **Unknown:** how AirNow handles negative or extreme corrected sensor values before display; whether the 2024 Appendix G clause 3.4.c ("the last two breakpoints … may be used" above the top breakpoint) is applied identically by AirNow.

## Evidence

Observation date for all repository, execution and literature evidence: 2026-11-21 (UTC).

Pinned repositories (resolved with the GitHub API `commits/HEAD`):
- `hrbonz/python-aqi` @ `8206df05b009a48f8ce4a9a4a1a3cf70143ffc82` (package 1.1.0): `aqi/algos/epa.py` (classes `EPA_2012`, `EPA_2015`, `EPA_2024`, lines 15–205), `aqi/algos/base.py` (lines 109–239), `aqi/nowcast.py` (lines 52–121), `docs/versions.rst`. Archived TAD PDFs with SHA-256: `docs/standards/epa-tad-2018-09_EPA-454-B-18-007.pdf` `173f8d86…46449`; `docs/standards/epa-tad-2024-05_EPA-454-B-24-002.pdf` `2c5bd330…0ae290`; `docs/standards/epa-tad-2026-05_EPA-403-B-26-003.pdf` `b69de26a…5e0c`. The full hashes are in `support/README.md`.
- `cran/con2aqi` @ `5fc7a0901481f0c217d3cd598903532327353925` (0.1.0, CRAN publication 2018-08-20): `R/con2aqi.R` lines 13–76; `DESCRIPTION` cites the May 2016 TAD.
- `USEPA/O3-Nowcast` @ `5d3c32c04eeaae3a1ca1bc487c311ca7bf46bf6f`: `GetNowcast.r` (lines 3–110), `NowcastFun.r` (8–95), `NowcastFun_Upd.r` (8–131), `RunNowcast_local_v2.r` (4–21), `Example.r`, `ExampleData.csv`, `WhitePaper.pdf` (SHA-256 `40e192b8d6df4df5219efef429880a7598183b48f80582fce75ae9103de2943d`).
- `USEPA/FASM-sensor-AQI-analysis` @ `58a880131e4106d5faca68c1021f65f6e04b0a1a`: `R/functions_for_AQI_barplots.R` (lines 27–157, 181–221), `R/template_for_sensor_vs_monitor.R` (lines 57–98, 136–162), `data/purpleair_data.csv`, `docs/tutorial.Rmd`, `docs/tutorial.html` (printed `addmargins` tables).
- `MazamaScience/AirMonitor` @ `decb3d7a8039f73a65ce33bf736e6cb1a4356b28` (0.4.7): `R/monitor_nowcast.R` (lines 67–233), `R/monitor_combine.R` (lines 62–110).

Normative documents (no DOI assigned):
- EPA TAD EPA-454/B-18-007 (Sept 2018), EPA-454/B-24-002 (May 2024) and EPA-403/B-26-003 (May 2026): the copies archived in `python-aqi` above, text extracted with pdfminer.six.
- 89 FR 16202–16406, 2024-03-06, FR Doc 2024-02637, read on govinfo.gov (`FR-2024-03-06/html/2024-02637.htm`): effective 2024-05-06; Table 2 (PM2.5 sub-index); Appendix G sections 2.3, 3.4 and footnote 4.

Peer-reviewed sources. Every DOI was checked against the Crossref REST API (`api.crossref.org/works/<doi>`) on 2026-11-21; title, authors, venue, volume and pages matched:
- Barkjohn, Gantt, Clements, *Atmos. Meas. Tech.* 14(6):4617–4637, 2021, doi:10.5194/amt-14-4617-2021 (full text, publisher HTML).
- Barkjohn, Holder, Frederick, Clements, *Sensors* 22(24):9669, 2022, doi:10.3390/s22249669, with its correction notice *Sensors* 24(24):7871 (2024), which does not change Eqs. 1–3.
- Holder, Mebust, Maghran, McGown, Stewart, Vallano et al., *Sensors* 20(17):4796, 2020, doi:10.3390/s20174796.
- Stieb, Burnett, Smith-Doiron, Brion, Shin, Economou, *J. Air Waste Manag. Assoc.* 58(3):435–450, 2008, doi:10.3155/1047-3289.58.3.435 (PubMed abstract). AQHI formula from British Columbia Ministry of Healthy Living and Sport, *Air Quality Health Index Variation across British Columbia* (2010), p. 3, and Public Health Ontario, *Review of Air Quality Index and Air Quality Health Index* (2013).
- Plaia, Ruggieri, *Rev. Environ. Sci. Bio/Technol.* 10(2):165–179, 2011 (Crossref online date 2010-12-14), doi:10.1007/s11157-010-9227-2 (abstract).
- Perlmutt, Cromar, *Atmos. Environ.* 202:1–7, 2019, doi:10.1016/j.atmosenv.2019.01.011 (abstract).
- Cromar, Ghazipura, Gladson, Perlmutt, *PLOS ONE* 15(11):e0242031, 2020, doi:10.1371/journal.pone.0242031.
- Mirabelli, Ebelt, Damon, *Environ. Res.* 183:109185, 2020, doi:10.1016/j.envres.2020.109185 (PMC7182097).
- Web pages: EPA "Technical Approaches for the Sensor Data on the AirNow Fire and Smoke Map" (last updated 2026-08-14); ECCC AQHI "About" page (page date 2026-10-14).

Execution environment: CPython 3.13.15 with numpy 2.5.4 and pandas 3.1.1; R 4.4.3 (conda-forge) with zoo 1.9.0, plyr 1.8.9, pls 2.9.0 and imputeTS 3.4. All probe scripts and their raw outputs are in `support/` (see `support/README.md`).

## Revalidation

- **Tables:** diff the TAD tables against `support/aqi_diff/aqi_reference_and_grid.py` (`OLD` and `NEW` dictionaries). A future TAD edition with new breakpoints needs a new dictionary and a new rerun.
- **python-aqi:** `pip install <repo tarball at revision>`, then run `aqi_reference_and_grid.py <out>`, `run_python_aqi.py <out>`, `compare.py <out>` and `ties.py <out>`. The finding holds if non-tie disagreements are 0 and CO 3.3 still gives 37. Changing the `Decimal` context or the `rounding` attribute changes the tie results.
- **con2aqi:** `Rscript run_con2aqi.R R/con2aqi.R <out>` and `Rscript edge_con2aqi.R R/con2aqi.R`. A single discriminating check is `con2aqi("o3", 0.070, "8h")`: 98 means the float-breakpoint defect is still present.
- **O3 NowCast:** `Rscript Example.r` in a checkout (a parse error at `RunNowcast_local_v2.r:18:2` means it is unchanged). Then `Rscript o3_harness.R <checkout> orig` (expect 19.58449091 and `max|diff| ~ 1e-13` versus `lm`) and `... upd` (expect the unused-argument error).
- **FASM:** `Rscript fasm_sensor_nowcast.R <AirMonitor>/R/monitor_nowcast.R data/purpleair_data.csv 300 <out>`, then `python3 fasm_port.py data/purpleair_data.csv <out>/r_nowcast_subset.csv 300`. Expect 109 mismatches. Alternatively, `grep -n "breaks <-"` in `R/functions_for_AQI_barplots.R`: a vector of lower bounds used with `right = FALSE`, or upper bounds 9.0/35.4/55.4/125.4/225.4 with `right = TRUE`, would fix the defect.
