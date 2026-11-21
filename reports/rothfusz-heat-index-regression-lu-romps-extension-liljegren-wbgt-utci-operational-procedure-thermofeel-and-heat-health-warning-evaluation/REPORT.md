# Heat-stress index computation and its software: Steadman/Rothfusz heat index and NWS adjustments, the Lu–Romps extension, Liljegren WBGT versus approximations, the UTCI polynomial, divergence among open implementations, and heat-warning evaluations

## Summary

- **The US heat index is three different things that share a name.** (1) Steadman's 1979 apparent temperature is the output of an iterative steady-state thermoregulation model of an idealized walking, partly clothed adult in shade, tabulated only where the model is physical. (2) Rothfusz 1990 is a 9-term least-squares polynomial fitted to Steadman's table (stated error ±1.3 °F, no validity range in the attachment itself). (3) The NWS operational algorithm wraps the polynomial with a simple-formula branch below about 80 °F and two humidity adjustments. Libraries implement different subsets of (2)–(3), and the extended index of Lu and Romps 2022 re-solves (1) everywhere.
- **The NWS switch rule is ambiguous, and open implementations resolve it differently.** The WPC text says "the simple formula is computed first and the result averaged with the temperature. If this heat index value is 80 degrees F or higher, the full regression … is applied." thermofeel switches on `(A+T)/2 >= 80`. weathermetrics, a conversion of the NWS online calculator's JavaScript, switches on `A > 79`, and MetPy on `A >= 79`, where `A` is the simple formula. Executed over 11,211 grid points, these rules disagree by up to **2.25 °F** (T = 79 °F, RH = 93 %) in a band of T = 77–80.5 °F. MetPy also subtracts the low-humidity adjustment from simple-formula values (up to **1.37 °F** at T = 81 °F, RH = 0 %). Basis: source + execution.
- **Two libraries ship the bare Celsius Rothfusz polynomial with no NWS adjustments or low-temperature branch.** These are pythermalcomfort `heat_index_rothfusz` and thermofeel `calculate_heat_index_simplified`. Their Celsius coefficients equal the Fahrenheit polynomial to 2.5e-5 °F, but they depart from the NWS algorithm by up to 9.4 °F within T ≥ 70 °F. Below the fitted range the bare polynomial is wild: +426 °F above air temperature at T = 0 °F, RH = 95 %. This matches the >40 °C cold-weather error Anderson et al. report for the uncorrected polynomial. pythermalcomfort returns NaN below 27 °C by default. thermofeel returns air temperature at or below 20 °C. Basis: source + execution + documentation.
- **Risk categories differ, as well as values.** pythermalcomfort bins the heat index at 27/32/41/54 °C (80.6/89.6/105.8/129.2 °F). The NWS office table used for public risk communication bins at 80/90/103/125 °F. For one and the same index value, 703 of 11,211 grid points get a different category. Example: a heat index of 103–105.8 °F is NWS "Danger" but pythermalcomfort "extreme caution". Basis: source + documentation + execution.
- **Lu–Romps extended heat index.** It matches Steadman to <1 K where Steadman is defined. Lu and Romps report that the NWS chart is biased low by up to 28 °F (16 K). The pythermalcomfort port, measured against a transcription of the NWS algorithm on the chart domain, reproduces a +28.9 °F gap (T = 85.5 °F, RH = 100 %). The polynomial extrapolation exceeds the extended index at extreme temperature (−36.6 °F at T = 110 °F, RH = 100 %). The port matches its upstream reference values to 2.2e-6 K, although its own test only asserts 1 K. Basis: documentation + execution.
- **WBGT approximations and the explicit Liljegren model.** In the shade/night scenario on a synthetic grid, the Australian simplified WBGT (sWBGT) exceeds thermofeel's Liljegren WBGT by 4.6–19.3 °C. In strong sun it ranges from −3.9 to +16.4 °C. It changes the KNMI 0–10 heat-force level at 68 of 100 night points and 33 of 100 sun points. This agrees in direction with Kong and Huber's recommendation to discontinue sWBGT, and with the BoM's own caveat about night-time overestimation. Basis: execution (synthetic inputs) + documentation.
- **UTCI is one 210-coefficient degree-6 polynomial in four variables, approximating the UTCI-Fiala model's output.** pythermalcomfort and thermofeel agree to 1.5e-11 °C when given the same vapour pressure. They differ in input handling. pythermalcomfort returns NaN outside the official input checks (180 of 1,440 grid points). thermofeel extrapolates silently, giving 72.6 °C at 40 °C, 90 % RH. Its dew-point path mixes two saturation-vapour formulas, an effect of ≤0.013 °C. Basis: source + execution.
- **Warning-system evidence is weak and setting-specific.** Ebi et al. estimate 2.6 lives saved per warning day (117 in total) for Philadelphia. Toloo et al. found limited research. Weinberger et al. found no association between NWS heat alerts and lower mortality among US Medicare beneficiaries (RR 1.005, 95 % CI 0.997–1.013). Basis: documentation (abstracts; see Evidence for retrieval limits).

## Applicability

**Subjects and their relationship.** The report compares four independent open implementations of overlapping index families at pinned commits:
- pythermalcomfort `a0e7ae2a9a0178f24b33fdd75f06f27e9f00ba76` (package version 4.8.1; the repository was transferred and is cited under its current owner);
- thermofeel `53437e0e47fb428c452d0f418b68fb46ba802a22` (2.3.0);
- weathermetrics `429ee9a4410c6c0c00d209a32ae8e52a0edfa4cc` (last commit 2017-05-18);
- MetPy `5edfa0186fb0d01ef6d29319c6c2a496a888fb28`.

It interprets them through the normative or defining documents that each claims to implement:
- Rothfusz 1990;
- the NWS Weather Prediction Center equation page;
- the NWS office risk table;
- Lu–Romps 2022;
- Liljegren et al. 2008, via thermofeel's transcription;
- Bröde et al. 2012;
- the BoM simplified WBGT.

The warning-evaluation papers are included because their exposure definitions depend on these computations, not because any library implements them.

**Exactly what was executed.** The pythermalcomfort, thermofeel and MetPy functions were installed from the pinned source tarballs and executed as shipped (CPython 3.13.15, numpy 2.5.4, numba 0.68.1, x86-64 Linux). weathermetrics is R code; R was not available. Its `heat.index.algorithm` was transliterated line by line into Python and executed, and is labelled `wm_translit`. The R wrapper's default rounding to whole degrees was not reproduced. The NWS algorithm was transcribed from the WPC page text (`nws_literal`), not taken from NWS software. All meteorological inputs are synthetic grid points; no station or reanalysis records were processed. The grids include physically extreme combinations, for example 45 °C at 90 % RH, a dew point above 42 °C. Maxima over the grid therefore bound implementation disagreement, not field error.

**Scope boundaries.** The comparisons cover:
- heat index from temperature and relative humidity;
- WBGT from temperature, humidity, pressure, 10 m wind and shortwave radiation;
- UTCI from temperature, mean radiant temperature, 10 m wind and humidity.

They exclude:
- indoor/occupational WBGT measured with physical sensors (pythermalcomfort `wbgt` only combines measured `twb`, `tg`, `tdb` by the ISO 7243 weights 0.7/0.2/0.1 or 0.7/0.3);
- wind-chill and cold indices;
- the full UTCI-Fiala model.

Results are claimed only for the pinned revisions; revalidation should diff the cited line ranges rather than assume continuity.

## Findings

### 1. Steadman's model, the Rothfusz regression, and what "the heat index" assumes

Rothfusz 1990 lists the fixed assumptions of Steadman's model that the regression silently inherits:

| Parameter | Value |
|---|---|
| Ambient vapour pressure reference | 1.6 kPa |
| Person | 5′7″, 147 lb |
| Effective radiating area | 0.80 |
| Clothing cover | 84 % (long trousers, short-sleeved shirt) |
| Core temperature | 98.6 °F |
| Core vapour pressure | 5.65 kPa |
| Metabolic output | 180 W m⁻² (walking 3.1 mph) |
| Effective wind speed | 5 kt |
| Sweat | "uniform and not dripping" |

The fitted equation, with T in °F and R in integer percent, is:

```text
HI = -42.379 + 2.04901523 T + 10.14333127 R - 0.22475541 T R - 6.83783e-3 T^2
     - 5.481717e-2 R^2 + 1.22874e-3 T^2 R + 8.5282e-4 T R^2 - 1.99e-6 T^2 R^2
```

Rothfusz states an error of ±1.3 °F and calls it an "ersatz" equation. The attachment gives no validity domain and no adjustments; both come later from the NWS. Basis: normative (technical attachment text).

Anderson et al. 2013 state that Steadman's apparent temperature is the temperature that would feel the same at a dew point of 14 °C. Steadman published two tables, by RH and by dew point, that do not cover cool or cold weather. Lu–Romps 2022 add that the index is undefined where the model becomes unphysical. At 80 % RH it is defined only for 288–304 K (59–88 °F). Basis: documentation.

### 2. The NWS operational algorithm and its ambiguous switch

The WPC page (accessed 2026-11-21) defines:
- **Low-humidity adjustment.** If RH < 13 % and 80 ≤ T ≤ 112 °F, subtract `[(13−RH)/4]·sqrt{[17−|T−95|]/17}`.
- **High-humidity adjustment.** If RH > 85 % and 80 ≤ T ≤ 87 °F, add `[(RH−85)/10]·[(87−T)/5]`.
- **Simple formula.** `A = 0.5·{T + 61.0 + [(T−68.0)·1.2] + (RH·0.094)}` applies where the regression "is not appropriate", which is a heat index below about 80 °F.
- **Switch.** "In practice, the simple formula is computed first and the result averaged with the temperature. If this heat index value is 80 degrees F or higher, the full regression equation along with any adjustment as described above is applied."
- **Domain.** "The Rothfusz regression is not valid for extreme temperature and relative humidity conditions beyond the range of data considered by Steadman."

Basis: normative (operational documentation).

`A` already equals the average of T and a linear Steadman fit, so "averaged with the temperature" admits two readings:
- **R1:** average again and switch on `(A+T)/2 ≥ 80`;
- **R2:** the averaging *is* the 0.5 factor, so switch on `A` near 80.

Anderson et al. say weathermetrics was converted "with permission from the NWS" from the JavaScript of the NWS online calculator. Its `A > 79` rule is therefore evidence of the rule the calculator used. The probe found that the R1 transcription reproduces the NWS office's published examples:

| T, RH | Probe (R1) | NWS office example |
|---|---|---|
| 96 °F, 65 % | 121.03 °F | 121 °F |
| 100 °F, 55 % | 123.64 °F | 124 °F |
| 100 °F, 15 % | 95.85 °F | 96 °F |

Those examples lie above the switch region, so they do not discriminate R1 from R2. Basis: normative + documentation + derived.

### 3. What each open implementation computes

| Implementation (pinned path:lines) | Formula | Low-T branch | Switch to regression | Adjustments | Out-of-range behaviour | Input / output |
|---|---|---|---|---|---|---|
| weathermetrics `R/heat_index.R:156-186` (`heat.index.algorithm`) | °F Rothfusz | `t <= 40` → `hi <- t` (l.161–162) | `hi > 79` on `A` (l.166) | Inside regression branch only. Low-humidity uses `rh <= 13` (l.172); at RH = 13 the adjustment is 0. | RH outside 0–100 → NA with warning (l.95–98) | °F default, `temperature.metric="celsius"` converts. **Default `round = 0`** (l.78, applied l.108): integer output. |
| MetPy `src/metpy/calc/basic.py:235-355` (`heat_index`) | °F Rothfusz, RH as fraction | `T <= 40 °F` → T (l.315–317) | `a < 79 °F` → `a`, else regression (l.320–327) | Applied to *all* points meeting the T/RH tests, including points set from the simple formula (l.330–347) | `mask_undefined=True` (default) masks T < 80 °F (l.350–353) | pint quantities; RH unitless fraction or percent with units |
| thermofeel `thermofeel/thermofeel.py:1181-1240` (`calculate_heat_index_adjusted`) | °F Rothfusz | `t2_f <= 40` → T (l.1234–1235) | `((A + t2_f)/2) >= 80` (l.1197) | Only where the switch selected the regression (l.1221, l.1228) | None. Takes **dew point**, recomputes RH by a Magnus form, so RH = 0 has no finite input and returns NaN. | K in, K out |
| thermofeel `thermofeel.py:1132-1178` (`calculate_heat_index_simplified`) | Celsius Rothfusz, bare | `t2_c > 20` gate; else returns T (l.1162) | none | none | none above 20 °C | K, RH % |
| pythermalcomfort `models/heat_index_rothfusz.py:18-119` | Celsius Rothfusz, bare (l.108–119) | none | none | none | `limit_inputs=True` (default) → NaN where `tdb < 27 °C` (l.76–78); no RH limit | °C; rounds to 0.1 by default; categories from unrounded value |
| pythermalcomfort `models/heat_index_lu.py` | Lu–Romps physiological model, nested bisection | n/a (defined everywhere) | n/a | n/a | defined for all T > 0 K; raises `ValueError` on a bad bracket or 100 iterations (l.345, l.358) | °C, RH % |

Basis: source.

The quoted switch lines at the pinned revisions are:

```text
weathermetrics R/heat_index.R:166      if (hi > 79) {
MetPy src/metpy/calc/basic.py:320      sel = np.array(a < units.Quantity(79., 'degF')) & np.isnan(hi)
thermofeel thermofeel/thermofeel.py:1197   warm_mask = ((A + t2_f) / 2) >= 80
```

MetPy's low-humidity adjustment (lines 330–338) is gated only on RH ≤ 13 % and 80 ≤ T ≤ 112 °F, not on whether the regression was used:

```text
330    sel = np.array((relative_humidity <= units.Quantity(13., 'percent'))
331                   & (temperature >= units.Quantity(80., 'degF'))
332                   & (temperature <= units.Quantity(112., 'degF')))
...
338        hi[sel] = hi[sel] - rh15adj
```

The source does not say whether this is intended; the docstring defers to "Figure 3 of [Anderson2013]" (not examined).

### 4. Differential test over temperature × humidity

Grid: T = 70–125 °F in 0.5 °F steps × RH = 0–100 % in 1 % steps, 11,211 points (`support/probe_hi.py`, output `support/probe_hi_output.txt`). Differences are reported where they exceed 0.05 °F.

| Pair | Points differing | Where | Max \|Δ\| |
|---|---|---|---|
| nws_literal (R1) vs wm_translit (`A > 79`) | 185 | T 77.0–80.5 °F, RH 16–100 % | 2.25 °F (T 79, RH 93) |
| wm_translit vs MetPy | 31 | T 80.0–81.0 °F, RH 0–12 % | 1.37 °F (T 81, RH 0) |
| nws_literal vs MetPy | 216 | T 77–81 °F | 2.25 °F |
| thermofeel adjusted vs nws_literal | 0 of 11,100 finite | — (RH = 0 row NaN by dew-point input) | < 0.05 °F |
| thermofeel simplified vs pythermalcomfort Rothfusz (no limit) | 0 | — | 0 |
| bare Celsius Rothfusz vs nws_literal | 3,042 | low-T and adjustment regions | 9.43 °F (T 70, RH 100) |
| Celsius vs Fahrenheit Rothfusz coefficients | — | whole grid | 2.5e-5 °F |
| pythermalcomfort `heat_index_lu` vs nws_literal | 10,841 | almost everywhere | 117 °F (T 125, RH 100) |

Basis: execution.

Spot values (°F): at T = 80, RH = 5 the outputs are:
- nws_literal, weathermetrics and thermofeel-adjusted: 77.94;
- MetPy: 77.25, from the extra adjustment;
- bare polynomial: 77.93;
- extended index: 76.16;
- pythermalcomfort default: NaN, since 80 °F < 27 °C.

At T = 70, RH = 50 the outputs are:
- NWS-type algorithms: 69.05;
- bare polynomial: 76.93;
- extended index: 68.67.

Under the NWS office categories, the category differs from nws_literal at:
- weathermetrics and MetPy: 87 points;
- the bare polynomial: 202;
- the extended index: 685.

Basis: execution.

Cool weather (T = 0–60 °F, RH 0–100 % in 5 % steps, 1,281 points): the bare polynomial without limits exceeds air temperature by up to 426.5 °F (T = 0 °F, RH = 95 %). This is consistent with Anderson et al.'s Table 2. Their algorithms 16 (°F Rothfusz) and 17 (Celsius Rothfusz, Fischer and Schär 2010) average 42.6 °C absolute difference from air temperature on days below 20 °C. The NWS algorithm (their algorithm 1) averages 0.8 °C there and has the smallest table-fit errors (0.2–0.4 °C). On the same cool grid:
- pythermalcomfort's default returns NaN at all 1,281 points;
- thermofeel's simplified function returns air temperature exactly;
- the extended index lies 7.33 °F below to 0.79 °F above air temperature.

Basis: execution + documentation.

### 5. Risk categories attached to the number

| Source | Caution | Extreme caution | Danger | Extreme danger |
|---|---|---|---|---|
| NWS office table (weather.gov/ama/heatindex, accessed 2026-11-21) | 80–90 °F | 90–103 °F | 103–124 °F | ≥ 125 °F |
| pythermalcomfort `_internal/validation.py:173-178, 289-291` (upper-closed bins) | (27, 32] °C | (32, 41] °C | (41, 54] °C | > 54 °C |
| same, in °F | (80.6, 89.6] | (89.6, 105.8] | (105.8, 129.2] | > 129.2 |

pythermalcomfort's 41 °C edge is consistent with the older NOAA convention that Anderson et al. cite (105 °F = "danger"). The current office table uses 103 °F. Applying both binnings to the same nws_literal value changes the category at 703 of 11,211 grid points, as follows:
- 303 points with heat index 103–105.8 °F are NWS "Danger" but pythermalcomfort "extreme caution";
- 236 points with 125–129.2 °F are NWS "Extreme Danger" but pythermalcomfort "danger".

The NWS table does not state interval closure; the probe used lower-closed bins. pythermalcomfort's `heat_index_lu` returns no category. Basis: source + documentation + execution.

### 6. The Lu–Romps extension: what changes and where

Lu and Romps keep Steadman's parameters and optimal-behaviour assumptions: shade, unlimited water, unlimited sweating and skin blood flow, and optimal clothing. They replace linearized terms with the full T⁴ longwave term, an explicit ventilation-cooling expression, and a more accurate saturation vapour pressure formula over water and ice. These changes deviate from Steadman's published values by < 1 K throughout the originally defined regions III and IV. By the same comparison, the Rothfusz fit errs by up to 7 K and the fit with NWS adjustments by up to 2 K. They define six physiological regimes:

| Region | Physiological regime | Status before the extension | Notes |
|---|---|---|---|
| I | Clothing fraction φ reduced from 1 to 0.84 | undefined | — |
| II | Reference vapour pressure `pa = p*(Ta)` instead of 1.6 kPa | undefined | — |
| III | Clothed (Steadman's case) | defined | — |
| IV | Naked (Steadman's case) | defined | — |
| V | Skin saturated, sweat drips | undefined | Entered from region IV at heat-index values of 308–333 K |
| VI | Skin blood flow unbounded and core temperature rising; index set from dT_c/dt at 1.6 kPa | undefined | Begins at heat index 345 K (161 °F) |

They report that the NWS chart is "negatively biased (biased low) by as much as 28 °F (16 K)". The edge of its labelled region corresponds closely to the V/VI boundary. Romps and Lu 2022 (abstract) report that the polynomial extrapolation underestimates the heat index by up to 10 °C (20 °F) during severe US heat waves of 1984–2020. Basis: documentation.

Port fidelity and behaviour, measured:
- **Agreement with upstream reference values.** pythermalcomfort's numba port matches the 54 reference values in its own `tests/test_heat_index_lu.py` (T = 200–370 K, RH = 0/50/100 %) to a maximum of 2.22e-6 K. The test itself asserts only `atol=1` K.
- **Gap against the NWS transcription.** On the NWS chart domain (T 80–110 °F, RH ≥ 40 %), the extended index minus nws_literal has a maximum of **+28.87 °F**, at T = 85.5 °F and RH = 100 % (109.7 vs 138.6 °F). This is independent reproduction of the published 28 °F figure. The minimum is −36.58 °F at T = 110, RH = 100, where the polynomial gives 278.2 °F against 241.6 °F extended.

Where the NWS value is ≤ 137 °F, the extended index is never more than 1.72 °F lower than the polynomial. The port's body mass and height (83.6 kg, 1.69 m, citing Fryar et al. 2018, as does the paper's reference list) enter only region VI's core heat capacity per unit area (`heat_index_lu.py:83-87, 279`). Basis: execution + source.

### 7. WBGT: explicit model vs approximations

**Definitions.** The outdoor WBGT is `0.7·T_nwb + 0.2·T_g + 0.1·T_a`, where T_nwb is the natural wet bulb and T_g the 150 mm black-globe temperature. Liljegren et al. 2008 solve steady-state energy balances for a wick cylinder and a globe from standard meteorological inputs. Their abstract reports agreement with measured WBGT "better than 1 °C". thermofeel's `liljegren.py` says it is transcribed from Liljegren's reference C code via an MIT-licensed mirror and is "validated bit-for-bit" against it; that claim was not re-checked here. It uses:
- fixed-point iteration with tolerance 0.02 K and at most 500 iterations, returning NaN on non-convergence (`liljegren.py:53-55`);
- a 10 m wind floor of 0.62 m s⁻¹;
- a Pasquill–Gifford stability-dependent 10 m → 2 m power-law profile;
- direct-beam fraction clamped to [0, 0.9].

Basis: source + documentation.

**Approximations shipped.**
- `calculate_wbgt_simple` is the BoM/ACSM sWBGT `0.567·Ta + 0.393·e + 3.94` (`thermofeel.py:616`). The BoM says it "assumes a moderately high radiation level in light wind conditions", overestimates in cloudy or windy conditions, and "will also overestimate night-time and early morning conditions".
- `calculate_wbgt` uses `0.7·Tw + 0.2·Tg + 0.1·Ta` with Stull's *psychrometric* wet-bulb regression, not the natural wet bulb (`thermofeel.py:713`). Stull states validity for RH 5–99 % and −20–50 °C, with errors −1 to +0.65 °C.
- pythermalcomfort `esi` is the environmental stress index.

Basis: source + documentation.

Measured on synthetic inputs (Ta 25–45 °C × RH 10/30/50/70/90 % × 10 m wind 0.5/1/2/4 m s⁻¹, p = 1013.25 hPa, 100 points per scenario; Liljegren converged at all points). Cells give approximation minus Liljegren as min / median / max (°C):

| Scenario / approximation | RH 10–30 % | RH 50 % | RH 70–90 % | KNMI heat-force level changed |
|---|---|---|---|---|
| night, sWBGT | 4.66 / 5.11 / 7.33 | 4.59 / 6.13 / 10.58 | 4.83 / 8.66 / 19.27 | 68/100 (≤ 3 levels) |
| night, ESI | 0.34 / 1.43 / 2.23 | 0.39 / 0.61 / 0.67 | 0.40 / 1.13 / 2.86 | 55/100 (≤ 2) |
| night, Stull wet bulb + globe (mrt = Ta) | 0.22 / 0.61 / 0.93 | 0.27 / 0.46 / 0.53 | −0.27 / 0.11 / 0.32 | 25/100 (≤ 1) |
| sun (800 W m⁻², fdir 0.8, cos z 0.85), sWBGT | −3.92 / −0.39 / 4.08 | −3.57 / 1.30 / 7.52 | −2.97 / 3.87 / 16.42 | 33/100 (≤ 2) |
| sun, ESI | −5.26 / −2.06 / 0.76 | −5.29 / −2.34 / −0.08 | −5.07 / −1.20 / 2.34 | 40/100 (≤ 3) |

Example spot (Ta 35 °C, RH 70 %, 1 m s⁻¹):

| Scenario | Liljegren | sWBGT | ESI |
|---|---|---|---|
| Night | 31.52 °C | 39.20 °C | 32.45 °C |
| Sun | 37.22 °C | 39.20 °C | 34.78 °C |

The heat-force scale is thermofeel's `calculate_heat_force`: 2 °C WBGT bands, level 10 at ≥ 32 °C, attributed there to a KNMI technical report that was not examined. Switching thermofeel's wind profile from the Liljegren profile to a log profile changes WBGT by 0.046 °C at one sunny point. Basis: execution (synthetic) + source.

These signs agree with Kong and Huber 2022 (abstract): "sWBGT greatly overestimates heat stress in hot-humid areas" and, over subtropical dry regions, both sWBGT and ESI "can substantially underestimate extreme heat". They recommend discontinuing sWBGT. The probe does not reproduce their ERA5 climatology. Basis: documentation + derived.

### 8. UTCI operational procedure and its two implementations

Bröde et al. 2012 (abstract) define UTCI as the air temperature of a reference environment that produces an equivalent dynamic physiological response in the UTCI-Fiala multi-node model with an adaptive clothing model. The reference environment has 50 % RH (vapour pressure capped at 20 hPa), calm air, and radiant temperature equal to air temperature. The one-dimensional response is a principal-component combination of 7 strain variables after 30 and 120 min, which accounts for about two-thirds of the variance. The procedure ships look-up tables and polynomial regressions over the same grid. Basis: documentation.

Both libraries use the same polynomial in (Ta, Tmrt−Ta, v₁₀, e in kPa) with constant term 0.607562052. A full polynomial of degree 6 in 4 variables has C(10,4) = 210 coefficients (derived), the count present in pythermalcomfort's `_utci_optimized`. Given identical vapour pressure, the two outputs agree to 1.46e-11 °C over 1,440 grid points. The implementations differ in four ways:
- **Range handling.** pythermalcomfort `utci` with `limit_inputs=True` (default) returns NaN outside Ta −50–50 °C, Tmrt−Ta −30–70 °C, v 0.5–17 m s⁻¹, RH 0–100 % and e 0–5 kPa (`utci.py:152-166`). It attributes these checks to the official `UTCI_a002.f90`, whose code accepts winds up to 30 m s⁻¹ while its documentation gives 17. thermofeel documents that "Inputs are not clamped; outside this range the approximation extrapolates" (`thermofeel.py:574`).
- **Out-of-range outputs.** Measured: at 40 °C and 90 % RH (e ≈ 6.6 kPa) the polynomial returns 72.59 °C in both libraries; pythermalcomfort's default returns NaN. At v = 25 m s⁻¹ it returns 39.37 °C against 30.30 °C at v = 0.1 m s⁻¹, for Ta = Tmrt = 30 °C and RH 50 %. pythermalcomfort's docstring warns that the original approximation "can also have a non-monotonic wind-speed response".
- **Vapour pressure.** pythermalcomfort derives e from RH with the Hardy ITS-90 saturation formula. thermofeel's dew-point path computes `Hardy_es(T)·RH_Magnus(T,Td)/100` (`thermofeel.py:583-584`), mixing two saturation formulas, so e is 0.975–1.003 times the self-consistent value. The resulting UTCI error is ≤ 0.013 °C (median 0.0015 °C). thermofeel's own `calculate_dew_point_from_relative_humidity` uses a third (Alduchov–Eskridge) form.
- **Categories.** pythermalcomfort maps UTCI to the 10-class stress scale with edges −40/−27/−13/0/9/26/32/38/46 °C. thermofeel returns no categories.

Basis: source + execution.

### 9. Heat-health warning evaluations and the index computations they depend on

| Study | Design and exposure | Outcome | Reported result | Stated limitation |
|---|---|---|---|---|
| Ebi et al. 2004 (Philadelphia, 1995–98) | Excess mortality age ≥ 65 vs a 1964–88 trend line, regressed on heat-wave timing and a warning indicator | Deaths | Warning coefficient ≈ −2.6 lives per warning day (and 3 days after); ≈ 117 lives saved; costs "small" compared with the value of a life | Single city; observational; trigger criteria not examined here |
| Toloo et al. 2013 (systematic review) | 15 included articles (per abstract via search index) | Mortality, morbidity, behaviour | Six studies reported fewer deaths after implementation. Availability of a warning did not by itself change behaviour. | "Research in this area is limited"; calls for prospective designs |
| Weinberger et al. 2021 (US, 2006–2016) | Medicare ≥ 65 in 2,817 counties; NWS heat alert days matched to non-alert days by month and daily maximum heat index; conditional Poisson | All-cause mortality; cause-specific admissions | Mortality RR 1.005 (0.997–1.013). Admissions increased: fluid/electrolyte RR 1.040 (1.015–1.065), heat stroke RR 1.094 (1.038–1.152). | Observational national-scale design |

Basis: documentation (see Evidence for retrieval).

**Template linking warning criteria to computations.** It is derived from §§2–8. Each warning criterion should record:
1. which index, and which named variant (Steadman table, Rothfusz bare, NWS-adjusted with switch rule R1 or R2, extended);
2. the input variable (RH or dew point) and the saturation-vapour formula used to convert it;
3. the units and rounding (weathermetrics rounds to integers by default; pythermalcomfort to 0.1);
4. out-of-range policy (NaN, mask, passthrough of T, or extrapolation);
5. the category table and its interval closure;
6. for WBGT, natural vs psychrometric wet bulb, wind height and floor, and the radiation inputs;
7. for UTCI, the vapour-pressure path and the input-range policy.

Under these choices the same weather can cross a threshold or not:
- §4: up to 2.25 °F near 80 °F;
- §5: 103 vs 105.8 °F;
- §7: several °C for WBGT.

Weinberger et al.'s matching on daily maximum heat index inherits whichever variant their data used (not identified here). Basis: derived.

### 10. Performance and resource footprint (L1–L6)

Host for all measurements: x86-64 Linux workstation, Intel Xeon @ 2.60 GHz, 96 logical CPUs, 236 GiB RAM, single process. Per-point times are the best of 3 runs on arrays (`support/perf_probe.py`, `support/perf_probe_output.txt`).

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | Person-time or tokens to implement any index | not measured | — |
| L1 | Size of formula logic | weathermetrics algorithm 31 lines (l.156–186); MetPy `heat_index` 121 lines including docstring; pythermalcomfort `heat_index_lu.py` 441 lines | source (line counts) |
| L2 build | `import pythermalcomfort.models`, empty numba cache (eager JIT) | 12.12 s; warm cache 1.43–1.63 s | execution |
| L2 | Import `metpy.calc` / `thermofeel` | 0.92–0.94 s / < 0.01 s | execution |
| L3 latency | First scalar call `heat_index_rothfusz` after import | 0.052 s (second call 0.30 ms) | execution |
| L4 throughput | pythermalcomfort Rothfusz | 45 ns/point | execution |
| L4 | thermofeel simplified / adjusted heat index | 63 / 108 ns/point | execution |
| L4 | MetPy `heat_index` (pint) | 116 ns/point | execution |
| L4 | pythermalcomfort `utci` / thermofeel `calculate_utci` | 459 / 761 ns/point | execution |
| L4 | thermofeel Liljegren WBGT (sun) | 5,799 ns/point | execution |
| L4 | pythermalcomfort `heat_index_lu` (nested bisection, tol 1e-8) | 93,930 ns/point; upstream documentation reports 53,000 ns/point on its own machine, and 187 ns/point for `utci` | execution; documentation (`docs/contributing/performance.rst`) |
| L4 | Global hourly year (≈ 9e9 points) for `heat_index_lu`, one core | ≈ 9.8 days at 93,930 ns (derived 9e9 × 9.393e-5 s); upstream says "~5 days" | derived; documentation |
| L5 verification | Certificate or proof checking | not applicable (no certificates exist) | — |
| L6 memory | Peak RSS of the timing run (1e6-point float64 arrays, all three libraries) | 698,020 kB | execution (`/usr/bin/time -v`) |
| L6 disk | Installed size: pythermalcomfort / thermofeel / metpy | 2.1 MB / 196 KB / 3.3 MB | execution (`du`) |
| L6 | Dependencies: numba / llvmlite; numba cache | 33 MB / 173 MB; 2.1 MB | execution |
| L6 energy | Energy per evaluation | not measured | — |

### 11. Comprehensibility and conceptual simplicity (C1, C2)

**C1, comprehensibility.** A forecaster or analyst must hold at least five independent decisions to know what a "heat index" number means:
- variant;
- switch rule;
- adjustment gating;
- out-of-range policy;
- category table.

None is visible in the function name: the bare polynomial ships as `heat_index_rothfusz` and `calculate_heat_index_simplified`, and MetPy applies one adjustment outside the branch the NWS text attaches it to. Failure legibility varies:
- pythermalcomfort emits a `UserWarning` and NaN;
- MetPy masks values;
- thermofeel returns plausible-looking extrapolations;
- weathermetrics returns integers by default.

Basis: source + derived.

**C2, simplicity.** The core invariant is "apparent temperature under Steadman's idealized person". Lu–Romps make that invariant total by re-solving the model in every region, which removes the switch, both adjustments, the low-temperature passthrough and the undefined regions. It costs about 2,000× the per-point time of the polynomial (93,930 vs 45 ns, measured) and an iterative solver that can raise exceptions. UTCI shows the opposite trade: one polynomial replaces the physiological model, and the special cases move into input-range policy. That policy is where the two UTCI libraries diverge. For WBGT, the explicit model has one fewer ad-hoc assumption than sWBGT, which hard-codes radiation and wind. Basis: derived.

### 12. Validation coverage (V1–V4)

- **V1, specification adequacy.** Rothfusz fit error ±1.3 °F; NWS-adjusted fit ≤ 2 K vs Steadman's table, and the extended index < 1 K (Lu–Romps); Anderson et al.'s 21-algorithm comparison against Steadman's tables and 2011 state-capital weather. Execution: this report's 11,211-point differential grid and 54-value port check. There are no mutation or property-based tests of the libraries beyond their own unit tests. pythermalcomfort's Lu test tolerance of 1 K would not detect sub-kelvin regressions; it is a weak oracle.
- **V2, implementation and lowering.** pythermalcomfort's numba rewrite of `heat_index_lu` is pinned to pre-rewrite outputs at `atol=1e-6` for 9 cases (`test_heat_index_lu_regression_values`). Cross-library differential testing found the switch-rule and adjustment-gating divergences of §4.
- **V3, concurrency, crash, silicon or physical leakage.** Not applicable to these pure numerical functions. Physical sensor validation is Liljegren's own field comparison, which was not re-examined.
- **V4, field and human validation.** Warning-system outcome studies (§9) are the only field evidence linking computed indices to health outcomes, and none isolates the index-variant choice. Human mental models of category labels were not examined.

## Boundaries

- **Not examined:**
  - Steadman 1979 directly (doi:10.1175/1520-0450(1979)018<0861:TAOSPI>2.0.CO;2; Crossref metadata verified only); its assumptions are quoted via Rothfusz 1990, Anderson et al. and Lu–Romps;
  - Anderson et al.'s Figure 3 flowchart, so whether its switch threshold is 79 or 80 °F, and against which quantity, is unknown from primary text;
  - the NWS online calculator's JavaScript;
  - ISO 7243:2017 (paywalled), so occupational WBGT reference values are not stated here;
  - the KNMI heat-force report cited by thermofeel;
  - the official UTCI Fortran code and look-up tables;
  - the original Lu–Romps reference code (the hosting site refused automated access); port fidelity was checked only against values embedded in pythermalcomfort's tests;
  - Liljegren's C reference code and the claimed bit-for-bit match.
- **Not examined (data):** no station, reanalysis or climate-zone records were processed. The station-record comparison design in §9 was not run. All WBGT and UTCI numbers come from synthetic grids, which include unrealistic humidity–temperature combinations.
- **Not examined (implementations):** spreadsheets, NWS internal software and other packages.
- **Unknown:**
  - which reading of the NWS switch rule (R1 or R2) the NWS itself uses operationally;
  - whether MetPy's ungated low-humidity adjustment is deliberate;
  - the heat-index variant used to build the exposure and matching variables of the warning-evaluation studies.
- **Known not to apply:** the heat index assumes shade. The NWS office page says direct sun can add "up to 15 °F", and no implementation examined models it. pythermalcomfort `wbgt` does not estimate WBGT from weather; it only combines measured sensor temperatures.
- **Unsupported:**
  - thermofeel's adjusted heat index cannot represent RH = 0 because it takes dew point;
  - pythermalcomfort `heat_index_lu` raises `ValueError` rather than returning NaN if a bisection bracket fails (`heat_index_lu.py:345, 358`); no grid point triggered this.
- **Not established:**
  - the probe does not show that any library is "wrong" relative to an authoritative specification, because the NWS text is ambiguous and no NWS software was executed;
  - the WBGT grid results do not establish field error magnitudes;
  - the agreement between the extended index's +28.9 °F gap and the published 28 °F figure comes from a transcription of the NWS algorithm, not from NWS output;
  - search-index abstracts were not cross-checked against publisher full text for Toloo et al., Weinberger et al. and Liljegren et al.

## Evidence

**Source, at pinned commits:**
- pythermalcomfort `a0e7ae2a9a0178f24b33fdd75f06f27e9f00ba76`:
  - `pythermalcomfort/models/heat_index_rothfusz.py:18-119`;
  - `pythermalcomfort/models/heat_index_lu.py:83-87, 103, 339-360, 363-407, 427-441`;
  - `pythermalcomfort/models/utci.py:129-166, 212+`;
  - `pythermalcomfort/models/wbgt.py`;
  - `pythermalcomfort/_internal/validation.py:171-178, 249-291`;
  - `tests/test_heat_index_lu.py`;
  - `docs/contributing/performance.rst`.
- thermofeel `53437e0e47fb428c452d0f418b68fb46ba802a22`:
  - `thermofeel/thermofeel.py:70-170` (vapour-pressure helpers), `214-232`, `284-596` (UTCI), `598-717` (WBGT approximations), `743-804` (Liljegren wrapper), `806-822` (heat force), `1132-1240` (heat index);
  - `thermofeel/liljegren.py:1-73, 146-314`.
- weathermetrics `429ee9a4410c6c0c00d209a32ae8e52a0edfa4cc` `R/heat_index.R:76-110, 156-186`.
- MetPy `5edfa0186fb0d01ef6d29319c6c2a496a888fb28` `src/metpy/calc/basic.py:235-355`.
- Tarball SHA-256 values are in `support/execution_record.md`.

**Normative and documentation sources (accessed 2026-11-21):**
- Rothfusz 1990, SR 90-23 (full text, weather.gov PDF);
- NWS WPC "The Heat Index Equation" page;
- NWS Amarillo office heat index page (risk table and ±1.3 °F statement);
- BoM thermal stress page (sWBGT formula and caveats).

**Literature.** Every DOI cited was verified against Crossref metadata (title, authors, venue, volume, pages) on 2026-11-21:

| DOI | Content examined |
|---|---|
| 10.1289/ehp.1206273 | full text via PMC |
| 10.1175/JAMC-D-22-0021.1 | full text, publisher HTML |
| 10.1088/1748-9326/ac8945 | Crossref abstract |
| 10.1029/2021EF002334 | Crossref abstract |
| 10.1175/JAMC-D-11-0143.1 | Crossref abstract |
| 10.1007/s00484-011-0454-1 | publisher abstract; full text paywalled. Crossref records issue date May 2012, online 2011. |
| 10.1175/BAMS-85-8-1067 | publisher abstract |
| 10.1080/15459620802310770 | abstract via web search index only |
| 10.1007/s00038-013-0465-2 | abstract via web search index only |
| 10.1016/j.envint.2021.106834 | abstract via web search index (two independent queries agreeing on all quoted figures); publisher page not retrievable |

Software papers were checked by Crossref metadata only and are not used for technical claims:
- Tartarini and Schiavon 2020, doi:10.1016/j.softx.2020.100578;
- Brimicombe et al. 2022, doi:10.1016/j.softx.2022.101005;
- Blazejczyk et al. 2012, doi:10.1007/s00484-011-0453-2, which thermofeel cites for its simplified heat index.

**Execution**, all on 2026-11-21. Environment, install commands, versions and the two transcriptions are in `support/execution_record.md`. Scripts and raw outputs:
- `support/probe_hi.py` → `support/probe_hi_output.txt`;
- `support/probe_wbgt_utci.py` → `support/probe_wbgt_utci_output.txt`;
- `support/perf_probe.py` → `support/perf_probe_output.txt`.

## Revalidation

1. **Switch rule and adjustment gating (cheapest).** Diff three lines at a new revision:
   - weathermetrics `R/heat_index.R` (`if (hi > 79)`);
   - MetPy `basic.py` (`a < units.Quantity(79., 'degF')` and the ungated `rh15adj` block);
   - thermofeel `thermofeel.py` (`warm_mask = ((A + t2_f) / 2) >= 80`).

   Then rerun `support/probe_hi.py`. Section [3] must still show the 77–80.5 °F disagreement band for the findings of §4 to hold.
2. **Bare polynomial and limits.** Check whether `heat_index_rothfusz` still lacks adjustments and still gates on 27 °C (`limit_inputs` block), and whether `calculate_heat_index_simplified` still gates on `t2_c > 20`. In the probe, section [2] pair "thermofeel_simplified vs ptc_rothfusz_nolimit" must stay at 0 difference.
3. **Categories.** Compare `HEAT_INDEX_STRESS_CATEGORIES` with the current NWS office table. Section [6] of the probe recounts the affected points.
4. **Extended index port.** Rerun the 54-value check in `support/execution_record.md`, or `pytest tests/test_heat_index_lu.py` with the tolerance tightened to 1e-4 K. Section [7b] must still show a maximum near +28.9 °F at T = 85.5 °F, RH = 100 %.
5. **WBGT and UTCI.** Rerun `support/probe_wbgt_utci.py`. Watch for:
   - UTCI agreement > 1e-6 °C, which would mean the polynomials diverged;
   - a change in pythermalcomfort's NaN count (180/1,440), which would mean range checks changed;
   - Liljegren NaN counts > 0, which would mean a solver change.
6. **Not cheaply revalidated.** The warning-evaluation findings require re-reading the papers. The NWS operational rule requires NWS source or a written specification, which this report did not obtain.
