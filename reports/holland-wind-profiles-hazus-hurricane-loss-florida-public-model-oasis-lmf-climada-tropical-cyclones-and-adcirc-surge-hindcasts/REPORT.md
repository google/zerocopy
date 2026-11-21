# Holland-type hurricane wind profiles in open loss and surge codes, Oasis loss kernels, HAZUS and Florida public-model context, and surge hindcast validation

## Summary

- **"Holland profile" names a family of recipes.** All codes share `p(r) = pc + Δp·exp(-(Rm/r)^B)` and its gradient wind but differ in every surrounding constant: air density (CLIMADA, GeoClaw 1.15 kg/m³; ADCIRC default 1.293), gradient-to-10-m reduction (0.9 hard-coded in CLIMADA, GeoClaw, ADCIRC NWS=19/20; user `BLAdj` in ADCIRC NWS=8), output 1-to-10-min factor (ADCIRC 0.8928, GeoClaw 0.88, CLIMADA none: 1-min output), ambient pressure (CLIMADA track/basin 1010 hPa; ADCIRC NWS=8 fixed 1013 hPa; GeoClaw 101.3 kPa) and B clamp ([1, 2.5]; CLIMADA H08 [0.81, 2.025]; ADCIRC GAHM none). In a toy comparison, recipes identical at the radius of maximum wind spread by 22% at 300 km.
- **CLIMADA's default model (H08) ignores the recorded maximum wind**; intensity comes from pressure deficit. Running CLIMADA's own functions, H08 is 3.6–6.0% above H1980 between 40 and 120 km for the same storm.
- **GeoClaw `holland2008`/`holland2010` pass Pa (Pa/s) into Holland's hPa (hPa/h) formula.** The compiled upstream function then returns B = 1.0 for any moving storm and 2.5 for a stationary one; in a toy reconstruction a 63-hPa storm loses 16% of its wind at Rm and gains 31% at 300 km. Only `holland80` has regression data.
- **Oasis ktools and OasisLMF share hash-seed constants and quadratic in-bin interpolation**, which stops honouring the declared bin mean when it lies outside the middle third of a bin. Real `gulcalc` with interpolation points at 10% of each bin: sample means shifted 0.8075 times the analytic shift (closed form 0.8015); `validatedamagebin` only warns; ktools lacks OasisLMF's discriminant guard.
- **ktools 3.12.5 built in 45 s and passed 200/200 golden-file checks in 40 s**; allocation rules 2 and 3 matched on all five multi-layer cases; fmpy maps rule 3 to 2.
- **Cited validation:** HAZUS 0.71 vs 0.72 intense landfalls/yr; Eberenz et al. 473 events, pre-calibration damage ratios 0.2–35.6; Westerink et al. slope 0.91, R² 0.804, MAE 0.30 m; SLOSH ±20%; GAHM's isotach match is in-sample.

## Applicability

The report compares independent implementations of one idealization, a parametric axisymmetric vortex with empirical surface adjustments, in CLIMADA (climate-risk platform), ADCIRC and GeoClaw (surge models). It also compares two independent Oasis loss kernels that consume hazard footprints: ktools (C++) and OasisLMF `pytools` (Python/Numba). HAZUS (Vickery et al. 2006 I/II), Emanuel et al. 2006, Eberenz et al. 2021, Westerink et al. 2008 and SLOSH (NWS 48) are published methodology and validation evidence and were not executed. The Florida commission material covers only the adopted standard categories and the review calendar.

All code statements refer to the single pinned revision of each repository; no other versions were compared. Executed: CLIMADA wind-profile function bodies (under numpy with a dict stand-in for xarray; the CLIMADA package itself was not installed); GeoClaw `get_holland_b_2008` and one ADCIRC `vortex.F` expression (gfortran 15.2.0); and the full ktools build, `make check` and example pipeline. ADCIRC as a whole, GeoClaw as a whole and OasisLMF were **not** built or run; statements about them rest on source reading and on toy transliterations labelled as such. Host for every measurement: x86-64 Linux workstation, Intel Xeon @ 2.60 GHz, 96 logical CPUs, 236 GiB RAM, gcc/g++/gfortran 15.2.0, Python 3.13, numpy 2.3.5.

The formulas are shared widely, but the constants are code- and configuration-specific; re-check the cited line ranges before reusing any table entry for another revision (see Revalidation). ADCIRC's air density is runtime-modifiable ("may be modified by the user at runtime", `constants.F90`), and NWS=8 `BLAdj` comes from the run's input file, so the values shown are defaults or common settings.

## Findings

### 1. Shared formulas

Basis: documentation (CLIMADA docstrings and ADCIRC GAHM page restating Holland 1980/2008/2010) + source.

| Quantity | Formula | Where used |
|---|---|---|
| Pressure | `p(r) = pc + Δp·exp(-(Rm/r)^B)` | all |
| Gradient wind, B form | `Vg = sqrt((B·Δp/ρ)(Rm/r)^B·exp(-(Rm/r)^B) + (r f/2)²) - r f/2` | CLIMADA `_stat_holland_1980` (l.759-767) |
| Gradient wind, Vm form | `Vg = sqrt(Vm²·(Rm/r)^B·exp(1-(Rm/r)^B) + (r f/2)²) - r f/2` | ADCIRC `HollandGet` (l.667-670), GeoClaw (l.662-664) |
| Cyclostrophic peak / B | `Vm = sqrt(B·Δp/(ρ e))`, i.e. `B = ρ e Vm²/Δp` | all "1980" recipes |
| Holland 2008 surface `bs` | `bs = -4.4e-5 Δp² + 0.01 Δp + 0.03 ∂pc/∂t - 0.014 abs(φ) + 0.15 vt^x + 1`, `x = 0.6(1 - Δp/215)`, Δp in hPa, ∂pc/∂t in hPa/h, vt in m/s | CLIMADA (l.420-432), GeoClaw (l.596-598) |
| Holland 2010 | `V = Vms·[(Rm/r)^bs·exp(1-(Rm/r)^bs)]^x`, x = 0.5 inside Rm, linear to x_n at r_n | CLIMADA (17 m/s at 300 km default), GeoClaw (10 m/s at 500 km) |
| GAHM | `B_g = B(1+1/Ro)e^(φ-1)/φ`, `φ = 1 + (1/Ro)/(B_g(1+1/Ro))`, solved iteratively | ADCIRC docs (eqs. 9, 11) |

The B and Vm forms are algebraically identical only while B is unclamped. With `Vg = 77.8 m/s` (70 m/s at 10 m), Δp = 60 hPa and ρ = 1.15, raw B = 3.152 is clamped to 2.5. The B form then caps the surface peak at 62.34 m/s, while the Vm form keeps 70.00 m/s. Basis: execution (toy model of the two forms, not any upstream code itself), `holland_toy.py`.

### 2. Per-implementation parameter, unit and averaging table

Basis: source (line numbers at the pinned revisions).

| Recipe | Vmax handling | Gradient→surface | ρ (kg/m³) | Ambient p | B and clamp | Output averaging |
|---|---|---|---|---|---|---|
| CLIMADA H1980 | `vg = max(0, vmax - vt)/0.9` (l.92-95) | ×0.9 after profile (l.201) | 1.15 (l.58) | track `environmental_pressure`; IBTrACS basin defaults 1004-1010 hPa (`tc_tracks.py` l.157-170) | `vg² e ρ/Δp`, clip (1.0, 2.5) (l.503-508, 528) | 1-min, 10 m (docstring l.1139) |
| CLIMADA H08 (default, `trop_cyclone.py` l.149) | **unused**; profile from Δp | none (B is surface-level) | 1.15, or Holland et al. 2010 eq. 9 if `rho_air_const=None` (l.340-361) | as above | Holland 2008 `bs`, clip (1.0, 2.5)×0.9² = (0.81, 2.025) (l.433-434, 529-531) | 1-min |
| CLIMADA H10 | replaced by `sqrt(bs Δp/(ρ e))` by default (l.304-306, 463-465) | none | 1.15 | as above | `bs` as H08; x truncated ≥ 0.4 (l.625) | 1-min |
| ADCIRC NWS=8 (`nws08.F90`) | `spd = (Vmax - 1.0·vt)/BLAdj` (l.621-627, 480-485) | ×BLAdj (l.677), code default 1.0 (l.71) | 1.293 (`constants.F90` l.73) | fixed `PRBCKGRND` 1013 hPa (l.613; constants l.61) | `ρ e spd²/Δp`, clamp [1, 2.5] (l.630-635) | ×0.8928 if `windspeed_averaging_minute = 1` (l.699-702) |
| ADCIRC NWS=19 (deprecated, docs l.32) | `(Vmax - 1.5·vt_kt^0.63)/0.9` (`wind.F` l.5471-5472) | ×0.9 (`vortex.F` l.722) | 1.293 | track | clamp [1, 2.5] (`vortex.F` l.186-188) | ×0.8928 (l.745-746) |
| ADCIRC NWS=20 GAHM | same asymmetry term, via ASWIP (`aswip.F` l.417-421) | ×0.9 (l.870) | 1.293 | track | `B_g` unclamped (`vortex.F` l.218 clamp commented out) | ×0.8928 (l.893-894) |
| GeoClaw holland80 | `(mws - vt)/0.9` (l.455-466) | ×0.9 (l.512) | 1.15 (`data.py` l.59) | 101.3 kPa (`data.py` l.60) | `ρ e mod²/Δp`, clamp [1, 2.5] (l.582-584) | ×0.88 (l.75, 514) |
| GeoClaw holland2008/2010 | replaced by `sqrt(B Δp/(ρ e))` (l.715, 794) | none | 1.15 | 101.3 kPa | `bs` with Pa arguments (see 4.1), clamp [1, 2.5] (l.599-600) | ×0.88 |

Other conventions (source): CLIMADA caps translation at 30 kn (l.886-889) and weights it by `min(1, Rm/r)` (l.1227-1231), while ADCIRC NWS=8 and GeoClaw weight it by `abs(V)/Vmax` (`nws08.F90` l.745-746; GeoClaw l.504-506). ADCIRC `fang` inflow rises from 0° at the centre to 10° at Rm and 25° at 1.2 Rm and beyond (`vortex.F` l.1143-1156); NWS=8 uses no inflow unless `useInflow` is set (l.796-809). CLIMADA rescales IBTrACS agency winds to 1-min with Knapp and Kruk factors by default (`tc_tracks.py` l.134-149, 665) and divides STORM 10-min winds by 0.88 (l.191, 1531).

### 3. Executed and toy comparisons for one reference storm

The reference storm is illustrative and not fitted to any event: Vmax = 50 m/s (1-min, 10 m), pc = 950 hPa, Rm = 40 km, latitude 25°N, and translation 5 m/s. Ambient pressure is 1010 hPa for CLIMADA and each code's default for the others. The table gives axisymmetric surface speeds in m/s, with no inflow and no translational vector.

| r (km) | 20 | 40 | 60 | 80 | 120 | 200 | 300 | Basis |
|---|---|---|---|---|---|---|---|---|
| CLIMADA H1980 (1-min) | 33.40 | 43.90 | 40.79 | 36.42 | 29.03 | 19.54 | 12.66 | execution of upstream functions |
| CLIMADA H08, after its translation subtraction (1-min) | 31.55 | 45.48 | 43.22 | 38.59 | 30.42 | 19.91 | 12.43 | execution of upstream functions (subtraction step is own code replicating l.1240-1242) |
| ADCIRC NWS=8, BLAdj 0.9, ÷0.8928 → 1-min | 31.76 | 43.90 | 40.46 | 35.68 | 27.80 | 18.02 | 11.20 | toy model of ADCIRC, not ADCIRC |
| GeoClaw holland80, ÷0.88 → 1-min | 34.44 | 43.90 | 41.01 | 36.91 | 29.86 | 20.59 | 13.72 | toy model of GeoClaw, not GeoClaw |
| GeoClaw holland2008 as coded, ÷0.88 | 37.90 | 43.68 | 41.49 | 38.37 | 32.66 | 24.41 | 17.68 | toy model; B from the compiled upstream function |
| GeoClaw holland2008 with hPa, ÷0.88 | 37.39 | 51.94 | 47.88 | 42.22 | 32.94 | 21.44 | 13.44 | toy model (counterfactual) |

The toy reproduces both CLIMADA rows exactly (`max|Δ| = 0.00 m/s`), which does not validate the ADCIRC or GeoClaw rows. B values: CLIMADA H1980 1.3025, H08 1.3925, ADCIRC NWS=8 1.3947 (ρ = 1.293, Δp from 1013 hPa), GeoClaw holland80 1.2405.

Derived: at Rm every Vm-form recipe gives `Vmax - vt` less the same Coriolis reduction (43.90 m/s); at 300 km the 1-min equivalents span 11.20–13.72 m/s (factor 1.225). ADCIRC's ρ = 1.293 instead of 1.15 multiplies B by 1.1243 and, in the toy, lowers winds by 8% at 20 km and 18% at 300 km while leaving the value at Rm unchanged.

### 4. Failure cases and sharp edges

**4.1 GeoClaw Holland 2008/2010 unit mismatch.** Basis: source + execution.

- Pressure units: the storm file is read with `! central_pressure = Pa` (`parametric_met_forcing_module.f90` l.133). `get_pressure_diff` returns `dp = ambient_pressure - Pc` floored by `if (dp < 100.d0) dp = 100.d0` (l.565-569), and `central_pressure_change(i) = ds / dt` is in Pa/s (l.176-178).
- The call: `set_holland_2008_fields` (l.712) and `set_holland_2010_fields` (l.791) both call `B = get_holland_b_2008(dp, dPc_dt, sloc(2), tv)`. That function computes `x = 0.6d0 * (1.d0 - dp / 215.d0)` and `B = -4.4d-5 * dp**2 + 0.01d0 * dp + 0.03d0 * dpdt ...` (l.596-598), which are Holland's hPa coefficients; CLIMADA converts explicitly ("The formula assumes that pressure values are in millibar (hPa)", l.417-420).
- Compiled upstream function, vt = 5 m/s: hPa arguments give B = 1.19253, 1.35473, 1.44346 and 1.46143 for Δp = 20, 50, 80 and 100 hPa; the Pa arguments as passed give 1.00000 for all four. At vt = 0 the Pa call gives 2.50000, because `0**x` with large negative x is +Inf before the clamp.
- Coverage: regression data exists only for `holland80` (`tests/regression/met_forcing/regression_data/aux_holland80.txt`, `examples/storm-surge/isaac/regression_data/holland80/`).

**4.2 CLIMADA H08 ignores recorded intensity.** Basis: source + execution.

- `_compute_angular_windspeeds_h08` calls only `_rho_air`, `_bs_holland_2008` and `_stat_holland_1980` (l.242-246), so the track's `vmax` never enters.
- Its B clip interval is the gradient-level (1.0, 2.5) multiplied by `gradient_to_surface_winds**2` (l.529-531), even though the profile is not multiplied by 0.9 afterwards.
- With `rho_air_const=None`, the reference storm's density becomes 1.1163 and the H08 angular speed at Rm becomes 51.26 m/s instead of 50.48 m/s.

**4.3 ADCIRC constants and comments.** Basis: source + derived.

- `nws08.F90` l.697-698 says "(0.88 factor)", but the multiplier is `one2ten = 0.8928d0 !... Powell et al 1996` (`constants.F90` l.111). Commented alternatives (`1.00D0 !... HWind`, `0.8787D0 !.. OceanWeather`) show the choice is a convention.
- GeoClaw describes its hard-coded 0.9 as "input variable in ADCIRC but always is set to the following value" (l.70-72), but NWS=8 `BLAdj` really is an input.
- Derived from ADCIRC's Garratt drag `Cd = 1e-3(0.75 + 0.067U)`, capped at 0.0035 (`wind.F` l.521, 123, 538): stress elasticity with respect to wind is 2.64–2.78 for 20–40 m/s and 2 above 41.04 m/s, so the 0.8928 vs 0.88 choice alone changes stress by 2.9–4.1%.

**4.4 ADCIRC NWS=19 rescale.** Basis: source + execution (expression) + toy model. In `uvp`, `speedAtRmax = SQRT((Vmax*kt2ms)**2.d0 * * EXP(0.d0) + (nm2m*dist*percentCoriolis*corio/2.d0)**2.d0) - nm2m*dist*...` (`vortex.F` l.704-709) evaluates the Coriolis term at the node distance `dist`, not at `rmx`. Every speed is then multiplied by `Vmax*kt2ms/speedAtRmax` (l.713, 719), so the profile is the gradient-wind profile times `Vm/(sqrt(Vm²+c²)-c)`, with `c = r f/2`. In the toy (25°N, Vm = 55.6 m/s) that factor is 1.0224 at 40 km, 1.1802 at 300 km and 1.2462 at 400 km. The `* *` split across l.705-706 joins into `**` under fixed-form rules and, compiled verbatim, yields `a**(2**exp(0)) = a**2` (43.594888 against 43.594888 computed directly): a legibility hazard, not a numerical bug. GAHM's `uvpr` has no rescale (l.849-863).

**4.5 Dimensional empirical constants.** ASWIP and NWS=19/20 compute storm motion as `1.5·vt^0.63` with vt taken from the track file's integer knot column (`aswip.F` l.417; `wind.F` l.5256, 5471), so the coefficient is unit-bound. Expressed in m/s, the same correction is `1.5·0.5144^0.37·vt^0.63 ≈ 1.17·vt^0.63` (derived).

### 5. Synthetic storm catalogues

- **HAZUS (Vickery et al. 2006 I; documentation, full text).** Uses the Vickery et al. (2000) track and wind-field model, updated to Atlantic storms 1886–2001, with limits on intensification rate and heading change and a new radius-of-maximum-wind model. A 100,000-year simulation stores peak gusts above 50 km/h (10 m, open terrain) at 31,142 census-tract centroids. Validation: 0.71 simulated vs 0.72 observed intense landfalls/yr (by central pressure); wind field checked at more than 140 anemometer sites.
- **Emanuel et al. 2006 (documentation).** Compares two largely independent track generators: a Markov chain on observed track statistics, and synthetic 850/250-hPa winds with beta drift and historical genesis. About 10^4 tracks per site, each run through a deterministic coupled intensity model.
- **CLIMADA random walk (source).** Defaults in `calc_perturbed_trajectories`: `nb_synth_tracks=9`, `max_shift_ini=0.75`°, `max_dspeed_rel=0.3`, `max_ddirection=π/360`, autocorrelations 0.85/0.5, landfall decay (`tc_tracks_synth.py` l.86-97). Decay coefficients are fitted to IBTrACS 1980–2019 (l.39-83). The docstring says the defaults "have been only roughly calibrated ... This is not an in-depth calibration" (l.127-129). The CLIMADA v1 paper applies 50 members to 693 tracks and reports the catalogue as both "34 650" and "34 560"; 693×50 = 34,650 (derived).
- **Missing Rm.** CLIMADA fills it from central pressure with a piecewise-linear fit, e.g. 14.9 nmi at 872 hPa and 56.9 nmi at 1021 hPa (`tc_tracks.py` l.3213-3230), which directly sets Rm in the tables above.

### 6. Vulnerability and impact functions

- **HAZUS (Vickery et al. 2006 II; documentation).** Component load-and-resistance damage on the building envelope (windows, roof cover, deck, connections, walls), with progressive failure and internal pressure. Resistances are random, e.g. strap uplift Normal(1200 lb, COV 0.3), toe-nail 415 lb (COV 0.25), entry door 50 psf (COV 0.2). Five damage states, from 0 (roof cover ≤ 2%, nothing else) to 4. Interior and contents losses are empirical "implicit" functions from engineering judgment and insurance data. Validation: a HUD survey of 466 houses in nine clusters after Andrew; roof damage after Erin and Fran.
- **CLIMADA / Eberenz et al. 2021 (documentation + source).** Impact function (Emanuel 2011): `mdd = vn³/(1+vn³)`, `vn = max(V - V_thresh, 0)/(V_half - V_thresh)` (`impact_funcs/trop_cyclone.py` l.197-199), defaults V_thresh = 25.7 and V_half = 74.7 m/s (the mean of Sealy and Strobl's 71.7–77.8; FEMA building values span 52–89). Eberenz et al. used 4098 IBTrACS tracks (1980–2017) on a 10-km grid with H08 winds. 848 EM-DAT events matched (USD 913 of 959 billion); 61 outliers off by more than a factor of 1000 were excluded, leaving 473. Only V_half was fitted per region, using TDR (sum ratio → 1) or RMSF (`exp(sqrt(mean((ln EDR)²)))`). Pre-calibration TDR: WP4 35.6, WP2 25.9, SI 0.2. The paper cites 62 countries (exposure section) and 53 (map caption) without reconciling them in the passages examined. Shipped TDR values (`climada/data/system/tc_impf_cal_v01_TDR1.0.csv`, m/s):

  | NA1 | NA2 (USA/Canada) | NI | OC | SI | WP1 | WP2 (Philippines) | WP3 | WP4 | Global |
  |---|---|---|---|---|---|---|---|---|---|
  | 66.3 | 89.2 | 70.8 | 64.1 | 52.4 | 66.4 | 188.4 | 112.8 | 190.5 | 110.1 |

  The RMSF file gives WP2 = 84.7 and NA2 = 86.0, so the cost-function choice moves WP2 by 188.4/84.7 = 2.22× (derived). With V_thresh fixed and no surge or rain hazard, V_half absorbs exposure error, sub-peril loss and reporting bias; values above about 120 m/s are not building fragilities (derived).

### 7. Oasis ground-up and insured loss: ktools vs OasisLMF

- **Seeding (source).** Both codes hash (group, event) with identical constants: ktools `s1 = (group_id * 1543270363L) % 2147483648L; s2 = (event_id * 1943272559L) % 2147483648L` (`gulcalc.cpp` l.468-470, 909-911); OasisLMF `GROUP_ID_HASH_CODE = 1543270363`, `EVENT_ID_HASH_CODE = 1943272559`, `HASH_MOD_CODE = 2147483648` (`gul/random.py` l.13-15), plus separate hazard-group constants (l.17-19). The generators differ by default: ktools uses `std::mt19937` with `uniform_real_distribution` (`getrands.h` l.58-59), while `gulmc` defaults to `--random-generator 2`, Latin hypercube on Philox4x32-7 (`gulmc/cli.py` l.49-55). Correlation is a one-factor Gaussian copula, `z_norm = sqrt_rho * x_norm + sqrt_1_minus_rho * y_norm` (`gul/random.py` l.212).
- **Stream conventions (source).** Special sidx: -1 analytic mean, -2 SD, -3 TIV, -4 chance of loss, -5 maximum loss (`gulmc/README.md` l.297-304). OasisLMF's packed multi-building stream spans `[-5B, B·S]`. Per README l.202-205, a reader trusting `sample_size` "would index past its sample array ... silently, as a wrong loss".
- **In-bin interpolation (source + execution + derived).** Both codes sample damage inside a bin from a linear density whose mean is the bin's interpolation value. ktools: `gul = (b.bin_from + (sqrt(bb*bb - (4 * aa*cc)) - bb) / (2 * aa)) * g.tiv;` (`gulcalc.cpp` l.204). OasisLMF: `disc = max(bb**2. + 4. * aa * rval_bin_offset, 0.)` (`gul/core.py` l.49). Derived: the discriminant is `bb²` at the bin bottom and `4h²/w²·(3x-1)²` at the top, where x is the relative mean position. A linear density with mean x is non-negative only for x ∈ [1/3, 2/3]; outside that interval the inverse cannot reach the whole bin, and the sample mean departs from x (toy: x = 0.1 gives mean 0.1794 and maximum 0.4167; x = 0.9 gives mean 0.8206). Real ktools: with every interpolation point at 10% of its bin, `validatedamagebin` reported 0 errors and 100 warnings, and paired runs sharing random numbers gave `Σ sample-mean shift / Σ analytic-mean shift = 0.8075` over 8805 (event, item) pairs, against a predicted 0.3206/0.4 = 0.8015. The 915,721 output rows contained no non-finite values. A toy at the exact edge (x = 1/3, r = prob_to) without OasisLMF's guard produced NaN in 38,424 of 200,000 random float32 bins.
- **Financial module (source + execution).** ktools `fmcalc` accepts `-a` 0–3 (`fmcalc/main.cpp` l.146). fmpy maps `allocation_rule == 3` to 2 (`fm/manager.py` l.34-35), while its README still lists "0, 1, and 2" (l.44). Executed case 1 (two layers, account limit 4000): rule 1 gave 500/500/1500/1500/1500/1500/500/500 by output id; rules 2 and 3 gave 400/800/2400/400/400/2400/800/400. Both match `examples/fm_alloc/README.md`, which documents a former defect in which rule 2 reused layer 1's proportions for every layer.
- **Consistency test design (not executed: OasisLMF needs numba, pandas and scipy, which were unavailable).**
  1. On the ktools `examples/` inputs, run `eve|getmodel|gulcalc -S1000 -a0` and `gulmc -S1000 --random-generator 0`.
  2. Require float32-equal specials -1, -3, -4 and -5 per item, with a tolerance for -2.
  3. Compare per-item sample means within 3 Monte Carlo SE, plus a two-sample KS test. Per-sample equality is not expected because the generators differ.
  4. Feed one ktools GUL stream to `fmcalc -aR` and `fmpy -aR` for R ∈ {0, 1, 2} and require per-sample equality within float32 rounding, logging the item, level and calcrule of any difference.

### 8. Florida public model and commission standards

Basis: documentation (meeting summary and index page only). On 2025-10-28 the commission adopted, effective 2025-11-01, hurricane standards in six groups (General, Meteorological, Statistical, Vulnerability, Actuarial, Computer/Information), each with disclosures, forms and audit items. Its professional-team page lists 2023-standards reviews dated 06/10/2025 for six models, including the Florida Public Hurricane Loss Model. Because the standards text, Powell et al. 2005 and Tao et al. 2022 were not examined, the report does not say which requirements are reviewed and which are computed.

### 9. Surge hindcast validation

- **Westerink et al. 2008 (ADCIRC; documentation, full text).**
  - Grid: S08, 314,442 nodes and 600,331 elements, from about 50 km in the deep Atlantic to under 100 m in channels.
  - Forcing: five tidal constituents and rivers (Betsy: Mississippi 5520, Atchafalaya 2200 m³/s). Winds were 10-min H*WIND (Betsy) and PBL (Andrew), with directional land roughness over 12 upwind sectors within 30 km and zero stress under canopies with z0 > 0.39 m.
  - Peak surge at gauges (20 stations for Betsy), four outliers excluded: slope 0.91 (Betsy 0.899, Andrew 0.924), R² 0.804, mean error -0.15 m, MAE 0.30 m, SD 0.37 m; mean peak error 0.43 m (Betsy) and 0.27 m (Andrew).
  - Stated error sources: no wave setup, sparse topography and missing levees, wind-speed-only drag.
  - Cost: 6 min wall per simulated day on 256 Cray XT3 processors with a 2-s time step.
- **SLOSH (NWS 48; documentation).** Polar curvilinear grid with barrier overtopping. A single constant drag coefficient was chosen from 43 historical storms, and the authors explicitly reject per-storm "calibration or tuning". Verification storms include Betsy, Camille, Donna, Carla and two 1949 hurricanes. Accuracy is stated (OCR: "+20%") as 20% "when the hurricane is adequately described".
- **ADCIRC GAHM page (documentation).** Reports GAHM isotach means of 34.0, 50.0 and 64.0 kt with SD 0.10–0.12 kt, against SDs of 7.65–9.42 kt for OWI winds and 11.00–16.08 kt for SLOSH. GAHM fits Rm per quadrant to those same isotachs, so this is an in-sample consistency check (V1). The page gives B as "between 1 and 2.5" in one place and "(0, 2.5)" in another.
- **Hindcast-sensitivity design (not executed).** On one ADCIRC mesh and storm, run NWS=8 and NWS=20 with `BLAdj` ∈ {0.8, 0.9, 1.0}, ρ ∈ {1.15, 1.293}, `windspeed_averaging_minute` ∈ {1, 10} and `BCalc` ∈ {limited, exact}. Report Westerink's measures against gauges and high-water marks for each run. First-order expectation: setup scales with stress, so a 1% wind change gives about 2–2.8% (Finding 4.3). This expectation is untested.

### 10. Coverage tables

Performance and resources (L1–L6):

| Level | Value | Basis |
|---|---|---|
| L1 authoring/maintenance | Lines: `trop_cyclone_windfields.py` 1478, `vortex.F` 1391, `aswip.F` 2998, `nws08.F90` 1600, GeoClaw parametric module 1623, `gulcalc.cpp` 1106, `fmcalcrules.cpp` 1894, `gulmc/manager.py` 2004; probes here 545. LoC/person-month: not measured. | measured (`wc -l`) |
| L2 toolchain build | ktools: `autoreconf -fi` 4.64 s, `configure --disable-parquet` 5.74 s, `make -j8` 45.18 s wall (61.04 s user), peak RSS 232,080 kB. ADCIRC, GeoClaw, OasisLMF, CLIMADA install: not measured. | measured (x86-64 Linux workstation) |
| L3 preprocessing | CLIMADA probabilistic hazard set of 34,650 events on 9311 points: under 2 h on 4 vCPUs. ASWIP and ADCIRC mesh preparation: not measured. | cited (Aznar-Siguan and Bresch 2019) |
| L4 execution | CLIMADA `_stat_holland_1980` body: 1,000,000 evaluations in 49.5 ms (20.2 M/s, numpy). ktools example `eve\|getmodel\|gulcalc -S1000`: 1.79 s wall, 70,862,640-byte stream, giving 70.86 MB/1.79 s = 39.6 MB/s (derived). The full pipeline with `fmcalc` took 2.03 s. ADCIRC S08: 6 min wall per simulated day on 256 Cray XT3 processors (cited). OasisLMF gulmc/fmpy: not measured. | measured / cited / derived |
| L5 verification runs | ktools `make check`: 39.60 s wall, 200 of 200 SHA-1 golden comparisons OK. OasisLMF pytest suites (golden-file `filecmp`/`assert_allclose`) and GeoClaw regressions: not measured. | measured / source |
| L6 memory/disk | ktools pipeline processes peaked at 3.9–4.7 MB RSS. GUL stream size grows with samples: 1.13 MB (S=10), 7.47 MB (S=100), 70.9 MB (S=1000). CLIMADA default wind-field memory cap is 8 GB per thread (l.52); gulmc CDF cache defaults to 200 MB (`cli.py`). Energy: not measured. | measured / source |

Comprehensibility and simplicity (C1–C2):

| Item | Finding | Basis |
|---|---|---|
| C1 concept count | Stating one wind profile unambiguously takes at least eight conventions: averaging period, height, gradient-to-surface factor, ρ, ambient p, B estimator and clamp, translation and Coriolis. No code examined records them in output metadata; CLIMADA records only `units = "m/s"` (`trop_cyclone.py` l.699). | source + derived |
| C1 nonlocal traps | A comment that disagrees with its constant (4.3); units implied by caller rather than declared (4.1); the fixed-form `* *` (4.4); a clip interval scaled by 0.9² for a surface-level B (4.2). | source |
| C1 diagnostics | `validatedamagebin` warns about off-centre interpolation but not about the [1/3, 2/3] bound that controls correctness; NaN would surface only as a non-finite loss. | execution + source |
| C2 minimal abstraction | Carrying a typed wind statistic (period, height, exposure) with each speed would merge the 0.9, 0.88, 0.8928 and `BLAdj` multipliers into one conversion. Using the Vm form, with B controlling shape only, removes the clamp-induced peak loss of Finding 1. Restricting interpolation to x ∈ [1/3, 2/3] removes the mean shift. | derived (proposal) |
| C2 duplicated mechanism | Two Oasis kernels re-implement identical seeding and interpolation, which helps differential testing but splits fixes: only OasisLMF has the discriminant guard. | source |

Validation (V1–V4):

| Level | What exists / was done | Basis |
|---|---|---|
| V1 spec adequacy / non-vacuity | Toy-vs-upstream differential: max \|Δ\| 0 m/s for CLIMADA. Real-binary paired test of the interpolation property: 0.8075 measured vs 0.8015 predicted. GeoClaw `holland2008` has no regression data. GAHM's isotach match is in-sample. Eberenz calibration is in-sample on 473 events, with no held-out region test in the passages examined. | execution / source / documentation |
| V2 differential | ktools golden files (200 checks) and OasisLMF golden-output tests exist; a ktools↔OasisLMF run was designed (Finding 7), not run; no fuzzing of either kernel is known. | measured / source |
| V3 concurrency/crash/physical | Not examined; crash and partial-stream behaviour of the streaming kernels was not tested. | not examined |
| V4 plant/field replay | Hindcasts against gauges and high-water marks (Westerink: Betsy and Andrew; SLOSH: six storms); HAZUS damage against HUD surveys and insurance data; landfall-rate comparison. Field-data replay here: not measured. | cited |

## Boundaries

- **Not examined:**
  - The FCHLPM 2023/2025 hurricane standards text and professional-team reports (PDF retrieval failed), so their computer, documentation, sensitivity/uncertainty and validation requirements are unknown here.
  - The contents of Powell et al. 2005, Tao et al. 2022 and Vickery et al. 2009 (Crossref metadata only), so FPHLM architecture, testing and boundary-layer details are absent.
  - The Holland 1980 primary text: the publisher PDF has no text layer, so the B range 1–2.5 and ρ = 1.15 come from the CLIMADA and ADCIRC restatements.
  - Execution of OasisLMF `gulmc`/`fmpy`, the ktools↔OasisLMF test, and any ADCIRC or GeoClaw build or run.
  - GAHM's iterative `B_g` solver; CLIMADA H10/ER11 beyond source reading; HAZUS terrain and gust conversions (in the Vickery 2000 papers).
  - Post-loss amplification (demand surge): ktools `placalc` applies event and amplification factors (`-F` absolute, `-f` relative secondary factor; `placalc/main.cpp` l.31-32) and is exercised by `make check`, but its semantics were not analysed.
- **Unknown:**
  - Whether downstream studies used GeoClaw `holland2008`/`holland2010` with the Finding 4.1 behaviour, and when that path was introduced.
  - Whether ktools' unguarded square root yields NaN in practice, given that random values equal to `prob_to` are rare.
  - Surge-error magnitudes caused by recipe differences, because the hindcast design was not run.
- **Known not to apply:** the Finding 4.4 rescale does not apply to GAHM (`uvpr`) or NWS=8. The interpolation mean shift is absent for interpolation points inside each bin's middle third, which includes the centred ktools example bins (sample/analytic ratio 1.0078, within Monte Carlo noise of about 0.0098).
- **Unsupported:** fmpy has no distinct allocation rule 3 (it is mapped to 2). CLIMADA's calibrated impact functions cover wind only.
- **Not established:** that any recipe is "most accurate" (no observation-based wind comparison was made); that the ADCIRC or GeoClaw toy rows predict those codes' output (they omit asymmetry, inflow and land effects); or that Eberenz V_half values are building fragilities.

## Evidence

All evidence was acquired on 2026-11-21 (UTC). SHAs were resolved via `api.github.com/repos/<repo>/commits/HEAD`; files were fetched from `raw.githubusercontent.com/<repo>/<sha>/<path>`. Line numbers are cited inline in Findings.

- `CLIMADA-project/climada_python` @ `cc0b21516a156384f718e328c59b60138dc1775c`: `climada/hazard/trop_cyclone/{trop_cyclone_windfields.py (sha256 28d30b5a9d3f3625a4b2e85ec51c9dae8977ce64492eeaa6f2d20d8a73cea830), trop_cyclone.py}`, `climada/hazard/{tc_tracks.py, tc_tracks_synth.py}`, `climada/entity/impact_funcs/trop_cyclone.py`, `climada/data/system/tc_impf_cal_v01_{TDR1.0,TDR1.5,RMSF}.csv`.
- `adcirc/adcirc` @ `ae33c51ffc2922f33dbf042e2948701c22e7bdc3`: `src/{constants.F90, nws08.F90, wind.F}`, `wind/{vortex.F, aswip.F}`, `docs/user_guide/model_configuration/meteorological_forcing/{nws_parameters.rst, generalized_asymmetric_holland_model.rst}`.
- `clawpack/geoclaw` @ `091b28d19ecb1fb0e3b4f1881ccf4ce17d3886a8`: `src/2d/shallow/surge/parametric_met_forcing_module.f90` (sha256 `cc6de93dd725382e5a9c722b16b8a80ba08f9c8161a69322640a6b09933e079a`), `src/2d/shallow/surge/met_forcing_module.f90`, `src/python/geoclaw/data.py`, recursive tree listing (regression-data paths).
- `OasisLMF/OasisLMF` @ `02aaf854da34b37cc3f386afc00b481727951e93`: `oasislmf/pytools/gulmc/{README.md, cli.py}`, `oasislmf/pytools/gul/{core.py, random.py}`, `oasislmf/pytools/fm/{README.md, TECHNICAL.md, manager.py, compare.py}`, `tests/pytools/gulmc/test_gulmc.py`, `tests/fm/test_fmpy.py`.
- `OasisLMF/ktools` @ `4a7506c74a22593b1fd7aa32b32b91c44509be01` (VERSION.in 3.12.5), built from the API tarball of this commit: `src/gulcalc/{gulcalc.cpp, getrands.h}`, `src/fmcalc/main.cpp`, `src/validatedamagebin/validatedamagebin.cpp`, `src/include/oasis.h`, `examples/fm_alloc/README.md`, `ktest/runtests.sh`.

Literature. Every DOI was verified through Crossref (`api.crossref.org/works/<doi>`; titles, journals, volumes and pages matched). Full text was read for Vickery 2006 I/II (NHR 7(2):82-93, 94-103), Westerink 2008 (MWR 136(3):833-864), Eberenz 2021 (NHESS 21:393-415) and Aznar-Siguan 2019 (GMD 12:3085-3097). Abstract or summary text was read for Holland 1980, 2008, 2010, Emanuel 2006, Emanuel 2011 and Knapp and Kruk 2010. Only Crossref metadata was checked for Powell et al. 2005 (`10.1016/j.jweia.2005.05.008`, JWEIA 93(8):651-674), Vickery et al. 2009 (`10.1016/j.jweia.2009.05.005`, JWEIA 97(7-8):392-405) and Tao et al. 2022 (`10.1002/spe.3086`, SPE 52(7):1736-1755). SLOSH NWS 48 was read as OCR text of NOAA's PDF. FCHLPM: the 2025-10-28 meeting-summary PDF and the professional-team-reports index page on `fchlpm.sbafla.com`.

Execution. Scripts are in `support/` (indexed in `support/README.md`) and full outputs in `support/outputs.txt`. ktools: `autoreconf -fi && ./configure --disable-parquet && /usr/bin/time -v make -j8 && /usr/bin/time -v make check`, then `sh support/ktools_probe.sh <tree> /tmp/ktx` and `python3 support/gul_paired_shift.py gul_base.csv gul_stress.csv`. The other probes take a scratch directory or no arguments.

## Revalidation

- **Recipe constants:** diff only the cited line ranges between the pinned SHA and the new one: CLIMADA `DEF_RHO_AIR`, `DEF_GRADIENT_TO_SURFACE_WINDS`, `_b_holland_clip_interval`, `_compute_angular_windspeeds_h08` and `from_tracks(model=...)`; ADCIRC `RhoAir`, `windReduction`, `one2ten`, the NWS=8 B clamp and `PRBCKGRND`, and `uvp` l.704-719; GeoClaw `atmos_boundary_layer`, `sampling_time`, `get_holland_b_2008` and its two callers. Then rerun `python3 support/holland_toy.py` with any changed constant.
- **GeoClaw units:** set `SHA` in `support/geoclaw_b2008_probe.sh` and rerun. The issue is fixed if the Pa column is no longer exactly 1.00000/2.50000 or the callers convert units. A failed line-range guard means the function moved.
- **CLIMADA:** set `SHA` in `support/climada_profile_probe.py`. The probe aborts if any of the nine functions is missing, and `max|upstream-toy|` reports whether the toy still matches.
- **Oasis interpolation:** rerun `support/ktools_probe.sh` and `support/gul_paired_shift.py` on a new ktools build. A ratio near 0.80 means the scheme is unchanged; near 1.00 means it was fixed. For OasisLMF, inspect `get_gul` in `gul/core.py`.
- **fm:** ktools `make check` covers the five `fm_alloc` cases; for fmpy, check `fm/manager.py` for the rule-3 mapping.
- **Literature** values are fixed by DOI. The FCHLPM standards need fresh retrieval, since 2021, 2023 and 2025 editions exist.
