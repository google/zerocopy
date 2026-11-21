# Avalanche danger assessment and avalanche models: SNOWPACK stability indices, the EAWS danger scale and Matrix, the Conceptual Model of Avalanche Hazard, random-forest danger-level and instability models, and AvaFrame com1DFA

## Summary

- **The danger level is an ordinal judgement with no direct ground truth.** The European Avalanche Danger Scale defines the level as a function of snowpack stability, the frequency distribution of that stability, and avalanche size. The 2025 EAWS Matrix is a lookup over 3 stability panels × 3 frequency rows × 5 sizes (45 cells). Its cell values come from a survey of forecasters, and about half of the cells carry a bracketed alternative level. The authors of the Matrix papers state that formal validation of the Matrix logic is not possible, because neither the level nor its inputs can be measured independently.
- **Empirical anchors** (Swiss and Norwegian data):
  - The frequency of the weakest stability class discriminates the danger level best (ρ = 0.81).
  - Single-test stability is weaker (Rutschblock ρ = 0.4; ECT ρ = 0.22), and avalanche size is weaker still (ρ = 0.15–0.25).
  - Forecasts from neighbouring regions agree about 91 % of the time within a forecast centre, but only about 62–63 % across centre or national borders.
  - Forecast centres have significant level biases (median bias ratios ≤ 0.84 to ≥ 1.19).
- **SNOWPACK computes stability by hard-coded, piecewise empirical rules** at `snowpack-model/snowpack@b324cbd`. The indices are a natural index (Sn38), a skier index (Sk38), a structural index (SSI = Sk38 + 2 − "lemons"), a deformation-rate index (Sdef), a critical cut length and a relative-threshold-sum weak-layer score. All of them are clamped (mostly to [0.05, 6]) and referred to a 38° slope.
  - The class rule compiled in by default (`prof_classi = 2`) assigns "fair" whenever no lemon is found, whatever Sk38 is.
  - Two test-infrastructure defects were observed by execution:
    - The `res1exp` CTest smoke test **passes vacuously when `numdiff` is absent**, and its 2017 reference outputs no longer match the current binary.
    - `BUILD_TESTING=ON` fails to compile `albedoTest.cc:584`.
- **The two data-driven models are trained on different kinds of label.**
  - The random-forest (RF) danger-level models (Pérez-Guillén et al. 2022) are trained on published forecasts, or on a "tidy" forecast subset. They reach 72–78 % accuracy on two held-out winters (RF1 74–76 %, RF2 72–78 %), which is close to the estimated 76 % agreement between forecasts and local nowcasts.
  - The RF instability model (Mayer et al. 2022) is trained on 146 balanced profile pairs labelled by Rutschblock results and local nowcasts. Its output is a probability `P_unstable` (threshold 0.77 for `P_max`), validated on 121 independent profiles.
  - Agreement figures from the two models are therefore not comparable.
- **AvaFrame com1DFA is a thickness-integrated particle–grid solver.** It has 12 friction or rheology laws and the default `samosATAuto`. It uses a fixed `dt = 0.1 s`, or `dt = cMax · cell size` when kernel-radius time stepping is enabled.
  - At `OpenNHM/AvaFrame@61f1bb9`, the similarity-solution and energy-line verification tests run and reproduce the published convergence behaviour (relative L2 thickness error 0.058 → 0.017 as the particle count rises from 9,270 to 59,138). The energy-line errors are below 1 cm and below 10⁻⁴ degrees.
  - The **dam-break test script fails** at this revision with `NotImplementedError` (`iniStep=True`).
  - A release volume of exactly 60,000 m³ leaves `samosATAuto` unresolved: the code uses `>` where the docstring promises `>=`.
  - The AIMEC docstrings swap the definitions of FP and FN relative to the code.

## Applicability

The subjects are related as follows:

- **Two pinned open-source codes:**
  - `snowpack-model/snowpack` at `b324cbdd1b7f4da4db8ff8a5b408274e88ac1945` (committed 2026-06-01). This repository bundles MeteoIO, SNOWPACK and Alpine3D. Only the SNOWPACK stability code, its `res1exp` and `albedo` tests, and the build were examined.
  - `OpenNHM/AvaFrame` at `61f1bb90f5aee0e10b81a46d15aca1ed8663fb7a` (committed 2026-11-19). The repository was renamed from `avaframe/AvaFrame`. The examined files are `com1DFA` (including `checkCfg.py`), `ana3AIMEC`, `ana1Tests`, `in3Utils/cfgUtils.py` and three run scripts.
- **Peer-reviewed papers** that define or evaluate the models and practices, identified by DOI.
- **Two EAWS web documents** (the danger scale page, and the Matrix definitions PDF updated May 2025 and accepted June 2025). They are identified by URL and version text only; no immutable hash exists.

The report concerns their combination:

- how a physical snowpack model produces stability indices;
- how forecasters' conceptual frameworks turn stability, frequency and size into a level;
- how consistent the published levels are;
- how machine-learning models were trained against those levels;
- how an open dense-flow module is formulated and verified.

Exact observation versus extension:

- **Source claims about SNOWPACK** hold for `b324cbd` with its compile-time constants (`Stability::prof_classi = 2`, `sh_mod = 2`) and its default configuration keys. Operational centres may run other versions or configurations. The papers describe SLF running SNOWPACK on four virtual 38° slopes. Our run was a flat-field test run.
- **Execution claims about SNOWPACK** come from a Release build of `b324cbd` on one x86-64 Linux host, running the repository's `res1exp` test case (Weissfluhjoch study plot data, winter 1995/96). They are not claims about operational model chains.
- **AvaFrame claims** hold for `61f1bb9`, installed into Python 3.12.16 with numpy 1.26.4, and run with the repository's own test inputs. The GMD paper describes version 1.3 and says its code "differs slightly from the implementation of the com1DFA module used for operational purposes". Numerical agreement with the paper is therefore qualitative: same trends, same order of magnitude.
- **Literature claims** are scoped to the data sets, regions and seasons each paper names: Swiss and Norwegian data (Techel et al. 2020); the European Alps 2011/12–2014/15 (Techel et al. 2018); Swiss IMIS stations 1997/98–2019/20 (Pérez-Guillén et al. 2022); Swiss profiles 2001/02–2018/19 (Mayer et al. 2022). Transfer to other snow climates is untested in those sources.

## Findings

### 1. What the physical snowpack model simulates

**Physics** (Basis: documentation, papers):

- SNOWPACK solves one-dimensional heat transfer, water transport, vapour diffusion and large viscous deformation of a three-phase (ice, water, air) snowpack. It uses "a fully implicit Lagrangian Gauss–Seidel finite-element method" (Bartelt & Lehning 2002).
- Typical implicit time steps are about 15 min, because forcing is measured at 30-min intervals.
- Microstructure is carried as four primary state variables: grain size, bond size, dendricity and sphericity. Each evolves by rate equations for equitemperature, kinetic-growth and melt metamorphism (Lehning et al. 2002, Part II). Bond size is "the single most important parameter for snow viscosity and thermal conductivity".
- Surface hoar is modelled as a layer boundary rather than a numerical layer.

**Evaluation reported** (Part III):

- Objective profile scores comparing temperature, density, snow type, liquid water content and grain size averaged "above 0.8" over five winters.
- Temperature scored best, and grain size and type scored worst.
- Surface-hoar formation rates reached r² = 0.87 with the adapted Monin–Obukhov approach.

> [!NOTE]
> Crossref maps DOI `10.1016/S0165-232X(02)00073-3` to the 5-author paper on pages 147–167 (Part II, *Snow microstructure*). It maps `10.1016/S0165-232X(02)00072-1` to the 4-author paper on pages 169–184 (Part III, *Meteorological forcing, thin layer formation and evaluation*). Some secondary listings swap these two DOIs.

**Operational use** (Morin et al. 2020; Basis: documentation):

- Switzerland runs SNOWPACK "at 130 locations whenever new data over at least 1 h is available", plus runs driven by numerical weather prediction every 3 h.
- France uses SAFRAN–Crocus–MEPRA by massif and 300 m elevation band (17 slope or aspect configurations).
- Canada, Italy, Austria and the USA run station-based or gridded SNOWPACK.
- Norway discontinued Crocus in 2017/18 ("unreliable results and lack of personnel").
- The review finds "little systematic undertaking of the verification of the predictive capability … in terms of avalanche hazard forecast". It calls post-processing and visualization "probably the weakest point" of model chains.

### 2. SNOWPACK stability indices as implemented

Basis: source (`Source/snowpack/snowpack/Stability.cc`, `StabilityAlgorithms.cc`, `StabilityAlgorithms.h` at `b324cbd`) + derived.

#### 2.1 Compile-time constants

`Stability.cc` L32–40 fixes these values:

- `psi_ref = 38.0` (reference slope);
- `max_stability = 6.0`;
- `minimum_slab = 0.1` m;
- `ground_rough = 0.2` m;
- `min_depth_ssi = 0.1` m;
- `skier_depth = 1.0` m;
- `min_thick_crust = 0.03` m;
- `nmax_lemon = 2`;
- `sh_mod = 2`.

`StabilityData` sets `alpha_max_rad(54.3*to_rad)`, with the note "alpha_max(38.) = 54.3 deg".

#### 2.2 Per-element loop

`checkStability`, L170–208, walks from the surface down. For each element `e` it computes:

- hand hardness (parameterization `MONTI`, `BELLAIRE` or `ASARC`, chosen by `HARDNESS_PARAMETERIZATION`);
- the deformation-rate index `S_dr`;
- Young's modulus from the mean slab density;
- stresses reduced to 38°;
- shear strength (`DEFAULT` or `NIED`, chosen by `STRENGTH_MODEL`);
- `S_n`, `S_s` (Sk38), the SSI, and a critical cut length.

The optional key is read with the comment "`MULTI_LAYER_SK38` … //HACK: temporary key until we decide for a permanent solution" (L77).

#### 2.3 The indices

| Index (output column) | Definition in source | Clamp | Location |
|---|---|---|---|
| Reduced stresses | `sig_n = -C·(cos ψ_ref / cos θ)² / 1000` kPa; `sig_s = sig_n·tan ψ_ref` | – | `compReducedStresses` L545–549 |
| Natural stability Sn38 | `(Sig_c2 + phi·sig_n) / sig_s` | [0.05, 6] | `getNaturalStability` L556–560 |
| Skier stability Sk38 | `(Sig_c2 + phi·sig_n) / (sig_s + Δτ_skier)`, with Föhn's line-load formula for an 85 kg skier on 1.7 m skis at depth `z − Pk` | [0.05, 6]; 6 if `z ≤ Pk` | `getLayerSkierStability` L573–589 |
| Penetration depth Pk | `min(0.8·43.3/ρ̄_top30cm, HS/cos θ − top_crust)` | – | `compPenetrationDepth` L495–537 |
| Structural SSI | `(nmax_lemon − n_lemon) + Sk38`. A lemon is counted when the hardness difference is > 1.5 or the grain-size difference `2·|Δrg|` is > 0.5 (mm) | [0.05, 6] | `initStructuralStabilityIndex` L119–135 |
| Deformation rate Sdef | `σ_crit(ε̇_neck, T) / σ_neck`; returns 0.1 if the ice fraction is < 0.05 | [0.1, 6] | `setDeformationRateIndex` L470–488 |
| Critical cut length | Gaume–Wever closed form: `λ·(−τ_g + √(τ_g² + 2σ_n(τ_p − τ_g)))/σ_n`, with `λ = √(E′·D·F_wl)` and Poisson ratio 0.2 | capped at 3 m; 3 m if slab < 0.1 m; 0 if the radicand is < 0 | `CriticalCutLength` L1339–1362 |
| Relative threshold sum (RTA) | Sum of 6 min–max normalized terms: grain size, grain-size difference, inverted hardness, hardness difference, persistent grain type, and a Weibull depth weight (w1 = 2.5, w2 = 50 cm) less a crust term. Divided by the profile maximum | [0, 1] | `getRelativeThresholdSum` L615–722 |

#### 2.4 Derived checks

- The source comment says the skier term is "around 0.1523 kPa / layer_depth". With `Constants::g = 9.80665` the formula gives 0.15232 kPa·m (support script `snowpack_constant_checks.py`).
- `0.8 × 43.3 = 34.64`. This matches the `Pk = 34.6/ρ30` feature definition used by Mayer et al. (2022, Table B1).

#### 2.5 Shear strength (`setShearStrengthDEFAULT`, L1116–1216)

- Shear strength is a power law in relative density whose coefficients depend on grain type. For example:
  - precipitation particles (PP): `2.85·ρ_r^1.13`;
  - rounded grains (RG): `7.39·ρ_r^1.20`;
  - faceted crystals and depth hoar (FC, DH): `18.5·ρ_r^2.11`.
- Surface hoar uses a regression on age, load, depth, thickness and temperature (`sh_mod = 2`, "New regression by Bruce Jamieson w/o Emin").
- Melt-freeze crusts are overridden: `if ( Edata.mk % 100 >= 20 ) { Sig_c2 = Sig_c3 = 4.; }` (L1196–1199, commented "Hack for MFCs").
- `STpar.Sig_c2 = std::min(Sig_c2, STpar.strength_upper)`, so a layer's effective strength is capped by the strength of the layer above.

#### 2.6 Weak-layer search windows (`findWeakLayer`, L247–328)

- **Sn38 and Sdef:** the minimum over layers deeper than 0.1 m below the surface and higher than 0.2 m above the ground.
- **Sk38 and SSI:** the minimum over layers between `Pk` and `Pk + 1.0` m. Near-ties (`|ΔSSI| < 0.09`) go to the layer with more lemons.
- The search runs only if `HS/cos θ > 0.2` m and `HS/cos θ − Pk > 0.1` m.

#### 2.7 Profile class (`S_class2`)

`prof_classi = 2` selects `classifyStability_SchweizerBellaire2` (L846–867):

- ≥ 2 lemons → class 1 (poor);
- 1 lemon → class 1 if Sk38 < 0.48, class 3 if Sk38 < 0.71, otherwise class 5;
- **0 lemons → class 3 whatever Sk38 is**;
- SSI outside (0, 100) → −1.

The three other class rules (thresholds 1.25/1.55 on SSI; 0.45/1.32 on Sk38/SSI; a 5-class Schweizer–Wiesinger rule) are compiled in but unreachable without editing `prof_classi`.

#### 2.8 Observations, not claimed as defects

- **Critical cut length uses mixed layers.** `CriticalCutLength(slab_thick, slab_mass/slab_thick, cos_sl, EMS[e-1], STpar, EMS[e].C)` (`Stability.cc` L203) takes weak-layer density and grain radius from element `e−1`. It takes `tau_p = STpar.Sig_c2` (L1343) from the strength just computed for element `e`, capped by the layer above. Whether this mixing is intended is **unknown**.
- **Self-flagged code.** `compCriticalStress` (L436–459) carries "HACK use this value for temperatures below 227.2 K (Quick and dirty fix;-)" and "TODO check that argument of sqrt is correctly written". `setShearStrengthDEFAULT` contains `assert(STpar.sig_n>0.); //in a few cases, we have received sig_n<0 from the caller`. Release builds compile the assertion out.

#### 2.9 Executed output

Basis: execution, Release build at `b324cbd`, `tests/res1exp`, flat field (see `support/execution_record.md`).

- Of 1782 three-hourly snow-covered records in winter 1995/96, the profile class was 1 (poor) in 506, 3 (fair) in 838, 5 (good) in 261, and −1 in 177.
- Median Sk38 was 0.505 and median SSI 2.05. Sk38 and SSI hit the 6.0 cap in 145 records, and Sn38 in 304.
- The run took 29.48 s for 231 days at 15-min steps. That is 22,176 steps, or ≈ 1.33 ms per step (derived), at 39.8 MB peak RSS.

These numbers characterize this test case only. They are not a skill measure.

### 3. Conceptual model of avalanche hazard and the danger level

**Conceptual Model of Avalanche Hazard (CMAH)** (Statham et al. 2018; Basis: documentation):

- The model asks four sequential questions:
  1. Which avalanche problem type? There are nine: dry loose, wet loose, storm slab, wind slab, persistent slab, deep persistent slab, wet slab, glide slab and cornice.
  2. Where is it in the terrain?
  3. How likely is it? This combines sensitivity to triggers (unreactive, stubborn, reactive, touchy) with spatial distribution (isolated, specific, widespread), giving unlikely … almost certain.
  4. How big? Destructive size 1–5.
- Likelihood and size are plotted as a rectangle on a hazard chart. The rectangle's extent conveys uncertainty.
- The CMAH deliberately avoids numeric probabilities. In its example, "the probability of an avalanche on a single slope of 0.01 could be considered likely, while the probability … across an entire region of 0.1 could be considered unlikely".
- Its link to the North American danger scale "is not deterministic". In contrast, the Bavarian Matrix was "designed specifically to determine a danger rating".
- The paper reports no quantitative validation, and notes that "the lack of quantitative links between the components … leaves the process highly susceptible to human error and bias".

**EAWS danger scale and Matrix** (Basis: normative EAWS documents + papers):

- The scale defines five levels. Its guidance gives approximate usage and fatality shares:
  - 1-Low: forecast about 20 % of the season, about 5 % of fatalities;
  - 2-Moderate: about 50 % of the season, about 30 % of fatalities;
  - 3-Considerable: about 30 % of the season, about 50 % of fatalities;
  - 4-High: a few days per winter, about 10 % of fatalities;
  - 5-Very high: "very rarely forecast".
- The 2025 Matrix definitions:
  - **Stability** has four classes: very poor (natural / very easy to trigger), poor (easy, e.g. a single skier), fair (difficult, e.g. explosives) and good.
  - **Frequency** f(i) = n_i/n has four classes: many, some, a few, none or nearly none. Thresholds are deliberately left open ("no clear answer exists yet").
  - **Size** has five classes, from small to extremely large.
- Reading rules:
  - Start at the weakest stability class that is not "none or nearly none".
  - Good stability means 1-Low regardless of the other factors.
  - Take the unbracketed level.
  - Across several problems, take the highest level.

**Disagreement between the two Matrix sources** (Basis: normative EAWS documents + papers): the EAWS PDF says cells are left uncolored if fewer than **70 %** of survey respondents gave an estimate. Müller et al. (2025, Part A) say **80 %**.

**How the Matrix was derived** (Part A, Basis: papers):

- There were 76 responses from 12 countries.
- 27 of the 45 cells carry a secondary level D2.
- A clear majority existed for only 18 cells.
- On average one level gets 67 % of the votes.

**Operational use** (Part B, 26 services, three winters; Basis: papers):

- The median Matrix non-compliance was 4 % for dry snow and 7 % for wet and gliding snow.
- The cells poor–some–size 2 and very poor–some–size 3 act as "transition zones". Poor–some–size 2 is 31 % of level-2 cases and also 13 % of level-3 cases.
- Level 5 was issued once.
- A one-class disagreement in a single factor in half of all cases changes the suggested level in "approximately 21 % of cases".

**Empirical relationships** (Techel, Müller & Schweizer 2020; Basis: papers):

- The data are 9,310 stability tests and 39,017 avalanche observations from Switzerland and Norway, with local nowcast levels as labels.
- Very-poor Rutschblock (RB) results rise from 2 % at 1-Low to 38 % at 4-High.
- The frequency class correlates with the level at ρ = 0.81. The text gives thresholds of 0 %, 4 % and 20 % very-poor stability between frequency classes, for bootstrap samples of n = 25 tests. The Table 2 footnote lists the interval limits as 0, 1.8, 6.2, 21 and 100 %.
- The proportion of days whose largest avalanche reached size 3–4 rises from 20 % to 78 %.
- Conclusion: "the frequency of the most unfavorable snowpack stability class is the dominating discriminator", while size 4 separates 3 from 4. That shift is "poorly represented" in the Matrix or ADAM.
- 4-High rests on only N = 21 RB ratings.

### 4. Consistency and bias of published forecasts

Basis: papers (Techel et al. 2018).

**Data:** 23 of about 30 Alpine forecast centres, 2011/12–2014/15, 477 forecast days, 281 warning regions with a median size of 350 km².

**Metrics:**

- Agreement `P_agree = N(ΔD=0)/N`.
- Bias ratio `B_ij = [N(ΔD=0)+N(ΔD+)]/[N(ΔD=0)+N(ΔD−)]`. Values outside 0.95–1.05 are significant at p < 0.05 by binomial test.
- `P_v.crit = N(D≥4)/N`.
- `P_favor = N(D=1)/N`.

| Measure | Value |
|---|---|
| Neighbour agreement, all pairs (median) | 83 % |
| Within a forecast centre | 91 % (IQR 83–96 %) |
| Across centres / across national borders | 63 % / 62 % |
| Chance baseline (same climatology) | 40 % (D_max), 36 % (D_morning) |
| Pairs with significant bias, across / within centres | 76 % / 51 % |
| Median bias ratio, lowest centres (NIE, SWI, BAY) / highest (LOM, BRI, SAL) | ≤ 0.84 / ≥ 1.19 |
| Level 4–5 forecasts, median over regions | 2.5 % (IQR 1.1–4 %); max 15.3 % |

**Stated causes:**

- region size;
- operational constraints;
- local interpretation of the scale, which "does not specify whether the highest or the spatially most representative danger level should be communicated";
- possibly real climate differences, which the study could not test.

### 5. Data-driven models: what was learned from which label

Basis: papers.

| | Danger-level RF (Pérez-Guillén et al. 2022) | Instability RF (Mayer et al. 2022) |
|---|---|---|
| Target | Regional danger level (4 classes; 5 merged into 4) | Binary stable/unstable weak layer; output `P_unstable` = mean vote of 400 trees |
| Labels | `D_forecast`: published forecasts (500,545 cases, 3,820 days). `D_tidy`: about 10 % subset "presumably" closer to conditions ("should not be considered a verified danger level") | RB result + local nowcast: unstable = RB poor ∧ LN ≥ 3; stable = RB good ∧ LN = 1 |
| Features | 67 meteorological + SNOWPACK features (incl. Sk38, Sn38, SSI, critical cut length, Pk) → 47 after correlation filter → 30 by recursive elimination | 34 → 6: viscous deformation rate, critical cut length, Pk, weak-layer sphericity, slab ⟨ρ/gs⟩, weak-layer grain size |
| Training / test | Train 1997/98–2017/18; test 2018/19–2019/20 (≈ 10 %); 5-fold season-blocked CV | 146 balanced DAV profile pairs (5-fold CV 88 ± 6 %); independent SWISS set 121 profiles |
| Headline skill | Accuracy 0.74 (RF1) / 0.72 (RF2) vs `D_forecast`; 0.76 / 0.78 vs `D_tidy`; 4-High F1 0.53–0.64 | SWISS, manual weak layers: accuracy 88 % (T = 0.5); `P_max` at T = 0.77: accuracy 93 %, precision 96 %, recall 92 % |
| Comparator | Forecast–nowcast agreement ≈ 76 %; adding the previous day's level raises accuracy to 0.82 but drops it to 0.43 / 0.29 on days when the level rose / fell | Published thresholds of Reuter et al. (2022) without retraining: recall 42 %; retrained depth-2 tree on the same features: 68 %; critical cut length alone: 72 % (5-fold CV on DAV) |
| Stated limits | Labels are forecasts made at 7,000 km² scale vs predictions at single stations; weaker on persistent-weak-layer days | Feature selection, tuning and training on the same set; no intermediate-stability profiles; transferability untested |

The two headline numbers measure different things:

- **Pérez-Guillén et al.** measure agreement with forecaster output, which is itself about 76 % consistent with nowcasts and tends to over-forecast by one level.
- **Mayer et al.** measure agreement with field stability tests filtered by nowcast. Weak layers were matched to the profiles by hand. Automatic weak-layer detection reached a probability of detection of 60 % overall on DAV, and 75 % (unstable) and 46 % (stable) on SWISS.

Code and data: renkulab GitLab plus EnviDat `10.16904/envidat.330`; WSL GitLab plus EnviDat `10.16904/envidat.351`. The repositories were not examined.

### 6. AvaFrame com1DFA formulation and numerics

**Formulation** (Tonnel et al. 2023, Basis: papers):

- The thickness-integrated mass and momentum equations are derived Lagrangianly in terrain-following coordinates under shallow flow on mildly curved topography, with constant density.
- Mass is carried on particles. Pressure gradients use SPH with a spiky kernel in the local tangent plane, and thickness lives on the grid.
- The convergence criterion follows Ben Moussa & Vila: `dt = C·r_kernel` and `n_ppk = n_ppk0·(r_kernel/r_kernel0)^α`, with α < −1.

**Implementation** (Basis: source at `61f1bb9`):

- **Friction law selection.**
  - `com1DFA.py` L2176–2191 maps the `frictModel` string to an integer over 12 laws: samosAT (and its Small and Medium variants), Coulomb, Voellmy, wetsnow, VoellmyMinShear, CoulombMinShear, spatialVoellmy, O'Brien–Julien, Herschel–Bulkley and Bingham.
  - The default `frictModel = samosATAuto` (`com1DFACfg.ini` L330) is resolved before that mapping. `prepareVarSimDict` L3604 computes the release volume, and `checkCfg.checkCfgFrictionModel` rewrites the model name using `volClassSmall = 25000` and `volClassMedium = 60000` m³ (`com1DFACfg.ini` L332–333).
- **Friction laws** (`DFAfunctionsCython.pyx` L300–376):
  - Coulomb: `τ = μ σ_b`.
  - Voellmy: `τ = μ σ_b + ρ g u²/ξ`.
  - samosAT (`DFAToolsCython.pyx` L825–863): `τ = τ0 + p μ (1 + R_s0/(R_s0 + R_s)) + ρ u² / (ln(max(h/R, 1))/κ + B)²`, where `R_s = ρu²/(p + 0.001)`.
- **Default parameters:**
  - μ_samosAT = 0.155, κ = 0.43, R = 0.05, B = 4.13 (L335–340);
  - Voellmy μ = 0.155, ξ = 4000 (L356–357);
  - ρ = 200 kg m⁻³ (L65).
- **Time stepping.**
  - The default is `dt = 0.1` s fixed and `tEnd = 400` s (L159–161).
  - With `sphKernelRadiusTimeStepping = True`, `dt = cMax · min(DEM cell, neighbour-grid cell)` with `cMax = 0.02` (`timeDiscretizations.py`). This is a geometric rule, not velocity-based adaptivity.
  - The run stops when kinetic energy falls below 1 % of its peak (L167–171).
- **Particles and grid:**
  - Initial particle placement is random with `seed = 12345` (L28–33).
  - Mass per particle is set from a 0.25 m release-thickness slice (`MPPDH`).
  - Mesh cells are 5 m.
- **Step order** (`computeEulerTimeStep`, L2731–2877):
  1. friction and body forces;
  2. SPH pressure force;
  3. optional cohesion;
  4. position update (centred);
  5. particle splitting;
  6. secondary release;
  7. neighbour search;
  8. grid fields;
  9. optional DEM adaptation.

**Defects at this revision:**

- **`samosATAuto` leaves exactly 60,000 m³ unhandled** (Basis: source + execution of the upstream function). The docstring of `checkCfg.checkCfgFrictionModel` (L84–88) promises `relVolume >= volClassMedium - set frictModel=samosAT`. The code (L154–160) is:

  ```python
      if cfg["GENERAL"]["frictModel"].lower() == "samosatauto":
          if relVolume < float(cfg["GENERAL"]["volClassSmall"]):
              cfg["GENERAL"]["frictModel"] = "samosATSmall"
          elif float(cfg["GENERAL"]["volClassSmall"]) <= relVolume < float(cfg["GENERAL"]["volClassMedium"]):
              cfg["GENERAL"]["frictModel"] = "samosATMedium"
          elif relVolume > float(cfg["GENERAL"]["volClassMedium"]):
              cfg["GENERAL"]["frictModel"] = "samosAT"
  ```

  Calling the installed function with the default configuration (`support/avaframe_samosat_auto_boundary.py`) gives:

  | release volume (m³) | resulting model | volume indicator |
  |---|---|---|
  | 24,999 | `samosATSmall` | S |
  | 25,000 | `samosATMedium` | M |
  | 59,999 | `samosATMedium` | M |
  | 60,000 | **`samosATAuto` (unchanged)** | M |
  | 60,001 | `samosAT` | L |

  `samosatauto` is not in `frictModelsList`, so `frictModelsList.index(frictModel)` (`com1DFA.py` L2191) would raise `ValueError` for a release volume of exactly 60,000 m³. This is derived from Python's `list.index` semantics; a full simulation at that volume was not run. The volume indicator (`setVolumeIndicator`, L3945–3968, `>` for L) labels that case "M". With real raster-derived volumes an exact tie is improbable.
- **Dam-break test unreachable** (Basis: source + execution). `com1DFA.py` L1177–1184 reads:

  ```python
      if cfg["GENERAL"].getboolean("iniStep"):
          message = (
              "iniStep=True is currently not supported due to recent refactoring of thickness handling. "
              "Please set iniStep=False in your configuration file. "
              "Support for iniStep will be restored in a future update."
          )
          log.error(message)
          raise NotImplementedError(message)
  ```

  `data/avaDamBreak/Inputs/damBreak_com1DFACfg.ini` L22 sets `iniStep = True`, so `runScripts/runDamBreak.py` exits with that error after 2.88 s. The dam-break verification test from the GMD paper therefore cannot run unmodified at `61f1bb9`. The two lines after the `raise` (L1185–1186) are unreachable.
- **AIMEC docstrings swap FP and FN** (Basis: source). `ana3AIMEC/aimecTools.py` documents:

  ```text
  L1429-1430:  FN: float / ref = False sim2 = True
  L1431-1432:  FP: float / ref = True sim2 = False
  ```

  The code computes the opposite:

  ```python
  L1483:  fpInd = np.where((refMask[nStart:] == 0) & (compRasterMask[nStart:] == 1))
  L1484:  fnInd = np.where((refMask[nStart:] == 1) & (compRasterMask[nStart:] == 0))
  ```

  The same swapped docstring appears in `ana3AIMEC.py` L271–277. The code follows the standard convention, and area fractions are normalized by the reference area `tp + fn` (L1494). Readers of the docstring will invert FP and FN.
- AIMEC thresholds the peak field `runoutResType = ppr` at `thresholdValue = 1` kPa (`ana3AIMECCfg.ini` L25, L35) inside a 600 m-wide thalweg domain. It derives runout from the maximum or mean over cross sections.

### 7. Verification results we reproduced

Basis: execution at `61f1bb9`; table in `support/avaframe_similarity_solution_errors.csv`.

**Similarity solution** (Hutter et al. 1993; Coulomb μ = tan 25°, 35° plane, `tEnd = 5` s, `cMax = 0.02`):

| r_kernel (m) | nPPK0 | aPPK | particles | rel. L2 error h | rel. L2 error hū | loop CPU (s) |
|---|---|---|---|---|---|---|
| 3 | 10 | −0.5 | 9,270 | 0.0576 | 0.0739 | 3.87 |
| 3 | 10 | −2.0 | 19,943 | 0.0366 | 0.0479 | 6.99 |
| 3 | 20 | −2.0 | 39,865 | 0.0232 | 0.0301 | 19.55 |
| 3 | 30 | −2.0 | 59,138 | 0.0172 | 0.0223 | 32.41 |
| 5 | 10 | any | 2,557 | 0.0704 | 0.0834 | 0.83–1.02 |
| 5 | 30 | any | 7,674 | 0.0286 | 0.0354 | 1.78–1.80 |

- **Effect of aPPK at r_kernel = 5 m (derived).** `aPPK` has no effect, because `n_ppk = n_ppk0·(5/5)^α`. The four aPPK rows per nPPK0 give identical particle counts and errors. A convergence study therefore needs `r_kernel ≠ r_kernel0` for α to matter.
- **Error slope (derived).** At r_kernel = 3 m and α = −2, the log–log slope of the h error versus particle count is −0.66 between 19,943 and 39,865 particles, and −0.76 between 39,865 and 59,138.
- **Consistency with the paper.** This matches the paper's statement that deviations decrease for α < −1. Our errors cannot be compared cell by cell with the paper's figures, which give no numeric tables.
- **Energy-line test** (`data/avaParabola`):
  - runout distance error −6.28 × 10⁻³ m;
  - elevation error 8.96 × 10⁻⁴ m;
  - runout angle error 6.61 × 10⁻⁵ °;
  - velocity-height RMSE 8.99 × 10⁻⁴ m.

  The paper reports "less than 10⁻² m and 10⁻⁴°".

### 8. Performance and resource footprint across six levels

| Level | SNOWPACK | AvaFrame com1DFA | Danger-level / instability RF | EAWS Matrix, CMAH |
|---|---|---|---|---|
| L1 authoring / maintenance | not measured | not measured | not measured | Matrix: survey of 76 forecasters plus 3 winters of testing (cited) |
| L2 toolchain build | MeteoIO 46.15 s, 335 MB; SNOWPACK 23.74 s, 762 MB (`make -j8`, measured) | `pip install .` with Cython 3:29.82, 439 MB (measured, includes downloads) | not measured | not applicable |
| L3 run latency | 29.48 s per station-season, ≈ 1.33 ms per 15-min step (measured / derived); operational cadence ≥ hourly at 130 stations (cited) | 24-run similarity sweep 1:41.72 wall, as two batches of 12 runs in a process pool (`nCPU = min(floor(96·0.5), nSims)` = 12, `cfgUtils.getNumberOfProcesses`); per-run loop CPU 0.83–32.4 s; energy-line test 1:01.23 (measured); "seconds to minutes" (cited) | not reported by the papers; not measured | human judgement; not measured |
| L4 generated-code throughput | as L3 (one process, single station) | as L3; Cython kernels, parallel only across simulations (cited) | not measured | not applicable |
| L5 checking / verification cost | `res1exp` comparator 5.5 s (measured); CTest 30.40 s (measured, vacuous) | similarity post-processing 48.70 s (measured) | not measured | not applicable |
| L6 memory / disk / binary | 39.8 MB peak RSS; binary 2.4 MB + 35.7 MB `libsnowpack` + 67.9 MB `libmeteoio`; one 3-hourly season `.pro` 59.6 MB (measured) | 433–542 MB peak RSS per process tree root (measured); per-worker RSS not measured | not measured | not applicable |

### 9. Comprehensibility and simplicity

**C1 (comprehensibility):**

- **Several indices for one invariant.** SNOWPACK exposes at least six stability indices (Sn38, Sk38, SSI, Sdef, critical cut length, RTA) and one class. They answer one question: is there a layer that can fail under a plausible load and propagate? Each has its own clamp, depth window and constants.
- **Lossy default class.** The default class rule discards Sk38 when no lemon exists. A reader seeing "class 3" cannot tell whether it came from the lemon count or from Sk38.
- **Ordinal labels without measurable ground.** Forecaster-facing tools (CMAH, Matrix) are compact, with 4 × 4 × 5 classes. But their frequency terms have no fixed thresholds, so two careful users can disagree by a class. Part B estimates that such a disagreement changes the level in about 21 % of cases.
- **Documentation that misleads.** The AIMEC docstring inversion is a legibility defect. It costs nothing at run time and misleads every reader.

**C2 (simplicity):**

- **Separating invariant from quirk.** The stability indices separate a physical invariant, failure initiation then crack propagation (critical cut length), from accidents of history: hand-hardness regressions, the melt-freeze-crust hack and the 227.2 K temperature fix.
- **The unifying abstraction is visible but unrealized.** The literature points to two quantities per candidate weak layer: an initiation propensity and a propagation propensity. Their spatial frequency would feed the frequency axis. Mayer et al.'s six-feature RF is a data-driven step in that direction. The code still carries all the legacy indices as parallel mechanisms.
- **Friction models.** In AvaFrame, the 12 friction models are one `tau = f(σ_b, u, h)` interface. The `samosATAuto` volume switch is a lookup table layered on top of it, which makes the result depend discontinuously on release volume at 25,000 and 60,000 m³ (derived).
- **Duplicated volume classification.** The volume switch is implemented twice with different comparison operators: `checkCfgFrictionModel` uses `>` and leaves the tie unhandled, while `setVolumeIndicator` uses `>` but falls through to "M". This is the "multiple mechanisms enforcing one invariant" pattern. A single classifier returning one of {S, M, L}, used both to name the simulation and to select parameters, would remove the gap.

### 10. How implementations and claims are validated

- **V1 (specification adequacy, non-vacuity).**
  - **SNOWPACK `res1exp` passes vacuously** (Basis: source + execution).
    - `tests/res1exp/CMakeLists.txt` declares `FAIL_REGULAR_EXPRESSION "error|differ"`.
    - `run_res1exp.sh` pipes `numdiff … | grep "+++"`.
    - On a host without `numdiff`, CTest printed four `numdiff: command not found` lines and `res1exp.smoke ... Passed`.
  - **The references are stale.** They are dated 2017-06-21 (Snowpack 3.41) with 100 columns, while the binary writes 103. A token comparison at relative tolerance 10⁻³ finds 111,421 of 121,431 numeric `.met` tokens out of tolerance; the token streams are not aligned, so this is an upper bound. We therefore expect the test to fail where `numdiff` is installed (derived; not executed with `numdiff`).
  - **The albedo test does not compile** with GCC 15.2. `albedoTest.cc:584` reads `if (slope.snow_erosion)`, but `Slope::snow_erosion` is a `std::string` (`DataClasses.h` L841).
  - For the ML models, label adequacy is the binding constraint. `D_tidy` is explicitly not verified, and the EAWS Matrix cannot be formally validated (Part B).
- **V2 (code verification against analytic and semi-analytic solutions).** AvaFrame ships analytic tests: similarity solution, energy line, rotation, and dam break, which currently fails. We ran two of them. SNOWPACK ships `implicitsolver` (analytic heat equation) and `linearsolver` tests. These were not executed, because the albedo compile error stopped the `BUILD_TESTING` build.
- **V3 (concurrency, crash, silicon): known not to apply** to these offline models, with two exceptions.
  - AvaFrame's random particle initialization is reproducible only through `seed = 12345`.
  - Its parallelism is a `multiprocessing` pool over whole simulations (`com1DFAMain` L182 `pool.map`), so there is no in-memory state shared between simulations. We did not test determinism across worker counts.
- **V4 (field falsification, human comprehension).**
  - Snowpack-model skill against avalanche activity has been checked only in limited studies (Morin et al.). Mayer et al.'s Weissfluhjoch check reached 73 % daily accuracy over 597 days.
  - AIMEC compares simulated runout with reference rasters or observed events using TP/FP/FN/TN areas.
  - Human-model consistency is measured directly by agreement rates: forecast versus nowcast (≈ 76 %), Matrix compliance (median 4 %), and neighbour agreement (62–91 %).

## Boundaries

- **Not examined:**
  - SNOWPACK physics beyond the stability code;
  - the operational SLF configuration (virtual slopes, Richards-equation water transport);
  - `res5exp`, `basics` and the analytic solver tests;
  - Crocus and MEPRA source;
  - the danger-level and instability RF code repositories and their data;
  - AvaFrame `com2AB`, `com4FlowPy` and the other com modules;
  - the AIMEC comparison against real events;
  - the rotation and FP tests.
- **Unknown:**
  - whether the mixed layer indices in `CriticalCutLength` are intended;
  - whether operational SNOWPACK builds use `prof_classi = 2`;
  - whether `res1exp` fails when `numdiff` is installed (inferred, not run);
  - AvaFrame determinism across worker counts;
  - why the danger-level RF's skill on persistent-weak-layer days is lower.
- **Known not to apply:**
  - Our flat-field `res1exp` statistics are not the 38° four-aspect operational output.
  - The AvaFrame errors are for test geometries, not real terrain.
- **Not measured:**
  - L1 authoring effort for any system;
  - RF training and inference time and memory (none of the papers report them);
  - AvaFrame per-worker RSS;
  - energy or power draw.
- **Unsupported by the evidence:**
  - That 72–78 % RF accuracy means the model is "as good as forecasters". It equals forecaster–nowcast agreement on held-out winters at station scale, which is a different comparison.
  - That `P_unstable` is a calibrated probability. Mayer et al. say intermediate stability was absent from training.
  - That EAWS Matrix cells are thresholds of measurable quantities.
  - That com1DFA verification implies hazard-map accuracy.
  - That SNOWPACK's `res1exp` reference outputs validate the current code.

## Evidence

Observation dates: GitHub pins resolved and source read 2026-11-21 (UTC). Builds and runs were done the same day, as were Crossref checks of the DOIs listed below and the EAWS pages.

**Source** (path:line at the pinned commit):

- `snowpack-model/snowpack@b324cbdd1b7f4da4db8ff8a5b408274e88ac1945`:
  - `Source/snowpack/snowpack/Stability.cc` L32–49, L55–89, L119–135, L149–245 (L203 critical cut length call), L247–328;
  - `Source/snowpack/snowpack/StabilityAlgorithms.cc` L436–459, L470–488, L495–537, L545–589, L615–722, L846–912, L1116–1216 (L1196–1199 melt-freeze crust), L1339–1362;
  - `Source/snowpack/snowpack/StabilityAlgorithms.h` L32–50;
  - `Source/snowpack/snowpack/Constants.h` L49–50, L76;
  - `Source/snowpack/snowpack/DataClasses.h` L841;
  - `Source/snowpack/tests/res1exp/{CMakeLists.txt,run_res1exp.sh,io_res1exp.ini}`;
  - `Source/snowpack/tests/albedo/albedoTest.cc` L584.
- `OpenNHM/AvaFrame@61f1bb90f5aee0e10b81a46d15aca1ed8663fb7a`:
  - `avaframe/com1DFA/com1DFA.py` L182, L1177–1186, L2176–2191, L2281–2289, L2731–2877, L3603–3622, L3945–3968;
  - `avaframe/com1DFA/checkCfg.py` L82–88, L153–168;
  - `avaframe/in3Utils/cfgUtils.py` L1146–1175 (`getNumberOfProcesses`);
  - `avaframe/com1DFA/com1DFACfg.ini` L28–33, L65, L155–206, L238–243, L330–360;
  - `avaframe/com1DFA/DFAfunctionsCython.pyx` L289–376;
  - `avaframe/com1DFA/DFAToolsCython.pyx` L825–863;
  - `avaframe/com1DFA/timeDiscretizations.py` `getSphKernelRadiusTimeStep`;
  - `avaframe/ana3AIMEC/ana3AIMEC.py` L229–277;
  - `avaframe/ana3AIMEC/aimecTools.py` L1388–1511;
  - `avaframe/ana3AIMEC/ana3AIMECCfg.ini` L10–48;
  - `avaframe/data/avaDamBreak/Inputs/damBreak_com1DFACfg.ini` L20–22;
  - `avaframe/data/avaSimilaritySol/Inputs/simiSol_com1DFACfg.ini`.

**Execution:** `support/execution_record.md`, which also gives the tarball SHA-256 values. Support files:

- `support/avaframe_similarity_solution_errors.csv`;
- `support/avaframe_similarity_solution_table.py`;
- `support/avaframe_samosat_auto_boundary.py` (its output is the table in §6);
- `support/snowpack_ref_compare.py`;
- `support/snowpack_constant_checks.py`.

**Papers.** All DOIs were Crossref-verified for title, authors, venue, volume and pages; locators are sections or tables:

- Bartelt & Lehning 2002, CRST 35(3):123–145, `10.1016/S0165-232X(02)00074-5`: abstract, Sects. 5, 8–9.
- Lehning, Bartelt, Brown, Fierz & Satyawali 2002 (Part II), CRST 35(3):147–167, `10.1016/S0165-232X(02)00073-3`: abstract, Sect. 2.
- Lehning, Bartelt, Brown & Fierz 2002 (Part III), CRST 35(3):169–184, `10.1016/S0165-232X(02)00072-1`: Sects. 2–4.
- Morin et al. 2020, CRST 170:102910, `10.1016/j.coldregions.2019.102910`: Sects. 2–4, 6, 9. Read from the open-access published PDF.
- Statham et al. 2018, Nat. Hazards 90(2):663–691, `10.1007/s11069-017-3070-5`: Sects. 1, 4–6, Tables 4–7.
- Techel, Mitterer, Ceaglio et al. 2018, NHESS 18:2697–2716, `10.5194/nhess-18-2697-2018`: Eqs. 1–4, Sects. 5–6.
- Techel, Müller & Schweizer 2020, TC 14:3503–3521, `10.5194/tc-14-3503-2020`: Sects. 2–6, Table 2.
- Pérez-Guillén et al. 2022, NHESS 22:2031–2056, `10.5194/nhess-22-2031-2022`: Sects. 3–7, Tables 1–3, B1.
- Mayer, van Herwijnen, Techel & Schweizer 2022, TC 16:4593–4615, `10.5194/tc-16-4593-2022`: Sects. 2–5, Tables 1, 2, B1, B2.
- Tonnel, Wirbel, Oesterle & Fischer 2023, GMD 16:7013–7035, `10.5194/gmd-16-7013-2023`: Sects. 2–6, Table 1, Fig. 9.
- Müller, Techel & Mitterer 2025 (Matrix Part A), NHESS 25:4503–4525, `10.5194/nhess-25-4503-2025`: Sects. 4–6.
- Techel, Müller, Marquardt & Mitterer 2026 (Matrix Part B), NHESS 26:1161–1181, `10.5194/nhess-26-1161-2026`: abstract, Sects. 4–6.

**Standards** (no immutable identity; accessed 2026-11-21):

- https://www.avalanches.org/standards/avalanche-danger-scale/
- https://www.avalanches.org/standards/eaws-matrix/
- https://www.avalanches.org/wp-content/uploads/2025/08/EAWS_matrix_definitions_EN.pdf ("updated in May 2025, accepted by EAWS General Assembly in June 2025")

## Revalidation

- **Stability rules.** Diff `Stability.cc` and `StabilityAlgorithms.cc` between `b324cbd` and the new revision, and re-read:
  - the constants block (L32–49);
  - `prof_classi`;
  - `classifyStability_SchweizerBellaire2`;
  - the `CriticalCutLength` call site;
  - the clamps.

  If those regions are unchanged, §2 holds. Then rerun `support/snowpack_constant_checks.py`.
- **SNOWPACK test vacuity.** Build with `-DBUILD_TESTING=ON`. If the albedo target still fails, build the `snowpack` target alone, then run `ctest -R res1exp.smoke -V` on a host without `numdiff`. "Passed" alongside `numdiff: command not found` reconfirms the finding. With `numdiff` installed, the same command tests the staleness inference. Re-check the reference header date with `bzcat output_ref/MST96_res.met.bz2 | sed -n 11p`.
- **AvaFrame.**
  - Search for the `iniStep` guard in `com1DFA.py`, and run `runScripts/runDamBreak.py`. Success means the dam-break finding is obsolete.
  - Run `support/avaframe_samosat_auto_boundary.py`. A row for 60,000 m³ that reads `samosAT` means the tie is fixed.
  - Re-read `analyzeArea` (docstring versus `fpInd`/`fnInd`).
  - Rerun `runScripts/runSimilaritySol.py` and `support/avaframe_similarity_solution_table.py`, then compare with the CSV. Particle counts should match exactly, because the seed is fixed. Errors should match to the printed digits if numerics are unchanged.
- **Literature.** The EAWS Matrix and its thresholds are revised by EAWS General Assemblies. Re-read the definitions PDF's version line and the 70 % versus 80 % cell-coloring rule.
