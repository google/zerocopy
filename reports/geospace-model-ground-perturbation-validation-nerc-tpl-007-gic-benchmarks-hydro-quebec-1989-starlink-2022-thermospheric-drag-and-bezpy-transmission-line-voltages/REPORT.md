# Geomagnetically induced currents for grid planning and the validation of operational geospace models: TPL-007 benchmark scaling, impedance-based line voltages in bezpy, dB/dt skill scores, March 1989 and February 2022

## Summary

- **The North American planning standard is a fixed linear pipeline with two scalar fudge factors.** NERC TPL-007-4 makes Planning Coordinators and Transmission Planners study a *benchmark* event (8 V/km reference peak geoelectric field) and a *supplemental* event (12 V/km, localized). The reference field is scaled by a geomagnetic-latitude factor α = 0.001·e^(0.115·L), clipped to 0.1 ≤ α ≤ 1, and by an Earth-conductivity factor β. β is either taken from a table of one-dimensional physiographic Earth models or computed as E/8 (or E/12) from a "technically justified" Earth model driven by the reference waveform. That waveform is the 13–14 March 1989 Ottawa record, scaled to 60° geomagnetic latitude so that the reference Quebec model gives exactly 8 V/km. Transformers whose maximum effective GIC is at least 75 A per phase (benchmark) or 85 A per phase (supplemental) need a thermal impact assessment. Basis: normative.
- **β is a property of the waveform's spectrum, not only of the ground.** The standard itself says Table 3 depends on the reference storm's frequency content. I drove the 22 tabulated 1-D models shipped with `bezpy` through its production pipeline with nine synthetic storm-like waveforms. Rankings agreed with Table 3 (Spearman 0.899–0.964), but the median absolute error was 0.115–0.133 in β, and one model's β varied by a factor of up to 2.32 across waveforms. A β computed from a different storm is therefore not the standard's β. Basis: execution (synthetic driver, not the NERC waveform).
- **One-dimensional impedances understate the spread of hazard.** With 64 measured 3-D impedances, Lucas–Love–Kelbert found line voltages more than an order of magnitude above *and* below the regional 1-D values. For March 1989, 62 lines exceeded 100 V with 3-D impedances against 16 with 1-D impedances. Basis: documentation (peer-reviewed abstract); not re-run here.
- **`bezpy` reproduces an independent GIC solver.** At the pinned revision, its Lehtinen–Pirjola nodal-admittance solve of the EPRI 21-bus test case matches published PowerWorld per-phase GICs for the six generator step-up transformers to within −0.12% to −0.15%. Its line integral is a left-endpoint rule (`E` sampled at segment start points). Basis: source + execution.
- **Operational geospace selection rested on a deliberately coarse binary-event metric.** Pulkkinen et al. 2013 scored five models. They used six events and six primary stations, cut each record into non-overlapping 20-minute windows, and counted hits, misses and false alarms for |dB/dt| thresholds of 0.3, 0.7, 1.1 and 1.5 nT/s. From those counts they computed POD, POFD and the Heidke skill score. The SWMF configuration (BATS-R-US + RIM + RCM) had the highest POD and HSS. No model reached POD or HSS above 0.5 at 1.5 nT/s, and lead time is at best 15–30 minutes for fast CMEs. Welling et al. 2018 recommended four changes: far more stations, eight events, metrics by magnetic local time, and metrics by activity type, plus a frequency-bias metric. Basis: documentation.
- **The two case studies show forecast products that did not match the decision needed.** In 1989 the Hydro-Québec collapse came early in the storm, at a substorm coincident with the second sudden commencement (07:43 UT), when Dst was not yet extreme. In February 2022 the Space Weather Prediction Center forecast the G1–G2 storm, but issued no drag-specific product. The operator's pre-launch NRLMSISE-00 analysis expected a ~50% density increase. The physics model indicated 50–125% at 200–400 km. In my counterfactual run, NRLMSIS driven by the observed ap raises 210 km density by at most 14–15% over a quiet-ap baseline. Basis: documentation + execution (empirical model only).

## Applicability

- **Standard.** NERC TPL-007-4, applicable to Planning Coordinators, Transmission Planners, Transmission Owners and Generator Owners with power transformers whose high-side wye-grounded winding exceeds 200 kV. I read the requirement and Attachment 1 text from a public transcription because my fetch tool could not open nerc.com. The bodies of Tables 1–3 were not in that text. Table 2 and Table 3 values below are as transcribed in `bezpy/tpl007.py` at the pinned revision, and I did not check them against the PDF. Attachment 1-CAN, the Canadian alternative, is noted but not analysed.
- **Code.**
  - `greglucas/bezpy@b7944f9404f3ab59373279f8116cc288e90dc390` (Python ≥ 3.12). I installed it editable into a Python 3.13 virtual environment with NumPy 2.5.4, SciPy 1.18.1, pandas 3.1.1 and shapely.
  - `SWxTREC/pymsis` installed as release 0.13.0. I inspected the source tree at `d8170cbde127aa802fc48b9deaf328f25ce32eb5` but executed the PyPI 0.13.0 binary distribution. I did not establish that this distribution was built from exactly that commit.
  - `SWMFsoftware/SWMF@4e927561205457169a907668d93eeffa014f2414` and `spacepy/spacepy@015c1adcf20f642fb31f8a35cb94463cac520fe7`: source inspection only. Neither was built or run.
- **Relationships.** The report follows one chain:

  solar wind → magnetosphere model (SWMF family) → ground ΔB and dB/dt (validated with binary-event metrics; read by `spacepy.pybats`) → geoelectric field E = Z·B (bezpy `mt`) → line EMF V = ∫E·dl (bezpy `tl`) → transformer neutral GIC (bezpy `tl.network`) → TPL-007 thresholds.

  The Starlink case leaves this chain at the magnetosphere and goes to thermospheric density, evaluated with the empirical NRLMSIS family through `pymsis`. The papers are interpreted against the code; no paper's own software was run.
- **Observation host.** Linux, 96 vCPU Intel Xeon at 2.60 GHz, 236 GiB RAM. Timings are single runs on that host class.

## Findings

### 1. What TPL-007-4 requires

Basis: normative (TPL-007-4 requirement text and Attachment 1).

| Req. | Who | What | Deadline or threshold |
|---|---|---|---|
| R1 | PC with its TPs | Assign responsibilities for models, studies, measurement-data processes | — |
| R2 | responsible entity | Maintain System models and GIC System models | — |
| R3 | responsible entity | Criteria for acceptable steady-state voltage performance during the Attachment 1 events | — |
| R4 | responsible entity | Benchmark GMD Vulnerability Assessment of the Near-Term Transmission Planning Horizon, on-peak and off-peak load, against Table 1 | at least once every 60 calendar months; distributed within 90 days |
| R5 | responsible entity | Give each TO/GO the maximum effective GIC for the worst-case field orientation; GIC(t) on written request | GIC(t) within 90 days of request |
| R6 | TO, GO | Benchmark thermal impact assessment of each transformer | if max effective GIC ≥ 75 A per phase; within 24 calendar months |
| R7 | responsible entity | Corrective Action Plan if Table 1 performance not met | CAP within 1 year; non-hardware actions within 2 years, hardware within 4 years of the CAP |
| R8–R11 | as R4–R7 | Supplemental event | R10 threshold 85 A per phase |
| R12 | responsible entity | Process to obtain GIC monitor data from at least one monitor | — |
| R13 | responsible entity | Process to obtain geomagnetic field data | — |

**Attachment 1 benchmark event**

- The event consists of:
  - a reference peak of 8 V/km "derived from statistical analysis of historical magnetometer data";
  - latitude scaling α, from equation 3 or Table 2;
  - conductivity scaling β;
  - a reference geomagnetic-field waveform.
- E_peak = 8·α·β (benchmark) or 12·α·β (supplemental).
- The supplemental peak applies over a localized area. One example the standard gives is 100 km north–south by 500 km east–west, with the benchmark field elsewhere. The enhancement lasts 2–5 minutes.
- β has two routes:
  - read it from Table 3 using the conductivity map, taking "the largest β factor of adjacent physiographic regions" when no model is available;
  - compute βb = E/8 or βs = E/12 from a technically justified Earth model and the reference waveform.
- For areas spanning several α or β values, the planner may use the largest value or a non-uniform field.
- The reference Quebec Earth model (Table 4) has layers of 15 km at 20,000 Ω·m, 10 km at 200, 125 km at 1,000 and 200 km at 100, over a 3 Ω·m half-space.
- The waveform is the NRCan Ottawa record of 13–14 March 1989. Ottawa is at 55° geomagnetic latitude. The record was "scaled up to the 60° reference geomagnetic latitude ... such that the resulting peak geoelectric field amplitude computed using the reference earth model was 8 V/km". It is sampled every 10 s.

**Two routes that disagree by construction**

- *α formula vs Table 2.* My probe evaluated both in `bezpy.tpl007.alpha_factor`. The formula gives 0.1768 at 45° against a tabulated 0.20, and 0.6264 at 56° against 0.60. The maximum |difference| over the Table 2 rows is 0.0264. Basis: execution, with the table values as transcribed in bezpy.
- *Tabulated vs computed β.* The standard warns that "Scaling factors in Table 3 are dependent upon the frequency content of the reference storm." See §2.3.

### 2. From magnetic data to geoelectric field and line voltage (`bezpy`)

#### 2.1 Layered-Earth impedance

Basis: source, `bezpy/mt/site.py`, `Site1d.calcZ`, lines 670–724.

- For each layer, `k = sqrt(1j·ω·MU/ρ)` (line 694), with `MU = 4π·10⁻⁷`.
- At the bottom half-space, `Z = iωμ/k`.
- Moving upward, with reflection coefficient r, each layer gives `Z_i = iωμ(1 − r·e^(−2k_i h_i)) / (k_i(1 + r·e^(−2k_i h_i)))`. The code comments call this "Following NERC report", referring to the 2013 GMD Task Force GIC Application Guide.
- The DC impedance is set to zero (line 716).
- The result is converted to (mV/km)/nT by `Z_output[1, :] = Z[0, :] * (1.0e-3 / MU)` (line 722), with `Zyx = −Zxy` and zero diagonal.

A 1-D Earth therefore produces E perpendicular to B, and the same scalar applies in every direction. A 3-D site (`Site3d`) carries a full 2×2 tensor spline-interpolated from measured periods.

#### 2.2 Convolution

Basis: source, `site.py` lines 60–85 and 834–950.

- E(f) = Z(f)·B(f) with `rfft`/`irfft`.
- Inputs are zero-padded to `N = 2 ** (int(np.log2(N0)) + 2)` (line 70), at least twice the next power of two, so that FFT multiplication does not wrap around.
- `Site3d.calcZ(extrapolate=...)` controls frequencies outside the measured band:
  - `"zeros"` band-stops them;
  - `"asymptotic"`, the default at this revision, continues |Z| along the half-space √ω asymptote anchored at the band edges (lines 407–429).
- The upstream method-comparison page `docs/validation.md` reports synthetic relative RMS E errors of 0.648 for `"zeros"` vs 0.030 for `"asymptotic"` with a 300–7,200 s impedance band. On real storms over 342 magnetotelluric (EMTF) sites in a central-US box, the median ratio of peak |E| (`asymptotic`/`zeros`) was 1.009 for May 2024 and 1.022 for October 2003. The maximum ratio, 7.01, came from a survey whose transfer functions stop near 1,190 s. Basis: documentation (upstream harness results; not re-run).

#### 2.3 β depends on the driving spectrum

Basis: execution of `bezpy.tpl007.beta_factor` on synthetic waveforms; `support/probe_geo_bezpy.py`, output in `support/probe_geo_bezpy.out`.

- `beta_factor` drives each site with a spatially uniform plane wave. It divides the peak |E| by the Quebec model's peak |E| *from the same waveform* (`tpl007.py` lines 311–315). This makes β invariant to waveform amplitude, and the function warns if the reference model does not give 8 V/km within 2% (lines 326–334).
- bezpy does not redistribute the NERC waveform file, and neither did I. The probe uses bezpy's own test stand-in: band-limited (100–10,000 s) random-phase series with an f^(−e) amplitude spectrum and independent Bx and By. I ran 3 seeds × e ∈ {0.5, 1.0, 1.5}.

| model | Table 3 βb (as transcribed) | synthetic min | median | max | max/min |
|---|---|---|---|---|---|
| PT1 | 1.17 | 1.168 | 1.172 | 1.224 | 1.05 |
| CP2 | 0.95 | 1.036 | 1.313 | 1.317 | 1.27 |
| IP1 | 0.94 | 0.676 | 0.683 | 0.793 | 1.17 |
| AP1 | 0.33 | 0.225 | 0.276 | 0.277 | 1.23 |
| IP4 | 0.41 | 0.131 | 0.168 | 0.239 | 1.82 |
| PB2 | 0.46 | 0.185 | 0.186 | 0.268 | 1.45 |
| BOU | 0.28 | 0.073 | 0.121 | 0.170 | 2.32 |

All 22 models are in the output file. Across the nine waveforms, the Spearman correlation with Table 3 was 0.899–0.964 and the median |β − βTable| was 0.115–0.133.

Reading:
- The pipeline ranks ground correctly.
- The absolute β of a resistive-over-conductive model such as BOU or IP4 moves by a factor of about 2 when only the storm spectrum changes.
- A utility that computes its own β must use the NERC waveform for the result to be the standard's β. Bezpy's reported `reference_peak_E` is the guard against silently using the wrong waveform.

#### 2.4 Line voltage

Basis: source, `bezpy/tl/transmissionline.py`.

- Segment vectors `dl` (km, north/east) come from haversine distances (`tl/utils.py`).
- `calc_voltages` interpolates E to the line points in one of three ways:
  - `how="nn"`: nearest MT site;
  - `"1d"`: the containing physiographic polygon;
  - `"delaunay"`: barycentric weights in a gnomonic projection. Points outside the hull get NaN (line 268).
- It then computes `voltages = np.sum(E3d * self.dl[np.newaxis, :, :], axis=(1, 2)) / 1000.0` (line 276), where `E3d` is taken at `points[:-1]` (for example `self.nearest_sites[:-1]` at line 234).
- This is a **left-endpoint rectangle rule**: each segment uses the field at its starting vertex. `resampled(max_segment_km)` subdivides segments along great circles so that the rule converges.
- In bezpy's own synthetic harness, `how="delaunay"` with 1 km resampling has a relative RMS voltage error of 0.037, against 0.108 without resampling. Basis: documentation, `docs/validation.md` section D7.

#### 2.5 Network GIC

Basis: source + execution, `bezpy/tl/network.py`.

- Lines (with EMF), grounded transformer windings and substation grounding form a resistive DC network. The module solves it in the nodal-admittance form that Boteler & Pirjola 2017 show to be equivalent to the original Lehtinen–Pirjola two-matrix formulation.
- `effective_gic(i_high, i_low, a=1.0, b=1.0)` returns `|a·I_H + b·I_L|`. The docstring states that TPL-007 guidance derives `a` and `b` from the turns ratio. **The default a = b = 1 is not that guidance.**
- Neutral currents are for the single-line-equivalent (three phases lumped). The upstream test divides by 3 to compare with published per-phase values.

EPRI 21-bus test case (Horton et al. 2012 topology, as distributed with PowerModelsGMD):

| transformer | bezpy |I_n|/3 (A per phase) | published (A per phase) | rel. error |
|---|---|---|---|
| xf-6-7-7 / xf-6-8-8 | 59.017 | 59.090 | −1.23×10⁻³ |
| xf-12-13-9 / -10 | 22.339 | 22.373 | −1.52×10⁻³ |
| xf-17-18-13 / -14 | 31.501 | 31.548 | −1.50×10⁻³ |

Driving the network with a uniform 1 V/km field from bus coordinates gave:
- eastward: 58.889, 22.290 and 31.431 A for the same transformers, within 0.37% of the published column;
- northward: a maximum of 46.66 A per phase (xf-5-20-5/6).

Each solve took 0.6–1.8 ms. The upstream suite (`test_network`, `test_tpl007`, `test_mt_1d`, `test_tl`) passed 61 tests in 2.37 s.

The inference that the published column corresponds to an eastward 1 V/km field is **derived** from that agreement only.

#### 2.6 Sensitivity to the impedance model

Basis: documentation (peer-reviewed abstracts).

| study | data | finding |
|---|---|---|
| Bedrosian & Love 2015 | EarthScope impedance tensors, midwestern US, uniform 100 s source | Geographic differences in E amplitude of about ×100, direction up to 130°, phase over a quarter wavelength. A 500 nT, 100 s storm gives a mean of 2.71 V/km with a site-to-site range of 0.15–16.77 V/km. |
| Lucas, Love & Kelbert 2018 | 64 empirical 3-D impedances vs regional 1-D, mid-Atlantic lines | Voltages differ by more than 10× in both directions. March 1989: 62 lines above 100 V (3-D) vs 16 (1-D). |
| Lucas et al. 2020 | 31 years, 84 storms, 24 observatories, 1,079 MT sites, 17,258 lines | Once-per-century E ranges from 0.02 V/km (Idaho) to 27.2 V/km (Maine). About 30% of surveyed area exceeds 1 V/km. Line voltages approach 1,000 V. |
| Pulkkinen et al. 2012 | statistical 100-year scenarios | 20 V/km (resistive) and 5 V/km (conductive) 100-year 10-s maxima at high latitude, with a drop of about an order of magnitude across ~50° geomagnetic latitude. |
| Kelbert et al. 2017 | frequency- and time-domain convolution with 3-D tensors | Validated against measured storm-time E in Japan. |

### 3. How geospace models were validated for operations

#### 3.1 Pulkkinen et al. 2013

Basis: documentation (full text).

- **Events (UT):**
  1. 29 Oct 2003 06:00 to 30 Oct 06:00
  2. 14 Dec 2006 12:00 to 16 Dec 00:00
  3. 31 Aug 2001 00:00 to 1 Sep 00:00
  4. 31 Aug 2005 10:00 to 1 Sep 12:00
  5. 5 Apr 2010 00:00 to 6 Apr 00:00
  6. 5 Aug 2011 09:00 to 6 Aug 09:00

  Events 1–4 had been used in earlier GEM challenges. Events 5 and 6 were "surprise events" that were "not communicated to the modelers prior to the model and model setup delivery to CCMC", and were selected jointly by CCMC and SWPC. This is a blind hold-out within a six-event suite.
- **Stations.** There were 12 observatories with 1-minute data. Primary metrics used six:
  - high latitude: PBQ (replaced by SNK for events 5–6), ABK, YKC;
  - mid-latitude: WNG, NEW, OTT.
- **Event definition.** Non-overlapping windows of t_f = 20 min. An event is |dB/dt| exceeding the threshold within a window. Thresholds were 0.3, 0.7, 1.1 and 1.5 nT/s. Varying t_f between 10 and 45 min "did not change the central results notably".
- **Metrics** from {H, F, M, N}:
  - POD = H/(H+M)
  - POFD = F/(F+N)
  - HSS = 2(HN − MF)/((H+M)(M+N) + (H+F)(F+N))

  HSS is 0/0 when there are no crossings, so thresholds must be crossed within the event set.
- **Models.**

  | identifier | model | grid |
  |---|---|---|
  | 2_LFM-MIX | LTR-2.1.1 | 163,000 cells, 0.4 R_E |
  | 3_WEIGEL | empirical | — |
  | 4_OPENGGCM | 4.0 with CTIM | 3.9 million cells, 0.25 R_E |
  | 5_WEIMER | empirical | — |
  | 9_SWMF | 2011-01-31; BATS-R-US + RIM + RCM | 1 million cells, 0.25 R_E |

- **Outcome.**
  - Section 5 says 9_SWMF "provides the highest POD and HSS for most of the thresholds". The Discussion says "for all dB/dt thresholds". Both statements are in the paper, and I preserve the discrepancy.
  - At 1.5 nT/s, no model exceeds POD or HSS of 0.5.
  - Event 1 dominates the statistics for large thresholds.
  - Lead times are "15–30 min at best" for fast CMEs driven from L1.
- **Related efforts.**
  - The predecessor GEM 2008–2009 challenge (Pulkkinen et al. 2011) used 14 models, 12 stations, four storms and five metrics. It found that "the ranking of the models is strongly dependent on the type of metric used" and that "one cannot pick the absolute 'winner'".
  - A follow-on validation of local K-index (Glocer et al. 2016) used six events, six observatories, contingency tables and distribution metrics.

#### 3.2 Recommended next-generation suite (Welling et al. 2018)

Basis: documentation (full text).

- **Stations.** Include all magnetometers reporting 60 s ΔB, and downsample data at 10 s or faster to 10 s. The paper cites about 400 northern-hemisphere stations, 31 of them at 1 s.
- **Events.** Grow from six to eight by adding 17 Mar 2015 02:00 UT (34 h) and 22 Jul 2004 06:00 UT (162 h). The paper notes that four of the original six events have |SYM-H| below 150 nT, and only event 1 is a super storm.
- **Regional analysis.** Bin by magnetic-local-time quadrant using virtual magnetometers on a 5° grid. The question per quadrant is whether any real or virtual station crosses the threshold, which separates spatial near-misses from true misses.
- **Activity type.** Segregate metrics by activity:
  - storm sudden commencements, with a window from 10 min before to 20 min after the SYM-H rise;
  - ring-current intensification, with SYM-H < 0 and dSYM-H/dt < 0 after a median filter, in windows of at least 1 h;
  - substorm expansions, identified by the Borovsky–Yakymenko 2017 method.
- **New metric.** Add frequency bias FB = (a + b)/(a + c).

Liemohn et al. 2018 separate fit metrics (RMSE, MAE) from event-detection metrics (HSS, POD) for index predictions.

**Which metrics serve whom (derived).**
- Binary dB/dt event scores over 20-minute windows match an operator's alert decision: will GIC exceed a level in this window?
- Fit metrics and MLT- or activity-segregated scores serve model developers.
- Neither class scores the quantity TPL-007 actually uses: peak E or effective GIC at a transformer. That depends on the impedance and network stages of §2, which the 2013 suite does not include.

#### 3.3 Software touch points

Basis: source.

- **SWMF.** `PARAM.XML` lines 807–838 define `#COUPLE1 NameSource NameTarget DnCouple DtCouple`. `DtCouple` is the coupling interval in simulation seconds for time-accurate runs, and "Setting both frequencies to a negative value means that there is no coupling". The default is no coupling. At the pinned revision, the `GM/` directory contains only `CMP` and `Empty`. The README tells users to fetch further repositories with `gitclone`. **Pinning the SWMF repository does not pin the BATS-R-US magnetosphere physics that was validated.**
- **spacepy.** `spacepy/pybats/bats.py` `Mag.calc_dbdt` (lines 2725–2770) computes |dB/dt|_H = √((dB_N/dt)² + (dB_E/dt)²) "following the convention of Pulkkinen et al, 2013". It uses the central difference `(x[2:] − x[:-2])/(dt[1:] + dt[:-1])` (line 2760) and second-order one-sided differences at the ends. That one-sided formula is second-order only for uniform sampling.

### 4. March 1989: what the reconstruction says

- **Solar and interplanetary drivers** (Boteler 2019 abstract).
  - Two CMEs: an X4.5 flare on 10 March and an M7.3 flare on 12 March.
  - Sudden commencements at 01:27 and 07:43 UT on 13 March, from shocks with transits of 54.5 h and 31.5 h and speeds of 760 and 1,320 km/s.
  - Peak-storm estimates of v ≈ 980 km/s and southward IMF Bs = 40–60 nT, derived from empirical relations rather than measured upstream.
  - "The second storm sudden commencement occurred at the same time as the substorm that impacted the Hydro-Québec system". External triggering may have made the substorm onset faster.
  - The blackout came "early in the storm when the Dst value was less disturbed". Later auroral-oval expansion caused problems in the United States, the United Kingdom and Sweden.

  Basis: documentation.
- **Grid sequence** (Natural Resources Canada chronology, quoting Blais & Metsa 1993 of Hydro-Québec).
  - A 9-hour blackout of the 21,000 MW system.
  - Voltage asymmetry on the 735 kV network reached 15%.
  - "Within less than a minute, the seven La Grande network static var compensators on line tripped one after the other".
  - Voltage fell to 0.2 p.u., the five lines to Montréal tripped, and 9,450 MW of generation was lost.
  - "The rest of the grid collapsed piece by piece in 25 seconds."

  Basis: documentation (government secondary source).
- **Indices** (GFZ file, excerpt in support). On 13 March 1989, Kp was 6.000 in the first 3-hour interval and 9.000 in the last (7.667–8.667 between), with Ap = 246. On 14 March, Ap = 158. Basis: source (data file).
- **Inputs and lead time (derived).** The failure was a fast protection cascade lasting seconds to a minute, triggered by a substorm at a shock arrival. The standard's 10 s benchmark waveform, the 1-minute validation data of §3.1 and the 20-minute scoring windows are all much coarser than that cascade.

### 5. February 2022: forecast products vs the decision

- **Mission facts and space weather** (Fang et al. 2022, full text).
  - 49 Starlink v1.5 satellites (Group 4-7) launched on 3 February into a 350 × 210 km, 53° orbit, targeting 550 km, with orbit raising "typically ... within 2 days".
  - "The Starlink team was only able to command 11 of the 49 satellites to a safehold attitude"; 38 re-entered.
  - Kp reached 5 for about 6 hours on each of 3 and 4 February. IMF Bz reached −19 nT (3 Feb) and −10 nT (4 Feb), with solar wind above 500 km/s.

  Basis: documentation.
- **Forecasts that existed.**
  - At 00:30 and 12:30 UTC on 1 February, SWPC's 3-day forecast said a G2 storm was likely on 2 February, lingering at G1 into 3 February.
  - The forecast Kp was 5–6 from 15:00 UT on 2 February to 03:00 UT on 3 February. The observed peak was Kp 5, between 03:00 and 09:00 UT on 3 February: later and smaller.
  - SWPC displays a WAM-IPE 400 km density forecast, run four times daily with a 2-day horizon, but "does not issue specific alerts or warnings for satellite drag".

  Basis: documentation.
- **Density estimates.**

  | source | estimate |
  |---|---|
  | Operator pre-launch (Monte Carlo with NRLMSISE-00) | about 50% density increase for the predicted storm |
  | WAM-IPE vs MSIS-00 along orbits | WAM 40–80% higher at perigee and 60–100% higher at apogee |
  | WAM-IPE storm enhancement | 50–125% at 200–400 km |
  | Fang et al., per the operator's later analysis | "at least 50% higher neutral density ... is approximately what was required to initiate safe hold" |
  | Dang et al. 2022 | about 20% at 210 km on 3 February, 20–30% on 4 February, regional enhancement over 60% |
  | Kataoka et al. 2022 | observed drag "up to 50%" at about 200 km; NRLMSIS 2.0 predicts less than 25%; GAIA predicts up to 50% |

  Baruah et al. 2024 conclude that space weather "conspired together with a low-altitude insertion and low satellite mass-to-area ratio". Basis: documentation.
- **Empirical-model response.** Basis: execution, `support/probe_msis_starlink.py`.
  - The probe ran `pymsis` 0.13.0 with observed 3-hourly ap, previous-day F10.7obs and an 81-day centred F10.7 average from the GFZ file. It compared those runs against a counterfactual in which every ap is 6 (the daily Ap of 1 February 2022), with identical solar inputs.
  - Densities are area-weighted means over |lat| ≤ 52.5°.

  | quantity | 3 Feb 10:30 UT (ap 56) | max over 3–4 Feb |
  |---|---|---|
  | 210 km density ratio, observed/quiet, MSIS-00 | 1.116 | 1.148 (4 Feb 19:30) |
  | 210 km, MSIS 2.0 and 2.1 | 1.112 | 1.144 |
  | 350 km, MSIS-00 | 1.235 | 1.281 |
  | 350 km, MSIS 2.0 and 2.1 | 1.225 | 1.270 |

  The absolute 210 km mean at 4 Feb 19:30 UT was 1.937×10⁻¹⁰ kg/m³ for MSIS-00 and 1.752×10⁻¹⁰ kg/m³ for MSIS 2.0/2.1, a 10.6% difference between model generations. MSIS 2.0 and 2.1 agree to the printed precision for mass density.

  Reading: an empirical 3-hourly-ap model cannot reproduce the 50–125% physics-model enhancement. This is consistent with Kataoka's "<25%". My ratio is a counterfactual on a latitude band, not Fang's anomaly relative to a 10-day mean, so the numbers are not directly comparable.

### 6. A case-study template linking forecasts to decisions

Basis: derived from §§4–5.

| product (issuer, cadence) | lead time available | quantity forecast | decision it could inform | was a matching product available? |
|---|---|---|---|---|
| CME arrival/Kp (SWPC 3-day, twice daily) | 1–4 days (WSA-Enlil) | Kp category G1–G5 | launch go/no-go, insertion altitude, grid posture | yes; in 2022 timing and peak were off |
| Geospace dB/dt (physics model driven from L1) | 15–30 min at best | regional dB/dt threshold crossings | operator GIC actions | an operational product exists (Gombosi et al. 2021 report operational use at SWPC); scored by binary-event POD, POFD and HSS |
| Thermospheric density (WAM-IPE) | 2 days | 400 km density | safehold timing, orbit-raise sequencing | displayed, but no drag alert or warning |
| TPL-007 benchmark | planning horizon (60 months) | 8 V/km × α × β peak E | transformer assessment, CAPs | yes; not an operational forecast |

### 7. Performance and resource footprint

| level | measured / cited / derived | value | basis |
|---|---|---|---|
| L1 authoring velocity | — | not measured | — |
| L2 toolchain build | — | bezpy is pure Python, pymsis ships compiled binary distributions, SWMF build not attempted: build times not measured | — |
| L3 latency | measured | bezpy upstream subset of 61 tests: 2.37 s (4.12 s wall including startup, 255.6 MB max RSS). EPRI-21 solve: 0.58–1.79 ms. 100,000 MSIS 2.1 point evaluations: 1.6–1.8 s | execution |
| L3 forecast lead | cited | dB/dt lead 15–30 min at best (Pulkkinen 2013). WAM-IPE: 2-day forecasts run 4×/day (Fang 2022) | documentation |
| L4 execution | measured | `SiteCollection.convolve_fft` (1-D sites): 100 sites × 8,640 samples 1.95 s; 1,000 × 8,640 20.2 s; 1,000 × 86,400 191.9 s (single run) | execution |
| L4 model scale | cited | 9_SWMF used 1 M cells at 0.25 R_E; OpenGGCM 3.9 M; LFM 163,000 (Pulkkinen 2013 Table 3) | documentation |
| L5 checking | — | no certificate or checker exists in this domain; validation-suite run cost not measured | — |
| L6 memory | measured | convolution probe peak RSS 2,528 MiB; output 659 MiB per E component for 1,000 × 86,400 | execution |

### 8. Comprehensibility, simplicity and validation

- **C1 (human comprehension).** A planner must hold about eight concepts at once: α, β, waveform, Earth model, line integral, network model, effective-GIC weighting, and the 75/85 A thresholds. Four footguns are visible in the sources:
  1. α has two permitted values per latitude.
  2. β from a table and β from a model answer different questions unless the reference waveform is used.
  3. Per-phase and three-phase currents differ by a factor of 3, as in the bezpy test comparison.
  4. bezpy's default effective-GIC weights are not the turns-ratio weights.

  Each is legible in code comments at this bezpy revision.
- **C2 (simplicity).** The physics is one linear operator chain, B → E (tensor Z) → V (line integral) → I (network admittance). bezpy composes it into reusable kernels (`voltage_matrix`, `gic_matrix`). In that chain, 1-D ground is a special case of the tensor, and tabulated β is a lossy cache of the same chain evaluated for one waveform. The standard enforces "peak E at the site" through two mechanisms that can disagree. The minimal abstraction is "the planning event is a waveform plus a transfer function", which makes the table an optional precomputation rather than a parallel rule.
- **V1 (specification adequacy).**
  - Welling et al. identify the 2013 suite's thin statistics: six stations, six events, no MLT or activity segregation, and HSS undefined without crossings.
  - bezpy's tests encode non-vacuity invariants:
    - reference β = 1;
    - amplitude invariance;
    - resistive ground gives β above conductive ground;
    - Spearman correlation > 0.85 against Table 3.
- **V2 (differential testing).** bezpy cross-checks its network solve against an independent PowerWorld computation (§2.5) and its methods against synthetic truth (`docs/validation.md`).
- **V3 (concurrency, crash, silicon).** Not applicable to these subjects; not examined.
- **V4 (replay of real events).**
  - Kelbert et al. 2017 validated E estimates against measured telluric data in Japan.
  - bezpy replayed the May 2024 and October 2003 storms over 342 sites.
  - Lucas 2018 replayed March 1989 on mid-Atlantic lines.
  - Fang et al. compared WAM densities with Starlink onboard drag estimates.
  - TPL-007 R12 and R13 create the measurement feeds (GIC monitors, magnetometers) needed for such replay. The standard does not itself require a model-versus-measurement comparison.

## Boundaries

- **Not examined:**
  - **Primary documents.**
    - The TPL-007-4 PDF on nerc.com, including the Table 1 performance criteria and the bodies of Tables 2–3. Table values are as transcribed by bezpy.
    - The NERC benchmark and supplemental waveform files. TPL-007 Table 3 is therefore **not reproduced**.
    - Attachment 1-CAN.
    - Whether a TPL-007 version later than -4 is in force on the observation date. A web search returned none, which does not prove absence.
  - **Computations not run.**
    - 3-D-impedance line voltages. EarthScope transfer functions were not downloaded, so all 1-D vs 3-D numbers are cited.
    - Any SWMF or BATS-R-US run or build.
    - Orbit propagation for Starlink.
    - A Hydro-Québec network model.
  - **Literature content.**
    - Pulkkinen 2013 per-model numeric POD, POFD and HSS values, which appear in figures.
    - The Applications Readiness Level values assigned by Pulkkinen et al. 2017. Only the abstract was read.
    - The full text of Boteler 2019. Only the abstract was read.
    - Bolduc 2002 (Hydro-Québec GIC observations and mitigation), whose full text was not accessible. Claims about post-1989 Hydro-Québec mitigation are therefore absent.
    - Whether CCMC or SWPC adopted the Welling et al. recommendations.
  - **Starlink details.** The SpaceX press release is not examined. The "11 of 49" statement is Fang et al.'s.
- **Unknown:**
  - Whether the PyPI `pymsis` 0.13.0 binary distribution corresponds byte-for-byte to the inspected commit.
  - Whether the EPRI-21 "1 V/km" published column is an eastward field. This is inferred only from the 0.37% agreement.
- **Known not to apply:**
  - The 2013 dB/dt scores say nothing about peak E or effective GIC at a transformer. Those depend on impedance and network stages outside the suite.
  - A β computed from any storm other than the NERC reference waveform is not the standard's β (§2.3).
  - Pinning `SWMFsoftware/SWMF` does not pin GM, IE or IM physics code.
- **Unsupported:** TPL-007 provides no operational forecast. It is a planning standard.
- **Attractive but unestablished conclusions:**
  - "SWMF is the best geospace model." The paper restricts this to its station, event and metric set, and says rankings vary by station and event.
  - "NRLMSIS caused the Starlink loss." The sources attribute the loss jointly to storm, insertion altitude and mass-to-area ratio.

## Evidence

All evidence was acquired on 2026-11-21 (UTC).

- **Standard.** TPL-007-4 requirement and Attachment 1 text via the nercipedia transcription (URL in `REPORT.json`).
- **Source at pinned revisions:**
  - `greglucas/bezpy@b7944f9404f3ab59373279f8116cc288e90dc390`:
    - `bezpy/tpl007.py`: lines 66–82 (constants, Quebec model), 91–135 (Tables 2–3), 163–164 (α formula), 311–334 (β normalization and warning);
    - `bezpy/mt/site.py`: 60–85, 70, 79, 407–429, 670–724;
    - `bezpy/tl/transmissionline.py`: 110–150, 214–283 (lines 234, 268, 276);
    - `bezpy/tl/network.py`: module docstring and lines 281–293, 493–509;
    - `tests/test_tpl007.py`, `tests/test_network.py` (lines 103–124 and 165–189);
    - `docs/validation.md`, sections D6 and D7.
  - `SWMFsoftware/SWMF@4e927561205457169a907668d93eeffa014f2414`: `PARAM.XML` lines 807–838, the `README.md` "Obtain SWMF" section, and the tree listing of `GM/`.
  - `spacepy/spacepy@015c1adcf20f642fb31f8a35cb94463cac520fe7`: `spacepy/pybats/bats.py` lines 2725–2770.
  - `SWxTREC/pymsis@d8170cbde127aa802fc48b9deaf328f25ce32eb5`: `pymsis/msis.py` lines 271–286 (version dispatch: `"0"` → MSIS-00, `"2.0"`, `"2.1"`).
- **Execution.** Scripts and raw outputs are in `support/`:
  - `probe_geo_bezpy.py` → `probe_geo_bezpy.out` (§§1, 2.3, 2.5, 7);
  - `probe_msis_starlink.py gfz_kp_ap_f107_excerpt.txt` → `probe_msis_starlink.out` (§5). The excerpt reproduces the full-file output exactly.
- **Literature** (DOIs verified against Crossref metadata on the observation date):
  - **Read in full text:**
    - Pulkkinen et al. 2013, 10.1002/swe.20056 (NASA technical-report server copy);
    - Welling et al. 2018, 10.1029/2018SW002064 (publicly hosted copy of the published article);
    - Fang et al. 2022, 10.1029/2022SW003193 (NOAA repository copy).
  - **Read via Crossref abstracts:**
    - Boteler 2019, 10.1029/2019SW002278;
    - Lucas, Love & Kelbert 2018, 10.1002/2017SW001779;
    - Lucas et al. 2020, 10.1029/2019SW002329;
    - Bedrosian & Love 2015, 10.1002/2015GL066636;
    - Kelbert et al. 2017, 10.1002/2017SW001594;
    - Pulkkinen et al. 2012, 10.1029/2011SW000750;
    - Pulkkinen et al. 2011, 10.1029/2010SW000600;
    - Glocer et al. 2016, 10.1002/2016SW001387;
    - Liemohn et al. 2018, 10.1029/2018SW002067;
    - Boteler & Pirjola 2017, 10.1002/2016SW001499;
    - Pulkkinen et al. 2017, 10.1002/2016SW001501;
    - Tóth et al. 2005, 10.1029/2005JA011126;
    - Gombosi et al. 2021, 10.1051/swsc/2021020;
    - Dang et al. 2022, 10.1029/2022SW003152;
    - Kataoka et al. 2022, 10.1051/swsc/2022034;
    - Baruah et al. 2024, 10.1029/2023SW003716.
  - **Cited via bezpy only:** Horton et al. 2012, 10.1109/TPWRD.2012.2206407 (EPRI-21 topology); Kelbert & Lucas 2020, 10.1029/2020SW002467.
  - **Model references:** Emmert et al. 2021, 10.1029/2020EA001321 (NRLMSIS 2.0); Picone et al. 2002, 10.1029/2002JA009430 (NRLMSISE-00).
  - **Bibliographic only (not examined):** Bolduc 2002, 10.1016/S1364-6826(02)00128-1.
- **Data and secondary sources:**
  - GFZ Kp, ap and F10.7 file retrieved 2026-11-21. This is a mutable file whose recent values are preliminary; the support excerpt preserves the rows used.
  - Natural Resources Canada "Chronology of effects" page (spaceweather.gc.ca), retrieved 2026-11-21.

## Revalidation

1. **TPL-007 constants.** Diff `bezpy/tpl007.py` lines 66–135 at a new revision. Check the current NERC standard number on nerc.com. If it is not TPL-007-4, re-read Attachment 1 for changes to 8 and 12 V/km, equation 3, Table 4, and the 75 and 85 A thresholds.
2. **β waveform sensitivity and EPRI-21 agreement.** Run `python3 support/probe_geo_bezpy.py` from outside the bezpy tree, with bezpy installed from the revision under test. It takes about 4 minutes, dominated by the cost section. Compare the Spearman, median-error and max/min columns with `support/probe_geo_bezpy.out`, and check that the EPRI-21 relative errors stay below 2×10⁻³. If the NERC waveform file is available, pass it to `beta_factor` instead: Table 3 should then reproduce, and `reference_peak_E` should equal 8.0.
3. **Line-integral rule.** Check `TransmissionLine.calc_voltages` for the `[:-1]` indexing and the `np.sum(E3d * self.dl...)` expression. A change to a midpoint or trapezoid rule alters short-line voltages without resampling.
4. **Validation suite.** Re-read the current CCMC or SWPC dB/dt validation description for stations, events, window length and thresholds. Compare them with Pulkkinen 2013 §3 and the Welling 2018 recommendations.
5. **Empirical density response.** Run `python3 support/probe_msis_starlink.py support/gfz_kp_ap_f107_excerpt.txt` with a new `pymsis`. Ratios are expected to stay near 1.11–1.15 at 210 km. A change in MSIS parameter files would move them.
6. **SWMF pin.** List `GM/` at the new revision. If physics code is present, the "does not pin BATS-R-US" boundary no longer holds.
