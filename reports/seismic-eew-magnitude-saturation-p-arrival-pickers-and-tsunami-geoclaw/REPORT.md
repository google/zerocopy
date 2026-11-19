# Seismic EEW Magnitude Saturation, STA/LTA P-Arrival Pickers, and GeoClaw Tsunami Positivity

## Summary

Regional Earthquake Early Warning (`EEW`) and real-time coastal tsunami inundation pipelines couple `100–200 Hz` strong-motion/borehole P-wave arrival pickers (`ObsPy`, `SeisComP`) to rapid rupture-sizing estimators (Japan Meteorological Agency `JMA` point-source scaling vs. `FinDer` finite-fault template correlation) and Adaptive Mesh Refinement (`AMR`) nonlinear shallow-water PDE solvers (`GeoClaw`) to trip high-speed rail emergency brakes, park EUV photolithography stages, isolate gas pipelines, and issue coastal evacuation alerts within seconds (`Basis: documentation, source`).

Across primary-source inspections of `obspy/obspy` (`9079f60ba41869db6b497561047cf3b4530e13c1` `obspy/signal/trigger.py`), `SeisComP/seiscomp` (`0f456a83db3435ef92b809bc47077c84b3a4883b` `src/system/libs/3rd-party/libmseed/mseedformat.h` and `genutils.c`), `clawpack/geoclaw` (`091b28d19ecb1fb0e3b4f1881ccf4ce17d3886a8` `src/2d/shallow/update.f90`, `b4step2.f90`, and `stepgrid.f`), Hoshiba et al.'s post-mortem of the 11 March 2011 $M_w 9.0$ Tohoku-oki earthquake (`DOI: 10.5047/eps.2011.05.031`), Böse, Heaton & Hauksson's Finite-Fault Rupture Detector (`FinDer`, `DOI: 10.1111/j.1365-246X.2012.05629.x`), and Berger, George, LeVeque & Mandli's `GeoClaw` AMR formulation (`DOI: 10.1016/j.advwatres.2011.02.016`), three structural failure modes govern end-to-end cyber-physical soundness:

1. **Single-Sample `STA/LTA` Glitch Ceiling (`N_L / N_S`) & `libmseed` UTC Leap-Second Timestamp Folding (`Basis: source, execution, derived`)**: Recursive Short-Term Average / Long-Term Average (`STA/LTA`) pickers (`obspy/signal/trigger.py:86–103`) weight squared sample energy $a_i^2$ by $1 / N_S$ in the numerator and $1 / N_L$ in the denominator. Consequently, **a single `10 ms` ADC bit-flip, mass-recentering calibration pulse, or demeaned packet-gap step drives `STA/LTA` instantaneously to its asymptotic ceiling $N_L / N_S = 20.00$** (`5x` above a `4.0` trigger threshold for standard `nsta = 50`, `nlta = 1000`). Simultaneously, direct inspection of `SeisComP`'s bundled `libmseed` (`src/system/libs/3rd-party/libmseed/genutils.c:193, 1293–1370`) proves that while `#define VALIDSEC(sec) (sec >= 0 && sec <= 60)` (`line 193`) accepts positive UTC leap seconds (`sec == 60`), `ms_time2nstime_int` (`line 1311`) computes a POSIX `86,400 s/day` linear combination **without adding `embedded_leapsecondlist[].TAIdelta` (`lines 79–161`)**, mapping `2016-12-31T23:59:60.000` and `2017-01-01T00:00:00.000` to the **exact same `nstime_t` integer (`1,483,228,800,000,000,000`)**—a non-injective `1.000 s` clock fold that mislocates hypocenters by `6–8 km` unless station picks are gated by **$k$-of-$N$ Minkowski causal-cone coincidence** over monotonic `TAI` nanoseconds.
2. **2011 $M_w 9.0$ Tohoku Dual False-Negative Saturation vs. `FinDer` Finite-Fault Line Templates (`Basis: normative, documentation, execution, derived`)**: During the `~450 km`-long, `150 s` 2011 Tohoku megathrust rupture, JMA's point-source short-period (`T <= 5–6 s`) displacement scaling saturated at $M_{\text{JMA}} \approx 8.0\text{–}8.1$ (`7.9` initial displacement-filter plateau)—**underestimating true $M_w 9.0$ seismic moment $M_0 = 10^{1.5(M_w + 6.07)}$ by `31.6x`** while computing Ground Motion Prediction Equation (`GMPE`) attenuation from the distant northern/central **point hypocenter ($R_{\text{hypo}} = 228.0\text{ km}$)** rather than the **nearest active fault segment ($R_{\text{rup}} = 60.0\text{ km}$, `3.8x` closer to southern Ibaraki/Chiba)**. Both errors compound in the **unsound false-negative direction** (under-predicting Kanto shaking and initial tsunami uplift). `FinDer` (`Böse et al. 2012`) eliminates both defects by matching spatial Peak Ground Acceleration (`PGA`) binary footprints against Wells & Coppersmith (`1994`) line-source templates ($M_{\text{len}}(450\text{ km}) = 8.63$, $R_{\text{rup}} = 60.0\text{ km}$) under $M_{\text{est}}(t) = \max(M_{\text{pt}}(t), M_{\text{len}}(t))$.
3. **Coastal Shoreline Wetting-Drying Positivity ($h \ge 0$), Lake-at-Rest Balance, and Cliff Desingularization (`Basis: source, execution, derived`)**: Across steep coastal shorelines (`3` dry `+12 m` cliff cells $h_f = 0, B_f = +12\text{ m}$ adjacent to `1` calm ocean cell $h_f = 20\text{ m}, B_f = -20\text{ m}, \eta_f = 0\text{ m}$ with coarse average bathymetry $B_c = +4.0\text{ m}$), naive AMR fine-to-coarse depth averaging invents a **phantom `+9.0 m` tsunami wall (`naive_eta = +9.0 m`)** on a motionless sea, whereas unclamped wet-surface subtraction ($\bar{\eta}_{\text{wet}} - B_c$) produces **negative fluid depth (`h_c = -4.0 m < 0`)**, turning shallow-water wave speed $\sqrt{g h_c}$ into `NaN`. Direct inspection of `clawpack/geoclaw` (`src/2d/shallow/update.f90:141–160` and `b4step2.f90:45–85`) shows `GeoClaw` averaging $\eta_f$ *exclusively over wet cells* (`hf > dry_tolerance`), zeroing dry momenta (`huf = hvf = 0`), clamping coarse depth via `hc = min(hav, max(etaav - bc*capac, 0.0d0))` (`update.f90:160`), and bounding cliff-runoff velocities via `fixdry` + `speed_limit` (`b4step2.f90:51–67`), preserving exact **$h_c == 0.0 \ge 0$ positivity and zero phantom inundation**.

## Applicability

This report characterizes an end-to-end cyber-physical sensing, estimation, and PDE forecasting pipeline across the six subjects in `REPORT.json` (`Basis: derived`):

- **Subject Relationships**:
  - **Stage 1 — Waveform Ingestion & Arrival Picking**: `SeisComP/seiscomp` (`0f456a83db3435ef92b809bc47077c84b3a4883b`, specifically its bundled EarthScope `libmseed` v3/v2 packet time parser in `src/system/libs/3rd-party/libmseed/`) and `obspy/obspy` (`9079f60ba41869db6b497561047cf3b4530e13c1`, `obspy/signal/trigger.py`) represent real-time `seedlink`/`miniSEED` timestamp decoding and `STA/LTA` P-wave detection.
  - **Stage 2 — Real-Time Source Sizing & Ground-Motion Prediction**: **Hoshiba et al. (`2011`)** provides the empirical field post-mortem of point-source EEW saturation during the $M_w 9.0$ Tohoku megathrust rupture, which **Böse, Heaton & Hauksson (`2012`)** (`FinDer`) resolves via spatial 2D template matching over extended line ruptures.
  - **Stage 3 — Coastal Tsunami Inundation Forecasting**: `clawpack/geoclaw` (`091b28d19ecb1fb0e3b4f1881ccf4ce17d3886a8`, `src/2d/shallow/`) implements the adaptive-mesh 2D shallow-water numerical method analyzed mathematically in **Berger, George, LeVeque & Mandli (`2011`)**, consuming finite-fault seafloor uplift (`dtopo`, `b4step2.f90:18–20, 87–92`) to forecast nearshore runup.
- **Exact Observation vs. Broader Applicability**:
  - Source findings apply directly to `ObsPy` `recursive_sta_lta_py` / `carl_sta_trig` (`IEEE 754` `float64`), `SeisComP`'s `libmseed` `ms_time2nstime` (`miniSEED` v2.4 `48 B` and v3.0 `40 B` headers), and `GeoClaw`'s 2D explicit finite-volume Fortran 90 solver (`dry_tolerance = 10^-3 m`, spherical capacity `mcapa` or Cartesian `mcapa == 0`).
  - The $N_L / N_S$ impulse ceiling holds for *every* first-order exponential `STA/LTA` recurrence (C, C++, FPGA, or Python); the `sec == 60` timestamp fold applies to *any* telemetry decoder mapping UTC leap seconds onto `86,400 s/day` POSIX epochs; and the dual $(M, R)$ non-conservativeness of point sources applies to any spatially extended hazard (`> 50 km` subduction/strike-slip faults, line-fire fronts, pipeline ruptures).

## Findings

### 1. Recursive `STA/LTA` Glitch Ceiling (`ObsPy`), `libmseed` Leap-Second Folding (`SeisComP`), and `TAI` Causal Cones

#### 1.1 Closed-Form Single-Sample Glitch Ceiling ($N_L / N_S$) in `obspy/signal/trigger.py`
`Basis: source, execution, derived`

In `obspy/obspy` (`9079f60ba41869db6b497561047cf3b4530e13c1`, `obspy/signal/trigger.py:86–103`), `recursive_sta_lta_py` computes the Evans–Allen characteristic function over demeaned/filtered acceleration or velocity samples $a[i]$:

```python
# obspy/signal/trigger.py:89-101
csta = 1. / nsta
clta = 1. / nlta
sta = 0.
lta = np.finfo(0.0).tiny  # avoid zero division (2.225e-308)
a = np.square(a)
charfct = np.zeros(ndat, dtype=np.float64)
icsta = 1 - csta
iclta = 1 - clta
for i in range(1, ndat):
    sta = csta * a[i] + icsta * sta
    lta = clta * a[i] + iclta * lta
    charfct[i] = sta / lta
charfct[:nlta] = 0
```

Suppose stationary background microseismic noise has variance $\sigma^2 > 0$, so prior to index $k$, $S_{k-1} \approx L_{k-1} \approx \sigma^2$ ($R_{k-1} \approx 1$). If sample $k$ suffers a **single `1`-sample non-seismic transient** $a_k^2 = M \sigma^2$ ($M \gg N_L$)—caused by a `24`-bit digitizer SPI bit-flip, borehole mass-recentering pulse, lightning ground-loop spike, or a `0`-filled missing packet step after high-pass filtering—the instantaneous ratio at sample $k$ is:
$$R_k = \frac{\frac{1}{N_S} M \sigma^2 + \bigl(1 - \frac{1}{N_S}\bigr)\sigma^2}{\frac{1}{N_L} M \sigma^2 + \bigl(1 - \frac{1}{N_L}\bigr)\sigma^2} = \frac{\frac{M - 1}{N_S} + 1}{\frac{M - 1}{N_L} + 1} \xrightarrow{M \to \infty} \frac{N_L}{N_S}$$
For standard `100 Hz` EEW picker windows `nsta = 50` (`0.5 s`) and `nlta = 1000` (`10.0 s`), **a single `10 ms` sample glitch drives `charfct[k]` to `20.00`**, exceeding a standard `3.5–4.0` P-pick threshold by **`5x` in `1` sample** (`verified in probes/verify_eew_saturation_geoclaw.py`)! While `carl_sta_trig` (`trigger.py:106–158`) and Baer–Kradolfer (`pk_baer`) introduce `ratio`/`quiet` envelope-duration hysteresis (`>= 0.1–0.3 s`), multi-sample calibration pulses or local cultural impacts (truck pass, construction pile-driver) still trip any single-station picker.

#### 1.2 Primary-Source `sec == 60` Leap-Second Timestamp Collision in `SeisComP` `libmseed`
`Basis: source, execution`

In `SeisComP/seiscomp` (`0f456a83db3435ef92b809bc47077c84b3a4883b`), `src/system/libs/3rd-party/libmseed/mseedformat.h:35–95` defines both `miniSEED 3.0` (`40`-byte `MS3FSDH`: `nsec`, `year`, `day`, `hour`, `min`, `sec` at offsets `4..14`) and `miniSEED 2.4` (`48`-byte `MS2FSDH` `BTime`), whose segmented UTC fields explicitly represent positive IERS leap seconds via `sec = 60`. Inspecting `src/system/libs/3rd-party/libmseed/genutils.c:78–164, 193, 1293–1370` uncovers a subtle timestamp-injectivity hazard:

```c
// SeisComP src/system/libs/3rd-party/libmseed/genutils.c:193 & 1293-1314
#define VALIDSEC(sec) (sec >= 0 && sec <= 60)
...
static nstime_t
ms_time2nstime_int (int year, int yday, int hour, int min, int sec, uint32_t nsec)
{
  ...
  days = (365 * (shortyear - 70) + intervening_leap_days + (yday - 1));
  nstime = (nstime_t)(60 * (60 * ((nstime_t)24 * days + hour) + min) + sec) * NSTMODULUS + nsec;
  return nstime;
}
```

1. **Exact `1.000 s` Non-Injective Epoch Fold**: Although `genutils.c:79–161` embeds a `LeapSecond embedded_leapsecondlist[]` table (`TAIdelta = 10 .. 37`, commented `good through: 28 December 2023`), **`ms_time2nstime` (`lines 1331–1370`) validates `VALIDSEC(sec)` (`allowing sec == 60`) and calls `ms_time2nstime_int` directly without consulting `leapsecondlist`!** Evaluating `ms_time2nstime_int` across the 31 December 2016 leap second (`probes/verify_eew_saturation_geoclaw.py`):
   - `ms_time2nstime_int(2016, 366, 23, 59, 60, 0) == 1_483_228_800_000_000_000`
   - `ms_time2nstime_int(2017,   1,  0,  0,  0, 0) == 1_483_228_800_000_000_000`
   Two physically distinct `100 Hz` packets separated by `1.000 s` receive **identical `nstime_t` timestamps** (apparent `100`-sample duplicate overlap / backwards time jump in downstream ring buffers)!
2. **Mixed NTP-Smear vs. GPS-Locked Station Skew & Causal-Cone Rejection**: If borehole station A locks directly to GPS/UTC (`sec = 60` folded by `-1.0 s` or stepped) while surface station B (`2.0 km` away) runs OS NTP leap-smearing or stale oscillator holdover, their P-arrival picks skew by $|\Delta t_{AB}| = 1.00\text{ s}$. At crustal P-velocity $v_P \approx 6.0\text{ km/s}$, a `1.00 s` arrival error shifts hyperboloidal hypocenter triangulation by **`6–8 km`**!
   - Enforcing the **Minkowski Elastic Causal-Cone Invariant** over monotonic `TAI` nanoseconds ($\text{TAI} = \text{UTC} + \Delta\text{AT}$, strictly monotonic with zero leap seconds) requires every pair $(i, j)$ in a triggering $k$-station quorum ($k \ge 3$) to satisfy:
     $$|t_i^{\text{TAI}} - t_j^{\text{TAI}}| \le \frac{\|\mathbf{x}_i - \mathbf{x}_j\|_2}{v_{P,\min}} + 2\epsilon_{\text{clk}}$$
   - For $\|\mathbf{x}_A - \mathbf{x}_B\|_2 = 2.0\text{ km}$, $v_{P,\min} = 4.5\text{ km/s}$, and GPS timing margin $\epsilon_{\text{clk}} = 0.05\text{ s}$, the physical upper bound is **`0.544 s < 1.000 s`**—automatically quarantining clock-skewed stations and rejecting single-station `STA/LTA = 20.0` spikes (`f < k` fault tolerance).

---

### 2. 2011 $M_w 9.0$ Tohoku Point-Source Saturation (`Hoshiba 2011`) vs. `FinDer` (`Böse 2012`)

`Basis: normative, documentation, execution, derived`

Hoshiba et al. (*Earth, Planets and Space* `63:547–551`, `2011`, `DOI: 10.5047/eps.2011.05.031`) analyzed JMA's operational EEW performance during the 11 March 2011 $M_w 9.0$ Tohoku-oki megathrust rupture (`rupture length L ~ 450 km`, `width W ~ 200 km`, `duration ~ 150 s`, peak slip `> 30–50 m`). While JMA issued its first public warning for Miyagi **just `8.6 s` after detecting the initial P-wave** at coastal station `OSH` (`~15 s` before destructive S-waves reached Sendai), two structural assumptions caused severe **under-prediction of Kanto/Tokyo ground motion and initial tsunami height**:

1. **Spectral Corner-Frequency Magnitude Saturation (`31.6x` Moment Deficit)**:
   - Operational point-source EEW estimates $M_{\text{JMA}}$ from peak vector displacement amplitude $P_d$ after applying a recursive high-pass/band-pass filter (`passband T <= 5–6 s`, i.e., $f \ge 0.17\text{–}0.20\text{ Hz}$) to prevent double-integration baseline drift on strong-motion accelerometers.
   - By Brune'somega-square source scaling, seismic moment $M_0 = 10^{1.5(M_w + 6.07)}\text{ N\cdot m}$ sets the source spectral corner frequency $f_c = 0.49\,\beta\,(\Delta\sigma / M_0)^{1/3}$:
     - At $M_w 6.0$ ($M_0 \approx 1.1 \times 10^{18}\text{ N\cdot m}$), $f_c \approx 0.25\text{ Hz}$ (`T ~ 4 s`), fitting cleanly inside the `5–6 s` filter window.
     - At $M_w 9.0$ ($M_0 \approx 4.0 \times 10^{22}\text{ N\cdot m}$), **$f_c$ drops to `~0.008–0.010 Hz` (`100–125 s` rupture duration)**! Measuring `<= 6 s` band-passed displacement clips `M_JMA` at **`~7.9–8.1`**, missing **`10^{1.5(9.0 - 8.0)} = 31.62x`** (`96.8%`) of the true seismic moment and seafloor volumetric tsunami uplift!
2. **Epicentral vs. Finite-Fault Rupture Distance ($R_{\text{hypo}} = 228.0\text{ km}$ vs. $R_{\text{rup}} = 60.0\text{ km}$)**:
   - Ground Motion Prediction Equations (`GMPE`s) attenuate shaking with source-to-site distance $R$:
     $$\log_{10}\operatorname{PGA}(\mathbf{x}) = a\,M - b\log_{10}(R + c) - d\,R$$
   - Tohoku nucleated offshore Miyagi ($\mathbf{x}_0 = (0, 0)$) and tore `> 250 km` southward off Ibaraki and Chiba. For a coastal site `220 km` along strike and `60 km` onshore ($\mathbf{x} = (220, 60)\text{ km}$), point-source EEW plugged in **hypocentral distance $R_{\text{hypo}} = \sqrt{220^2 + 60^2} = 228.0\text{ km}$**, whereas the tearing fault plane passed just **$R_{\text{rup}} = \min_{y \in [0, 450]} \sqrt{(220 - y)^2 + 60^2} = 60.0\text{ km}$** away (**`3.8x` closer**)!
   - **Dual Non-Conservativeness Theorem**: Treating an extended fault $\Gamma(t) \subset \mathbb{R}^3$ as its nucleation point $\{\mathbf{x}_0\}$ simultaneously **under-approximates $M$** ($M_{\text{pt}} \le M_w$) AND **over-approximates $R$** ($R_{\text{hypo}} \ge R_{\text{rup}}$). Because $\partial\operatorname{PGA}/\partial M > 0$ and $\partial\operatorname{PGA}/\partial R < 0$, **both approximations err strictly in the dangerous false-negative direction**!
3. **`FinDer` 2D Spatial Template Matching (`Böse, Heaton & Hauksson 2012`, `DOI: 10.1111/j.1365-246X.2012.05629.x`) & Post-Tohoku Hybridization**:
   - `FinDer` bypasses temporal filter saturation by classifying the spatial 2D grid of real-time station `PGA` values into binary near-source/far-source masks (`PGA > threshold`) at `1 Hz` and running 2D image template correlation against rotated line-source templates parameterized by Wells & Coppersmith (`1994`) subsurface rupture length scaling ($\log_{10} L_{\text{km}} = -2.44 + 0.59\,M_w \iff M_{\text{len}}(L) = \frac{\log_{10} L + 2.44}{0.59}$).
   - At $L = 450\text{ km}$, `FinDer` recovers **$M_{\text{len}} = 8.63$** (`vs. 8.0 point-source`) and exact **$R_{\text{rup}} = 60.0\text{ km}$** (`vs. 228.0 km`). Combined with real-time `1 Hz` GNSS static coseismic displacement (`REGARD`, non-saturating at `0 Hz`) and direct wavefield propagation (`PLUM`, immune to Hoshiba `2011`'s multi-aftershock association confusion), taking the join $M_{\text{est}}(t) = \max\bigl(M_{\text{pt}}(t), M_{\text{len}}(t), M_{\text{GNSS}}(t)\bigr)$ restores monotone safety on $M_w 8.5\text{–}9.5$ megathrusts.

---

### 3. `GeoClaw` Adaptive-Mesh Tsunami Positivity, Lake-at-Rest Balance, and Cliff Desingularization

`Basis: source, execution, derived`

`clawpack/geoclaw` (`091b28d19ecb1fb0e3b4f1881ccf4ce17d3886a8`, Berger, George, LeVeque & Mandli `2011`, `DOI: 10.1016/j.advwatres.2011.02.016`) integrates the 2D depth-averaged nonlinear shallow-water equations (`SWE`) for conserved state $\mathbf{q} = [h, hu, hv]^T$ over time-varying seafloor/coastal topography $B(x, y, t)$ (`aux(1,i,j)`):
$$\partial_t h + \partial_x(hu) + \partial_y(hv) = 0, \qquad \partial_t(hu) + \partial_x\!\left(hu^2 + \tfrac{1}{2}g h^2\right) + \partial_y(huv) = -g h\,\partial_x B - \frac{g n^2 u\sqrt{u^2+v^2}}{h^{1/3}}$$
Inspecting `src/2d/shallow/update.f90:15–21, 141–160`, `src/2d/shallow/b4step2.f90:45–85`, and `src/2d/shallow/stepgrid.f:180–225` exposes three load-bearing numerical invariants required to prevent `NaN` crashes and phantom tsunami bores across `5–6` nested AMR levels:

#### 3.1 Why Naive Shoreline AMR Restriction Invents `+9.0 m` Tsunamis or `-4.0 m` `NaN` Depths (`update.f90:141–160`)
When a fine AMR grid (`level l+1`) restricts its solution onto an underlying coarse cell (`level l`) straddling a steep coastline, `update.f90:141–160` executes:

```fortran
! clawpack/geoclaw src/2d/shallow/update.f90:141-160
if (alloc(iaddf(1,iff+ico-1,jff+jco-1,locf,mi)) > dry_tolerance) then
    etaf = hf + bf
    nwet = nwet + 1
else
    etaf = 0.d0
    huf=0.d0
    hvf=0.d0
endif
hsum   = hsum + hf
husum  = husum + huf
hvsum  = hvsum + hvf
etasum = etasum + etaf
...
if (nwet > 0) then
    etaav = etasum/dble(nwet)
    hav = hsum/dble(nwet)
    hc = min(hav, (max(etaav-bc*capac, 0.0d0)))
    alloc(iadd(2,i,j)) = (min(hav, hc) / hsum) * husum
    alloc(iadd(3,i,j)) = (min(hav, hc) / hsum) * hvsum
```

Evaluate all three candidate restriction rules on a `2x2` fine patch containing **`3` dry `+12 m` coastal cliff cells** ($h_f = 0, B_f = +12\text{ m}$) and **`1` calm ocean cell at sea level $\eta_f = 0\text{ m}$** ($h_f = 20\text{ m}, B_f = -20\text{ m}$), overlying coarse cell average bathymetry $B_c = \frac{1}{4}(12 + 12 + 12 - 20) = +4.0\text{ m}$ (`verified in probes/verify_eew_saturation_geoclaw.py`):

| Candidate AMR Fine-to-Coarse Formula | Computed Coarse Depth $h_c$ | Implied Sea Surface $\eta_c = h_c + B_c$ | Catastrophic Failure / Soundness Property |
| :--- | :--- | :--- | :--- |
| **1. Standard Conservative Depth Average** ($h_c = \frac{1}{4}\sum h_f$) | $20 / 4 = \mathbf{5.0\text{ m}}$ | $5.0 + 4.0 = \mathbf{+9.0\text{ m}}$ | **Violates Lake-at-Rest**: dumps `5 m` of water atop a `+4 m` cliff, launching a **spurious `+9.0 m` tsunami wave** from a flat `0.0 m` sea! |
| **2. Unclamped Wet-Surface Subtraction** ($h_c = \bar{\eta}_{\text{wet}} - B_c$) | $0.0 - 4.0 = \mathbf{-4.0\text{ m}}$ | $0.0\text{ m}$ | **Violates Depth Positivity ($h < 0$)**: eigenspeed $\lambda_{\pm} = u \pm \sqrt{g h_c} = \sqrt{-39.24} = \mathbf{\text{NaN}}$, poisoning the entire grid in `1` step! |
| **3. `GeoClaw` Min-Max Wet Envelope** (`update.f90:160`: $\min(\bar{h}_{\text{wet}}, \max(\bar{\eta}_{\text{wet}} - B_c, 0))$) | $\min(20, \max(-4, 0)) = \mathbf{0.0\text{ m}}$ | Dry cell ($h_c = 0$, $hu_c = hv_c = 0$) | **Sound**: preserves exact **$h_c \ge 0$**, **zero phantom wave** ($\mathbf{u}_c = \mathbf{0}$), and scales coarse momentum by `min(hav, hc)/hsum = 0`! |

#### 3.2 Pre-Step Dry Desingularization & Cliff Runoff Speed Limiting (`b4step2.f90:45–85` & `stepgrid.f:180–225`)
Before every hyperbolic flux update `call step2(...)` (`stepgrid.f:180–215`, tracking OpenMP thread-safe Courant number `cflmax = dmax1(cflmax, cflgrid)` at `lines 192–197` where positivity requires $\text{CFL} = \frac{\Delta t}{\Delta x}\max(|u| + \sqrt{gh}) \le 1$), `b4step2.f90` enforces three explicit guards:
1. **`NaN` Sentinel Trap (`b4step2.f90:46`)**: `call check4nans(meqn,mbc,mx,my,q,t,1)` halts immediately rather than propagating silent `IEEE 754` `NaN`s into inundation maps.
2. **Dry-Cell Momentum Zeroing (`b4step2.f90:51`)**: `call fixdry(...)` clamps rounding-induced $h < 0 \mapsto 0$ and zeroes $hu = hv = 0$ whenever $h \le \epsilon_{\text{dry}}$ (`dry_tolerance`), preventing microscopic thin films ($h = 10^{-14}\text{ m}$) from dividing $u = hu / h$ into $10^{+8}\text{ m/s}$ supersonic velocities and collapsing adaptive $\Delta t \to 0$.
3. **Steep-Cliff Velocity Capping (`b4step2.f90:59–67`)**: When water drains off steep topography ($\Delta B \gg h$), `SWE`'s hydrostatic assumption breaks down; `b4step2.f90` computes `s = sqrt(q(2)**2 + q(3)**2) / q(1)` (`line 62`) and rescales `(hu, hv)` direction-preservingly by `speed_limit / s` (`lines 64–66`, default `speed_limit = 50 m/s`), preventing CFL time-step starvation (`dt -> 0`) during tsunami drawdown.

---

### 4. Multi-Level Performance and Resource Footprint Matrix (`L1`–`L6`)

`Basis: source, documentation, execution, derived`

| Level | Axis | `ObsPy` + `SeisComP` (`libmseed`) + `FinDer` (Seismic EEW) | `clawpack/geoclaw` (2D AMR Shallow-Water Tsunami) | Engineering & Verification Trade-Off |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | `ObsPy` `trigger.py` `898 LoC` Python; `libmseed` `genutils.c` `2,079 LoC` C; `FinDer` core `~2,500 LoC` C++ (`~3–5x` proof ratio for `TAI` causal cones & monotone rupture bounds) | `GeoClaw` `src/2d/shallow/` Fortran 90/77 AMR + augmented Riemann solver `~12,000 LoC` (`subtle` index/ghost-cell arithmetic; `~5–8x` deductive proof ratio, `~40K` LLM tokens per kernel) | Factoring `WetCell | DryCell` and `CausalQuorum` into reusable verified primitives avoids re-proving `dry_tolerance` & leap-second invariants across `10 KLoC` solver loops |
| **L2** | **Framework & Toolchain Build Time** | `ObsPy` Python/C wheel `< 15 s`; full `SeisComP` C++/Boost/Qt/SQL tree (`README.md:77–138`) **`15–35 min` (`~4 GB` RSS)** | `GeoClaw` `gfortran -O3 -fopenmp` build **`15–40 s` (`< 400 MB` compiler RSS)** (`zero` C++ template expansion bloat) | Keep hard-real-time rail/stepper trip interlocks in zero-dependency C/Rust/Fortran binaries (`< 5 s` build) decoupled from `SeisComP` GUI/ORM packages |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | Linear real/integer SMT check (`QF_LIRA`) of `TAI` causal-cone triangle inequalities & `STA/LTA <= N_L/N_S` ceiling **`< 15 ms`** | Nonlinear real/interval proof (`NRA` / Lean `positivity` + lattice tactics) of `min(hav, max(etaav - bc, 0)) >= 0` & Lake-at-Rest **`< 35 ms`** (`< 20 ms` warm LSP) | Min/max lattice rewrite rules discharge AMR restriction positivity in `< 35 ms` without brittle nonlinear quantifier instantiation |
| **L4** | **Generated Code Execution Performance** | Compiled C/Rust `recursive_sta_lta` **`< 0.4 us`/sample** (`3,000` `100 Hz` channels `< 0.12 s/s` on `1` core); regional `FinDer` `1,000`-station 2D template correlation **`~15–45 ms` per `1 Hz` tick** | OpenMP + AVX-512 `GeoClaw` augmented Riemann solver **`~20–45 M` cell-updates/s/node** (`5`-level `10 m` harbor runup in `~30–120 s`, or **`< 0.5 s`** via pre-computed unit-source Green's-function superposition + local AMR refinement) | `18 ms` `FinDer` + `1 Hz` GNSS `REGARD` slip feeds pre-computed offshore Green's functions to initialize nearshore `GeoClaw` patches within `< 3 s` |
| **L5** | **Proof / Certificate Verification Speed** | `k-of-N` (`k <= 8`) signed station `TAI` causal-cone quorum check runs in **`< 5 us`** (`28` pairwise distance-time checks, `0` alloc) | Per-step AMR grid positivity ($h_{\min} \ge 0$), `NaN`-freedom (`check4nans`), and total wet-volume conservation audit **`< 0.2 ms`/patch** | High-speed rail / EUV fab receivers independently verify a `256`-byte `k`-station cryptographic causal-pick certificate in `< 5 us` before tripping brakes |
| **L6** | **RAM, Disk & Binary Footprints** | `1,000` `3`-axis `100 Hz` `Steim-2` `miniSEED` streams = **`~1.2 MB/s` network / `100 GB/day` disk**; `FinDer` template bank **`< 20 MB` RAM** | `GeoClaw` `5`-level AMR (`0.5M–4M` active cells at `32 B/cell` `[h, hu, hv, B]` + `ETOPO1`/LIDAR DEMs) = **`0.5–3.5 GB` RAM** | Berger–Oliger `AMR` shrinks memory & FLOPs by **`50–200x`** over uniform `10 m` ocean-wide meshes (`> 250 GB` uniform -> `~1.5 GB` AMR) |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived, source`

#### 5.1 `(C1)` Human Comprehensibility vs. Agent Execution Ergonomics
- **The `"Smooth Moving Average"` Illusion in `STA/LTA`**: Human engineers reading the `3`-line loop `sta = csta*a[i] + icsta*sta; lta = clta*a[i] + iclta*lta; charfct[i] = sta / lta` (`trigger.py:98–100`) form a mental model of a low-pass ratio filter (`2` working-memory chunks) and almost universally fail to see that a **single `1`-sample outlier** immediately hits $N_L / N_S = 20.0$. Likewise, human reviewers reading `genutils.c:79` (`static LeapSecond embedded_leapsecondlist[]`) naturally assume `ms_time2nstime` uses that table—missing `1,150` lines down (`line 1311`) that `ms_time2nstime_int` silently folds `sec == 60` onto the next day's `00:00:00`!
- **Logarithmic Magnitude Compression (`M 8.0` vs. `M 9.0` Mental Trap)**: In emergency operations centers, `M 8.0` vs. `M 9.0` reads visually like a `12.5%` discrepancy rather than a **`31.6x` factor in fault slip volume** and a **`3.8x` distance error (`228 km` vs. `60 km`)**. Human-auditable EEW displays and APIs must surface **explicit physical units**—rupture segment geometry $\Gamma(t)$ (`km`), nearest fault distance $R_{\text{rup}}$ (`km`), and seismic moment $M_0$ (`N*m`)—rather than a bare point hypocenter and scalar $M$.
- **Dual Coordinate Mental Tax in Shallow-Water Code (`q(1) = h` vs. `eta = h + B`)**: Maintaining `7+` coupled state conventions across Fortran arrays (`q(1)=h`, `aux(1)=B`, implicit $\eta = h+B$, `dry_tolerance`, spherical `mcapa`, `speed_limit`, and ghost-cell `mbc`) stretches human working memory to its limit: forgetting `if (hf > dry_tolerance)` at *one* grid interface contaminates sea-surface elevation $\eta$ with `+12 m` dry cliff height.

#### 5.2 `(C2)` Conceptual Simplicity, Felleisen Expressibility & Ousterhout Deep-Module Refinement
- **Why Scattered `if (h > dry_tol)` Guards & UTC Tables Fail Felleisen's Test**: Forcing every caller of `libmseed` to manually cross-check `embedded_leapsecondlist` or every AMR stencil in `GeoClaw` to remember `if (h > dry_tolerance)` fails Felleisen's local-expressibility criterion and Ousterhout's deep-module principle: the safety invariant leaks into every consumer loop as repetitive, bug-prone adapter boilerplate.
- **Three Universal Deep-Module Refinements**:
  1. **`MonotonicTaiPick` & `CausalQuorum<k, VpMin>`**: Decode `miniSEED` (`year, yday, hour, min, sec, nsec`) *once* at the ingress boundary into `TaiInstantNs` (injectively mapping `23:59:60` to a distinct nanosecond `10^9 ns` prior to `00:00:00` via IERS `DeltaAT`), and require downstream actuator trips to accept only a `CausalQuorum<k >= 3>` witness verifying pairwise Minkowski cone bounds—turning single-station `STA/LTA` spikes and unsynchronized station clocks into unconstructible types.
  2. **Set-Valued Compact Rupture Source (`CompactFault<R3>`)**: Model *every* earthquake from $t = 0$ onward as a compact set $\Gamma(t) \subset \mathbb{R}^3$ equipped with set distance $R_{\text{rup}}(\mathbf{x}, \Gamma(t)) = \inf_{\mathbf{y} \in \Gamma(t)} \|\mathbf{x} - \mathbf{y}\|_2$ and monotone moment envelope $M_0(t) = \max(M_{0,\text{pt}}, M_{0,\text{len}}(\operatorname{diam}\Gamma(t)), M_{0,\text{GNSS}})$. Point nucleation ($\Gamma(0) = \{\mathbf{x}_0\}$) becomes the trivial `0`-length degenerate case of a single scale-free law, eliminating point-vs-finite mode switches.
  3. **Algebraic Sum Type for Shoreline Cells (`HydroCell = Dry { b: f64 } | Wet { h: PosF64, eta: f64, u: BoundedSpeed, v: BoundedSpeed }`)**: Because sea-surface elevation `eta` and fluid velocity `(u, v)` **do not exist on `Dry` cells**, averaging `eta` over dry cliffs (`naive_eta = +9.0 m`) or dividing `hu / 0.0` becomes a compile-time type error, while lowering to identical packed `32 B` SIMD `[h, hu, hv, B]` arrays at `L4`/`L6`.

## Boundaries

1. **Non-Hydrostatic Dispersive Tsunami Bore Fission & Submarine Landslides (`known not to apply` to pure 2D hydrostatic `SWE`)**: Classic `GeoClaw` (`update.f90`, `stepgrid.f`) solves hydrostatic shallow-water equations valid when horizontal wavelength $\lambda \gg H$. Short-wavelength tsunamis generated by steep submarine landslides or volcanic flank collapses (e.g., 2018 Anak Krakatau / Palu Bay) and nearshore undular bore fission exhibit strong frequency dispersion requiring elliptic Boussinesq (`Serre–Green–Naghdi` / `GeoClaw-Boussinesq`) linear-system solves (`known not to apply` to explicit hydrostatic `SWE`).
2. **Deep-Focus (`300–680 km` Wadati–Benioff Slab) Apparent Horizontal Phase Velocity (`not examined`)**: Our planar causal-cone bound ($|t_i - t_j| \le \|\mathbf{x}_i - \mathbf{x}_j\|_2 / v_{P,\min}$ with $v_{P,\min} = 4.5\text{ km/s}$ suffices to reject `1.0 s` clock steps on `2 km` baselines, while upper-velocity checks $v_{\text{app}} \le 8.5\text{ km/s}$ apply only to shallow crustal/interplate ruptures): a wavefront ascending nearly vertically from a `500 km` deep slab hits adjacent surface stations almost simultaneously ($v_{\text{app,horiz}} \to \infty$), which is still accepted by the upper bound $|t_i - t_j| \le d / v_{P,\min} + 2\epsilon$, whereas full 3D hypocentral association requires spherical `iasp91`/`ak135` travel-time tables (`not examined` in the planar probe).
3. **3D Urban Macro-Roughness, Floating Debris Damming & Scour Forces (`unsupported` in bare-earth `2D SWE`)**: Depth-averaged Manning friction (`n ~ 0.025`) over `10 m` bare-earth LIDAR DEMs cannot resolve impulsive shipping-container/vessel strikes, multi-story building collapse blockages, or bridge-pier foundation scour (`unsupported` without 3D multiphase Navier–Stokes / SPH coupling).
4. **Zero-Warning Epicentral Blind Zone Directly Above Shallow Inland Faults (`unknown` pre-rupture)**: Because S-waves trail P-waves by $t_S - t_P \approx R_{\text{hypo}} \cdot (v_S^{-1} - v_P^{-1}) \approx R_{\text{hypo}} / (8\text{ km/s})$, infrastructure located directly above a `10 km`-deep inland strike-slip hypocenter receives `< 1.25 s` physical P-to-S lead time—leaving positive pre-shaking actuator shutoff inside the `< 15 km` blind zone physically impossible (`unknown` prior to fault nucleation).

## Evidence

| Source / Artifact | Immutable Identity & Narrow Location | Grounded Fact Established |
| :--- | :--- | :--- |
| `obspy/obspy` | Commit `9079f60ba41869db6b497561047cf3b4530e13c1`, `obspy/signal/trigger.py:86–158` | `recursive_sta_lta_py` (`csta = 1./nsta`, `clta = 1./nlta`, `sta / lta` at `lines 89–100`) and `carl_sta_trig` envelope damping (`lines 106–158`) |
| `SeisComP/seiscomp` | Commit `0f456a83db3435ef92b809bc47077c84b3a4883b`, `src/system/libs/3rd-party/libmseed/mseedformat.h:35–95` & `genutils.c:78–164, 193, 1293–1370` | `MS3FSDH`/`MS2FSDH` UTC `sec` field; `VALIDSEC(sec <= 60)` (`193`); `embedded_leapsecondlist` (`79–161`); `ms_time2nstime_int` linear `86,400 s/day` folding of `sec == 60` onto next day's `00:00:00` (`1311, 1369`) |
| `clawpack/geoclaw` | Commit `091b28d19ecb1fb0e3b4f1881ccf4ce17d3886a8`, `src/2d/shallow/update.f90:15–21, 141–160`, `b4step2.f90:45–85`, & `stepgrid.f:180–225` | Wet-only `hf > dry_tolerance` `etaf` averaging & `hc = min(hav, max(etaav - bc*capac, 0.0d0))` (`update.f90:141–160`); `check4nans`, `fixdry`, and cliff `speed_limit` rescaling (`b4step2.f90:46–67`); OpenMP `cflmax` & flux update (`stepgrid.f:180–215`) |
| Hoshiba et al. (`2011`) | *Earth, Planets and Space* `63:547–551`, `DOI: 10.5047/eps.2011.05.031` | 11 March 2011 $M_w 9.0$ Tohoku JMA EEW timeline (`8.6 s` initial Miyagi warning), `M_JMA ~ 8.0–8.1` point-source saturation, Kanto under-prediction, and aftershock false-alarm post-mortem |
| Böse, Heaton, Hauksson (`2012`) | *Geophysical Journal International* `191(2):803–812`, `DOI: 10.1111/j.1365-246X.2012.05629.x` | `FinDer` real-time 2D spatial `PGA` binary-image template correlation recovering finite-fault length $L$, strike, and $R_{\text{rup}}$ |
| Berger, George, LeVeque, Mandli (`2011`) | *Advances in Water Resources* `34(9):1195–1206`, `DOI: 10.1016/j.advwatres.2011.02.016` | Well-balanced augmented Riemann solver, moving wet-dry shoreline positivity, and multi-scale tsunami AMR in `GeoClaw` |
| Preserved Executable Probe | `reports/seismic-eew-magnitude-saturation-p-arrival-pickers-and-tsunami-geoclaw/probes/verify_eew_saturation_geoclaw.py` (observed `2026-11-19`) | Deterministic Python 3 verification of `STA/LTA = 20.00` `1`-sample glitch, `libmseed` `2016-12-31T23:59:60 == 2017-01-01T00:00:00` collision, `3`-of-$N$ causal-cone rejection, `31.6x` Tohoku moment error & `228 km -> 60 km` `R_rup`, and `GeoClaw` `h_c = 0.0 m` vs. `+9.0 m` / `-4.0 m` naive AMR |

## Revalidation

Run either the preserved package probe from the corpus root (`python3 reports/seismic-eew-magnitude-saturation-p-arrival-pickers-and-tsunami-geoclaw/probes/verify_eew_saturation_geoclaw.py`) or the standalone zero-dependency bash probe below from any directory (`Python >= 3.10`):

```bash
python3 - <<'EOF'
import math

# 1. ObsPy STA/LTA 1-sample spike ceiling (nlta/nsta = 20.0) & SeisComP libmseed sec==60 fold
nsta, nlta = 50, 1000
csta, clta = 1.0 / nsta, 1.0 / nlta
sta, lta = 0.0, 2.2250738585072014e-308
trace = [1e-3 * ((-1.0) ** i) for i in range(1500)]
trace[1200] = 5.0
spike_ratio = 0.0
for i in range(1, len(trace)):
    sq = trace[i] * trace[i]
    sta = csta * sq + (1.0 - csta) * sta
    lta = clta * sq + (1.0 - clta) * lta
    if i == 1200:
        spike_ratio = sta / lta
assert spike_ratio > 19.99

def ms_time2nstime_int(year, yday, hour, minute, sec):
    sy = year - 1900
    a4 = (sy >> 2) + 475 - int(not (sy & 3))
    a100 = a4 // 25 - int(a4 % 25 < 0)
    days = 365 * (sy - 70) + ((a4 - 492) - (a100 - 19) + ((a100 >> 2) - 4)) + (yday - 1)
    return (60 * (60 * (24 * days + hour) + minute) + sec) * 1_000_000_000

assert ms_time2nstime_int(2016, 366, 23, 59, 60) == ms_time2nstime_int(2017, 1, 0, 0, 0)
# 2 km station baseline max causal dt = 2.0 / 4.5 + 0.10 = 0.544 s < 1.000 s leap skew:
assert 2.0 / 4.5 + 0.10 < 1.0

# 2. 2011 Mw 9.0 Tohoku (L=450 km) point-source saturation vs FinDer line template
moment_err = 10.0 ** (1.5 * (9.0 - 8.0))
mw_finder = (math.log10(450.0) + 2.44) / 0.59
r_hypo = math.hypot(220.0, 60.0)
r_rup = math.hypot(220.0 - min(max(220.0, 0.0), 450.0), 60.0)
assert abs(moment_err - 31.6227766) < 1e-4 and 8.62 <= mw_finder <= 8.64
assert r_hypo > 228.0 and r_rup == 60.0

# 3. GeoClaw update.f90:141-160 shoreline AMR positivity & lake-at-rest preservation
fine_h, fine_b = [0.0, 0.0, 0.0, 20.0], [12.0, 12.0, 12.0, -20.0]
bc = sum(fine_b) / 4.0  # +4.0 m
naive_eta = sum(fine_h) / 4.0 + bc
wet_eta = [h + b for h, b in zip(fine_h, fine_b) if h > 1e-3]
unclamped_h = sum(wet_eta) / len(wet_eta) - bc
hav = sum(fine_h) / len(wet_eta)
geoclaw_hc = min(hav, max(sum(wet_eta) / len(wet_eta) - bc, 0.0))
assert naive_eta == 9.0 and unclamped_h == -4.0 and geoclaw_hc == 0.0
print("REVALIDATION_OK")
EOF
```

Revalidate upstream implementations when:
1. `SeisComP/seiscomp` updates bundled `libmseed` (`ms_time2nstime`) or `seedlink` to emit native `TAI` nanosecond timestamps or consult `leapsecondlist` during `sec == 60` decoding;
2. `FinDer` replaces Wells & Coppersmith (`1994`) 1D line-length templates with 3D curved subduction-slab mesh templates (`FinDer v3+`); or
3. `clawpack/geoclaw` modifies `src/2d/shallow/update.f90` (`hc` restriction) or enables dispersive Boussinesq (`SGN`) equations by default on coastal inundation grids.
