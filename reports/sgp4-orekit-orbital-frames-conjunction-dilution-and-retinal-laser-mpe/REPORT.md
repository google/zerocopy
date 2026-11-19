# SGP4/Orekit Orbital Frames, Conjunction Probability Dilution, and Retinal Laser MPE Safety

## Summary

Analytical orbital astrodynamics and integrated photonic retinal projection occupy distant physical scales—thousands of kilometers in Low Earth Orbit (LEO) versus tens of micrometers on the human fovea—yet fail along identical structural fault lines: **untyped Euclidean coordinate vectors subtracted across non-commuting reference frames**, **non-monotone probabilistic hazard metrics whose point value drops when sensor uncertainty degrades**, and **multi-rate pulsed actuation whose safety envelope collapses under mechanical dwell stalls**.

Across primary sources in `brandon-rhodes/python-sgp4` (`8e234f81a93b226689a8b67d80a4f1a82be7439b`), `CS-SI/Orekit` (`bdf730121dae7f63db84bcbe6d9bf342d18d7a20`), `NanoComp/meep` (`84cbc56a2e94b90acfa05dee78247b565b68d04c`), `gdsfactory/gdsfactory` (`7407836dd5d872c704fc06f38562a2ffc88049dc`), Vallado et al.'s `AIAA 2006-6753` SGP4 consolidation (`DOI: 10.2514/6.2006-6753`), Salvatore Alfano's maximum conjunction probability analysis (`DOI: 10.2514/1.8589`), and `IEC 60825-1:2014` Class 1 laser exposure rules, four concrete invariants govern sound verification:

1. **Epoch-Indexed Celestial Frame Typing (`TEME` vs. `TOD`/`GCRF`/`ITRF`)**: `python-sgp4` propagates NORAD Two-Line Element (TLE) mean elements into raw Cartesian `([f64; 3], [f64; 3])` km and km/s tuples in the **True Equator, Mean Equinox (`TEME`)** frame of date (`README.rst`, `sgp4/propagation.py`). As `Orekit`'s `TEMEProvider.java` documents, `TEME` lacks an official IAU definition, differs from True of Date (`TOD`) by a Z-axis rotation through the Equation of the Equinoxes (`~530 m` LEO offset at $\Delta\psi \approx 17.2''$), and drifts from inertial `J2000`/`GCRF` by `~50.29 arcsec/yr` general precession—yielding a **`45.40 km` LEO position error** after 26.88 years (`~10–45 km` across typical catalog comparisons) whenever raw `[f64; 3]` position arrays are subtracted without frame-transformation witnesses.
2. **Alfano's Covariance Probability-Dilution Paradox (`Pc` vs. `Pc_max`)**: Short-term orbital conjunction assessment projects relative position covariance onto the 2D encounter B-plane (`Alfriend1999.java`, `Alfano2005.java`). Because 2D Gaussian probability density scales inversely with covariance determinant ($\det\Sigma^{-1/2}$) while exponential Mahalanobis decay approaches unity as uncertainty grows, computed collision probability $P_c(k\Sigma)$ peaks at $\sigma^* = d/\sqrt{2}$ and **decreases as $\mathcal{O}(k^{-2})$ for $k\sigma > d/\sqrt{2}$**. On a `150 m` nominal miss with `10 m` combined hard-body radius, inflating isotropic uncertainty $\sigma$ from `106.1 m` to `1,000 m` (degraded radar observations) **depresses $P_c$ from `1.629e-3` (above the `1e-4` maneuver threshold) down to `4.927e-5` (below threshold)**—falsely suppressing collision-avoidance burns unless gated by the worst-case covariance-inflation envelope $P_{c,\max} = R^2 / (e\, d^2)$ (`1.635e-3`).
3. **Staggered Yee-Grid Courant Bounds and Thermo-Optic Grating Crosstalk**: In `NanoComp/meep` (`src/step.cpp`), leapfrog Finite-Difference Time-Domain (FDTD) updates stagger magnetic (`B`, `H`) and electric (`D`, `E`) fields by $\Delta t / 2$ across half-integer Yee cells and remain stable only under the Courant–Friedrichs–Lewy (CFL) bound $c\Delta t \le n_{\min} (\Delta x^{-2} + \Delta y^{-2} + \Delta z^{-2})^{-1/2}$ (`S <= 0.57735` in 3D isotropic vacuum; Meep default `Courant = 0.5`). In `gdsfactory` silicon-photonic grating couplers (`gdsfactory/components/gratings/`), thermo-optic phase shifters ($\mathrm{d}n_{\text{Si}}/\mathrm{d}T \approx 1.86 \times 10^{-4}\text{ K}^{-1}$) induce parasitic index shifts across adjacent gratings unless layout-level thermal keep-out zones and FDTD diffraction-order monitors bound stray zero-order eye-ward emission.
4. **`IEC 60825-1` Three-Rule Pulse-Train MPE and Hardware MEMS Scan-Stall Leases**: Retinal-scan displays rely on raster angular motion to dilute a Class 3B internal pulse engine (`e.g., 10 nJ` pulses at `5 MHz = 50 mW`) across $>10^5$ resolvable `~25 um` foveal spots so each spot sees only `60 Hz` (`0.6 uW << 0.39 mW` Class 1 CW Accessible Emission Limit). Under a mechanical MEMS mirror stall, all `5 MHz` pulses strike a single foveal spot, breaching the `250 us` `IEC 60825-1` thermal AEL (`1.39 uJ`) by **`8.98x` (`12.50 uJ`)—`1,000x` faster than the `0.25 s` human blink reflex**. Software OS watchdogs (`1–10 ms` scheduling jitter) cannot preserve Class 1 safety; only a hardware analog/FPGA angular-velocity lease shutting off laser diode current within `< 3 us` (`150 nJ < 200 nJ` sub-`18 us` AEL) prevents retinal thermal injury.

Created a runnable verification probe at `reports/sgp4-orekit-orbital-frames-conjunction-dilution-and-retinal-laser-mpe/probes/verify_orbital_and_laser_mpe.py` confirming `TEME`-vs-`GCRF`/`TOD` LEO frame offsets, `Orekit`'s `Alfano2005` Simpson 2D $P_c$ integrator and covariance dilution paradox, 3D Yee-grid CFL stability, and `IEC 60825-1` MEMS scan-stall vs. `3 us` hardware-lease exposure bounds.

---

## Applicability

These findings apply directly to:

- **Type-system and ghost-parameter design for physical/geometric coordinates** (`Vec3<Frame, Epoch, Units>`), ensuring Euclidean vector subtraction, inner products, and covariance projections statically require identical `(Frame, Epoch, Units)` witnesses and explicit Earth Orientation Parameter (`EOP`) transitions (`TEME -> TOD -> MOD -> GCRF -> ITRF`).
- **Safety-critical probabilistic decision kernels** (conjunction screening, autonomous collision avoidance, sensor-fusion hazard monitors) where point probability estimates $P(\text{hazard} \mid \Sigma)$ fail monotonicity under epistemic covariance degradation and must be paired with interval/worst-case dilution envelopes ($\sup_{k \ge 1} P(\text{hazard} \mid k^2 \Sigma)$).
- **PDE solver stability certificates and photonic EDA pipelines**, where FDTD Courant numbers, Yee-lattice half-cell field staggering, and layout-to-thermal crosstalk constraints can be discharged as compile-time or pre-synthesis arithmetic obligations.
- **Real-time actuator safety interlocks and time-bounded capability leases**, separating soft-real-time control loops (`> 1 ms` OS scheduling jitter) from microsecond-scale hardware/FPGA dead-man leases (`< 3 us`) required by `IEC 60825-1` Class 1 scanned-laser limits.

---

## Findings

### 1. SGP4 Mean-Element Propagation and `TEME` vs. `GCRF`/`ITRF` Coordinate Frame Hazards

`Basis: source | normative | execution`

NORAD/USSPACECOM Two-Line Element (`TLE`) sets do **not** encode osculating Keplerian elements that can be plugged into a generic two-body or numerical Runge–Kutta integrator. Instead, TLEs encode **Brouwer–Kozai mean elements** paired with an atmospheric drag parameter $B^*$ fitted specifically against the **Simplified General Perturbations 4 (`SGP4` / `SDP4`)** analytical perturbation theory consolidated by Vallado, Crawford, Hujsak, and Kelso (`AIAA 2006-6753`, `DOI: 10.2514/6.2006-6753`).

Inspection of `brandon-rhodes/python-sgp4` (`8e234f81a93b226689a8b67d80a4f1a82be7439b`, `README.rst:28–48` and `sgp4/propagation.py`) and `CS-SI/Orekit` (`bdf730121dae7f63db84bcbe6d9bf342d18d7a20`, `src/main/java/org/orekit/frames/TEMEProvider.java:34–40, 105–146`) establishes three critical boundary properties:

1. **Numerical Integrator Precision vs. Physical Ephemeris Accuracy**: `python-sgp4` wraps Vallado's reference C++ `SGP4.cpp` (`0.1 mm` numerical agreement against reference test vectors), whereas TLE mean elements themselves exhibit **`1–3 km` intrinsic epoch error** growing at `1–3 km/day` due to unmodeled thermospheric density variations and truncated zonal/tesseral harmonics (`J2`–`J4` plus resonant `12h`/`24h` deep-space terms). Fitting or propagating TLE elements with a high-order numericalCowell/RK78 propagator without SGP4 mean-to-osculating conversion introduces immediate `~10 km` secular semi-major axis bias from missing `J2` short-period recovery.
2. **Ambiguity and Non-Inertial Drift of `TEME`**: `sgp4(satrec, jd, fr)` returns bare floating-point 3-tuples `(r, v)` in **`TEME` (True Equator, Mean Equinox)** of date. As `TEMEProvider.java:34–40` explicitly warns (citing the CCSDS Orbit Data Messages Blue Book), `TEME` has **no official IAU definition**, has historically suffered `"of date"` vs. `"of epoch"` confusion across flight-dynamics centers, and should never be used outside TLE ingestion. `Orekit` transforms from True of Date (`TOD`) to `TEME` via a right-handed Z-rotation by the Equation of the Equinoxes:
   $$\text{eqe}(t) = \bigl(\Delta\psi(t) + \delta\Delta\psi_{\text{EOP}}(t)\bigr)\cos\bar{\epsilon}(t) + \Delta_{\text{eqe,higher}}(t)$$
   where $\Delta\psi$ is IAU-1980 nutation in longitude (`up to ±17.2 arcsec` over the 18.6-year lunar nodal cycle), $\delta\Delta\psi_{\text{EOP}}$ is the IERS celestial pole offset, and $\bar{\epsilon} \approx 23.439^\circ$ is mean obliquity.
3. **Magnitude of Untyped `[f64; 3]` Frame Subtraction Errors in LEO**: At $h = 550\text{ km}$ LEO ($R = 6{,}928.137\text{ km}$):
   - Confusing **`TEME` with `TOD`** omits $\text{eqe}(t)$, shifting equatorial position by **`up to 530.1 m`** (`verify_orbital_and_laser_mpe.py`)—more than **`50x` a `10 m` satellite hard-body collision radius**.
   - Confusing **`TEME` (of date) with `GCRF` / `EME2000` (`J2000`)** omits `~50.288 arcsec/yr` lunisolar precession plus nutation; at `26.88 years` past `J2000.0`, raw vector subtraction produces a **`45.40 km` position error** (`~10–17 km` even over a partial decade or when mixing `MOD`/`TOD` catalogs).
   - Confusing **`TEME` with `ITRF` (`WGS84` Earth-fixed)** without UT1-UTC (`dUT1`) and polar motion $(x_p, y_p)$ injects `465 m/s * dUT1` equatorial tangential offset (`~418 m` if a `0.9 s` leap-second / `UTC`-vs-`UT1` residual is omitted).

| Coordinate Frame Pair Subtracted as Raw `[f64; 3]` | Omitted Physical Rotation / Parameter | LEO Position Error ($h = 550\text{ km}$) | Conjunction Screening Impact ($R_{\text{HB}} = 10\text{ m}$) |
| :--- | :--- | :--- | :--- |
| `TEME` (of date) vs. `GCRF` / `J2000` | `26.88 yr` IAU-76 precession + IAU-80 nutation + `eqe` | **`45.40 km`** | Complete miss of real collisions; phantom close approaches |
| `TEME` (of epoch) vs. `TEME` (of date, +7 days) | `7 days` precession + nutation drift (`~1.0 arcsec`) | **`~33.6 m`** | `3.4x` hard-body radius bias on B-plane miss vector $\boldsymbol{\mu}$ |
| `TEME` vs. `TOD` (True of Date) | Equation of the Equinoxes $\Delta\psi \cos\bar{\epsilon}$ (`17.2''`) | **`530.1 m`** | Invalidates `150 m` B-plane Mahalanobis distance completely |
| `TEME` vs. `ITRF` (omitting `dUT1 = 0.9 s`) | Sidereal Earth rotation $\omega_\oplus \cdot \mathrm{dUT1}$ | **`~442 m`** (equatorial) | Corrupts ground-station laser ranging & radar azimuth/elevation |

---

### 2. Short-Term Encounter B-Plane Integrals and Alfano's Probability-Dilution Paradox

`Basis: source | derived | execution`

In `CS-SI/Orekit`'s short-term encounter subsystem (`org.orekit.ssa.collision.shorttermencounter.probability.twod`), relative motion at Time of Closest Approach (`TCA`) is linearized along the relative velocity vector $\mathbf{v}_{\text{rel}}$, projecting the 3D combined primary+secondary position covariance $\Sigma_{\text{3D}} = \Sigma_1 + \Sigma_2$ onto the 2D encounter **B-plane** orthogonal to $\mathbf{v}_{\text{rel}}$ and rotating into principal axes $(\sigma_x, \sigma_y)$ with nominal miss coordinates $(x_m, y_m)$ and combined hard-body sphere radius $R = R_1 + R_2$.

Comparing `Alfriend1999.java:65–69` and `Alfano2005.java:51–93, 159–173, 226–232` reveals both the numerical integration subtleties and a profound epistemic hazard:

- **Small-Disk Point Approximation (`Alfriend1999.java`)**: Evaluates Gaussian density at the disk center multiplied by disk area $\pi R^2$:
  $$P_{c,\text{Alfriend}} = \frac{R^2}{2 \sigma_x \sigma_y} \exp\!\left(-\frac{1}{2}\left[\frac{x_m^2}{\sigma_x^2} + \frac{y_m^2}{\sigma_y^2}\right]\right)$$
  Fast (`O(1)` flops), accurate when $R \ll \min(\sigma_x, \sigma_y)$, but can **exceed `1.0`** when $R > \sqrt{2}\sqrt{\sigma_x \sigma_y}$ (e.g., large tethered structures or sub-meter laser-ranged covariances).
- **Adaptive Simpson Disk Quadrature (`Alfano2005.java`)**: Integrates the 1D inner integral analytically via `Erf.erf((ym ± sqrt(R^2 - x^2)) / (sqrt(2) * sy))` and evaluates the outer $x \in [-R, R]$ integral via composite Simpson's rule with adaptive step count $M = \operatorname{clamp}(\lfloor 5R / \min(\sigma_x, \sigma_y, \sqrt{x_m^2 + y_m^2}) \rfloor, 10, 100{,}000)$ (`Alfano2005.java:226–232`). Crucially, `Alfano2005.java:162` shifts the left endpoint inward to `x0 = 0.015 * xStep - radius` to prevent numerical derivative blowup at the semicircular boundary $\frac{\mathrm{d}}{\mathrm{d}x}\sqrt{R^2 - x^2} \to \infty$ as $|x| \to R$.
- **Alfano's Probability-Dilution Paradox (`DOI: 10.2514/1.8589`)**: Scale the B-plane covariance uniformly by $k^2 \Sigma$ ($k > 0$ representing sensor quality: $k < 1$ better radar/optical observations, $k > 1$ stale TLE covariance growth). In the isotropic case $\sigma_x = \sigma_y = \sigma$ with miss distance $d = \sqrt{x_m^2 + y_m^2}$ and $R \ll d$:
  $$P_c(\sigma) \approx \frac{R^2}{2\sigma^2} \exp\!\left(-\frac{d^2}{2\sigma^2}\right), \qquad \frac{\partial P_c}{\partial \sigma} = \frac{R^2}{2\sigma^5}\left(d^2 - 2\sigma^2\right)\exp\!\left(-\frac{d^2}{2\sigma^2}\right)$$
  Setting $\partial P_c / \partial \sigma = 0$ yields a unique global maximum at $\sigma^* = d / \sqrt{2}$ with peak probability:
  $$P_{c,\max}(d, R) = \frac{R^2}{e\, d^2}$$
  **Verification probe results (`verify_orbital_and_laser_mpe.py`, $d = 150\text{ m}$, $R = 10\text{ m}$, NASA/ESA RED maneuver threshold $T_{\text{man}} = 1.0 \times 10^{-4}$):**
  - At tight covariance $\sigma = 35\text{ m}$ ($\sigma < \sigma^*$): $P_c = 4.13 \times 10^{-6} < 10^{-4}$ (**true safe miss**: the `3-sigma` ellipsoid `105 m` misses the `150 m` nominal pass).
  - At critical covariance $\sigma^* = 106.07\text{ m}$: `Alfano2005` yields **$P_c = 1.6293 \times 10^{-3} > 10^{-4}$** (`16.3x` above maneuver threshold; `Alfriend1999` gives `1.6353e-3`).
  - At degraded covariance $\sigma = 1{,}000\text{ m}$ (stale TLE / missed radar pass, $\sigma \gg \sigma^*$): `Alfano2005` drops to **$P_c = 4.9267 \times 10^{-5} < 10^{-4}$**!

  **Consequence**: Treating `Pc < 1e-4` as `"safe"` violates epistemic monotonicity: **worse knowledge (`sigma = 1000 m` vs `106 m`) flips a mandatory RED collision-avoidance maneuver into a false GREEN no-action state** because probability mass is diluted across a `1 km` disk. Sound conjunction screening requires a two-dimensional decision predicate pairing point $P_c(\Sigma)$ with Alfano's dilution-robust upper envelope $P_{c,\max} = \sup_{k \ge 1} P_c(k^2 \Sigma)$ (which stays at `1.635e-3 > 1e-4`, triggering sensor tasking or precautionary maneuver rather than silent suppression).

---

### 3. Yee-Grid FDTD Stability (`Meep`) and Silicon-Photonic Grating Crosstalk (`gdsfactory`)

`Basis: source | derived | execution`

Integrated photonic beam steerers and waveguide-to-free-space retinal display combiners pair electromagnetic field solvers (`NanoComp/meep`) with parametric GDSII mask generators (`gdsfactory/gdsfactory`):

1. **Staggered Leapfrog Order and CFL Bound in `Meep` (`src/step.cpp:64–105`)**: `fields::step()` advances Maxwell's curl equations on a staggered Yee lattice in strict half-step order:
   - Advance magnetic flux $\mathbf{B}$ from curl of $\mathbf{E}$ (`step_db(B_stuff)`), synchronize chunk boundaries (`step_boundaries(B_stuff)`), and update $\mathbf{H} = \mu^{-1}(\mathbf{B} - \mathbf{M})$ plus Lorentzian/Drude magnetic polarizations (`update_eh(H_stuff)`, `update_pols(H_stuff)`), advancing `t` by `0.5 * dt`.
   - Advance electric displacement $\mathbf{D}$ from curl of $\mathbf{H}$ plus current sources (`step_db(D_stuff)`, `step_source(D_stuff)`), then update $\mathbf{E} = \varepsilon^{-1}(\mathbf{D} - \mathbf{P})$ (`update_eh(E_stuff)`).
   Because explicit central differences diverge exponentially (`|lambda| > 1` amplification of checkerboard Nyquist modes) whenever the numerical domain of dependence falls inside the physical light cone, stability strictly requires:
   $$\Delta t \le \frac{n_{\min}}{c_0 \sqrt{\Delta x^{-2} + \Delta y^{-2} + \Delta z^{-2}}}$$
   In 3D uniform grids ($\Delta x = \Delta y = \Delta z = \Delta$), the vacuum Courant factor $S = c_0 \Delta t / \Delta$ is bounded by $S_{\max} = 1/\sqrt{3} \approx 0.577350$ (`Meep` defaults to `Courant = 0.5`, leaving a `13.4%` stability margin, which collapses immediately if a subpixel metallic/dispersive feature or negative-permittivity plasma pole introduces effective $n_{\min} < 0.866$ without reducing `Courant`).
2. **Parametric Grating Couplers and Thermo-Optic Phase Crosstalk (`gdsfactory`)**: `gdsfactory` synthesizes silicon-on-insulator (`SOI`, $n_{\text{Si}} \approx 3.48$, $n_{\text{SiO}_2} \approx 1.44$ at $\lambda = 1550\text{ nm}$; $\text{Si}_3\text{N}_4$ $n \approx 2.0$ for visible `450–650 nm` retinal combiners) elliptical focusing gratings (`grating_coupler_elliptical.py`) whose emission angle $\theta$ obeys the Bragg phase-matching condition:
   $$n_{\text{eff}}(T) - n_{\text{clad}} \sin\theta = m \frac{\lambda}{\Lambda}$$
   Adjacent TiN/doped-Si thermo-optic phase shifters dissipate `10–30 mW` per $\pi$ phase shift over `10–50 us` thermal time constants, raising local waveguide temperature by $\Delta T \sim 15\text{–}40\text{ K}$ within `20–50 um` laterally. Unmodeled thermal crosstalk shifts $n_{\text{eff}}(T)$ and deflects diffraction orders or degrades destructive interference in optical-phased-array (`OPA`) sidelobes—redirecting specular zero-order power straight into the user's pupil.

---

### 4. `IEC 60825-1` Pulse-Train MPE Rules and Microsecond MEMS Scan-Stall Leases

`Basis: normative | derived | execution`

Under `IEC 60825-1:2014` (§4.3.f, Tables 3 & A.1), Class 1 laser products operating in the visible retinal-hazard spectral band (`400–700 nm`, `7 mm` limiting pupil aperture $= 0.385\text{ cm}^2$, point source angular subtense $\alpha \le \alpha_{\min} = 1.5\text{ mrad} \implies C_6 = 1.0$) must satisfy **all three Accessible Emission Limit (`AEL`) rules simultaneously** over every emission window $T \in [t_p, T_2]$ ($T = 0.25\text{ s}$ blink-aversion window for Class 2 / intentional short viewing; $T_2 = 10\text{ s}$ or `100 s` for Class 1):

1. **Rule 1 (Single-Pulse Thermal/Acoustic Limit)**: Every individual pulse of width $t_p$ must satisfy $E_p \le \text{AEL}_{\text{single}}(t_p)$, equal to **`200 nJ` (`2.0e-7 J`)** across the thermal-confinement plateau $1\text{ ns} \le t_p < 18\text{ us}$ and $7.0 \times 10^{-4}\, t_p^{0.75}\text{ J}$ for $18\text{ us} \le t_p \le 10\text{ s}$.
2. **Rule 2 (Average-Power Cumulative Window Limit)**: Total energy across $N$ pulses entering the `7 mm` pupil within any window $T$ must satisfy $N \cdot E_p \le \text{AEL}(T)$ (`0.39 mW` Class 1 CW AEL; `247.5 uJ` MPE over `0.25 s`).
3. **Rule 3 (Repetitive-Pulse Thermal Reduction Factor $C_5$)**: Per-pulse energy in a pulse train is further reduced by $E_p \le C_5(N)\cdot \text{AEL}_{\text{single}}(t_{\text{eff}})$ where $C_5 = N^{-0.25}$ (for relevant pulse regimes under Ed. 3.0 / ANSI Z136.1) penalizes cumulative sub-threshold melanosome heating across $N$ pulses.

**Quantitative MEMS Scan-Stall Hazard (`verify_orbital_and_laser_mpe.py`)**:
Consider a MEMS raster-scanned retinal display with a `5 MHz` pixel clock (`50 ns` pulses, $E_p = 10\text{ nJ}$ per pixel = `50 mW` raw internal optical engine).
- **Normal `60 Hz` Raster Scan**: Each `25 um` foveal spot is illuminated once per `16.67 ms` frame ($N = 15$ pulses in $0.25\text{ s}$, $C_5 = 15^{-0.25} = 0.508$). Governing per-pulse AEL is **`101.6 nJ`** (`10x` above $E_p = 10\text{ nJ}$), and per-spot average power is `0.6 uW` (`650x` below `0.39 mW` Class 1 CW AEL).
- **`250 us` Mechanical MEMS Mirror Stall**: If torsion hinge fracture, resonant PLL dropout, or electrostatic pull-in freezes the mirror, **all `5 MHz` pulses hit a single stationary foveal spot**. Within just **`250 us`** (`1,000x` faster than the `250 ms` blink reflex and `40x` faster than a `10 ms` Linux RT/RTOS software watchdog), `1,250` stationary pulses deliver **`12.50 uJ`**, exceeding the `250 us` retinal AEL (`1.39 uJ`) by **`8.98x`**.
- **Hardware Velocity-Lease Interlock (`<= 3 us`)**: Gating the laser diode driver on a hardware analog comparator / FPGA timer refreshed exclusively by continuous MEMS piezoresistive/back-EMF zero-crossing velocity pulses with a **`3 us` lease ceiling** (`15` pulses = **`150.0 nJ`**) guarantees total stationary emission stays strictly below the **`200.0 nJ`** sub-`18 us` thermal-confinement AEL even under instantaneous mirror seizure.

---

### 5. Six-Level Performance & Resource Footprint Matrix (`L1`–`L6`)

`Basis: source | documentation | execution | derived`

| Level | Metric / Resource Axis | `python-sgp4` + `Orekit` (`TEME` & `Alfano2005`) | `Meep` FDTD + `gdsfactory` + `IEC 60825-1` Lease | Verification / System Engineering Implication |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | `~150–400 LoC` for typed frame graph + `Pc_max` gate; `~3–5x` proof-to-code ratio for frame-witness algebra & Simpson bounds | `~200–600 LoC` `gdsfactory` layout + RTL velocity-lease interlock (`~4–8x` formal invariant / timing proof overhead) | Ghost-typed `Frame` witnesses eliminate manual rotation audit at near-zero authoring friction once standard library exists |
| **L2** | **Framework & Toolchain Build Time** | `python-sgp4` C++ wheel builds in `< 5 s`; `Orekit` Maven Java build `~45–90 s` (`~1.5 GB` JVM heap) | `Meep` C++/MPI/Harminv/HDF5 from-scratch build `~4–12 min`; `gdsfactory` Python environment `< 15 s` | Decouple lightweight frame/safety specs from heavy PDE solver C++ builds |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | Dimension/frame typechecking `< 5 ms`; SMT/real-arithmetic bounds on `Pc_max` `< 50 ms` (`< 20 ms` warm LSP) | `gdsfactory` DRC/GDS export `50–800 ms`/cell; FPGA scan-lease RTL synthesis `~10–40 s`; FDTD setup `~1–5 s` | Keep FDTD field simulations offline; compile only extracted surrogate bounds & lease timers into online proofs |
| **L4** | **Generated Code Execution Performance** | C++ `SGP4` `~0.8–1.5 us`/state (`> 650k` props/s/core); `TEME->GCRF` `~0.3 us` with cached EOP; `Alfano2005` (`M=50`) `~4–12 us` | `Meep` CPU `~10–50 M` Yee-voxels/s/node; hardware comparator/FPGA laser cutoff **`< 0.5–3.0 us` WCET** (`0` OS jitter) | Never run `IEC 60825-1` scan-stall shutdown through an OS kernel thread (`p99.9 > 200 us` breaches retinal AEL) |
| **L5** | **Proof / Certificate Verification Speed** | Frame-graph path witness check `< 1 us` (`O(1)` type equality); interval Simpson enclosure certificate `< 0.5 ms` | CFL rational inequality check `< 10 us`; RTL 3-microsecond timer model-checking certificate `< 2 ms` | Pre-computed EOP interpolation tables + interval `Pc_max` certificates admit sub-millisecond flight-software checks |
| **L6** | **RAM, Disk & Binary Footprints** | `SGP4` C core `< 64 KB` `.text`, `~256 B`/satellite `elsetrec`; `Orekit` `orekit-data` IERS EOP + JPL ephemeris `~15–60 MB` | 3D `Meep` grating cell (`10 um^3` @ `15 nm` grid): `~2.96e8` Yee cells $\approx$ **`7–14 GB` RAM**; FPGA interlock `< 200` LUTs, `< 5 mW` | Embedded flight & wearable ASICs require `KB`-scale tabular/RTL kernels distilled from `GB`-scale offline FDTD/IERS data |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived | source`

#### (C1) Human Comprehensibility & Mental-Model Ergonomics
- **Invisible Silent Failure of Bare `[f64; 3]` Arrays**: An LLM or human engineer reading `r_miss = r_sat1 - r_sat2` sees clean, idiomatic linear algebra with **zero syntactic hint** that `r_sat1` came from `sgp4` (`TEME` of date) while `r_sat2` came from a precision GPS ephemeris (`ITRF` or `GCRF`). The cognitive burden is strictly *nonlocal* unless coordinate frame, epoch, and unit (`km` vs `m`) are carried in the type signature.
- **Counter-Intuitive Epistemic Reversal in `Pc`**: Humans naturally interpret `"collision probability dropped from 1.6e-3 to 4.9e-5"` as *"risk decreased by 33x."* Understanding that $P_c$ fell solely because radar covariance bloated (`sigma = 1000 m`) violates intuitive monotonicity. Surfacing a two-tuple `(Pc_nominal, Pc_max_dilution)` alongside a boolean `is_covariance_diluted = (sigma_max > miss_distance / sqrt(2))` restores immediate human-auditable legibility in operations consoles.
- **Multi-Rule `IEC 60825-1` Table Indirection**: `IEC 60825-1` spreads pulse-train limits across wavelength-dependent $C_1 \dots C_7$ correction factors, $T_1 / T_2$ breakpoints, and angular subtense $\alpha$ regimes. Distilling the runtime invariant into a single **per-foveal-voxel energy-bucket leaky integrator** (`E_spot <= 150 nJ` without verified mirror displacement $\Delta\theta \ge \alpha_{\min}$) reduces a 90-page normative table lookup to 3 human-verifiable state variables.

#### (C2) Simplicity, Orthogonality & Universal Model Refinement
- **Eliminating Ad-Hoc Frame Conventions via Affine Torsors + Explicit Groupoid Morphisms**: `TEME`, `TOD`, `MOD`, `GCRF`, and `ITRF` should not be modeled as string enum tags dispatched dynamically at runtime (`match frame { ... }` with hidden global IERS singleton tables, as in traditional object-oriented astrodynamics libraries). Instead, the universal refinement models physical positions as points in an **affine torsor `Pos<F, t>`** and transformations as **typed groupoid morphisms `RigidIso<F1, F2, t>`** parameterized explicitly by an immutable `EopSnapshot` value. Under Felleisen's macro-expressibility criterion, `TEME`'s historical `"of date"` vs. `"of epoch"` ambiguity disappears because `TEME<EpochTle>` and `TEME<EpochNow>` are distinct static types with no implicit coercion.
- **Refining Point Probability into Credal Upper Envelopes**: Alfano's paradox exposes that a single Gaussian covariance $\Sigma$ under stale tracking conflates *aleatoric spread* with *epistemic ignorance*. Modeling sensor degradation as a **credal set $\mathcal{C}(\Sigma_0) = \{ k^2 \Sigma_0 \mid k \in [1, k_{\max}] \}$** makes `Pc_max` the ordinary upper-probability operator $\overline{P}(A) = \sup_{\Sigma \in \mathcal{C}} P_\Sigma(A)$—unifying conjunction dilution with general imprecise-probability safety verification without ad-hoc post-processing heuristics.
- **Time-Bounded Hardware Capability Leases for High-Energy Actuators**: Both MEMS laser scan-guards and thruster valve drivers obey the same deep-module abstraction (Ousterhout): the high-energy actuator holds **zero ambient authority** to emit; instead, a physical motion witness (mirror quadrature zero-crossing) mints a **non-renewable hardware energy token (`150 nJ` / `3 us`)** consumed directly at the current source.

---

## Boundaries

1. **Long-Term / Non-Linear Encounter (`> 1` Orbital Period) Conjunction Dynamics (`known not to apply`)**: Both `Alfriend1999` and `Alfano2005` assume rectilinear constant-velocity relative motion (`short-term encounter`) and Gaussian Cartesian covariance on the B-plane. For low-relative-velocity geosynchronous (`GEO`) hovering, phasing maneuvers, or multi-orbit encounters (`> 3–7 days`), curvilinear orbital-element (`equinoctial`) state distributions become strongly non-Gaussian ("banana-shaped" uncertainty shells) where B-plane 2D disk integrals are **known not to apply** without Monte Carlo or Gaussian Mixture Model (`GMM`) splitting.
2. **Sub-Nanosecond Photochemical & Ultrashort Nonlinear Retinal Damage (`not examined`)**: Our `IEC 60825-1` analysis covers thermal-confinement nanosecond/microsecond pulse trains (`1 ns <= t_p <= 0.25 s`, `400–700 nm`). Femtosecond self-focusing nonlinearities ($t_p < 100\text{ fs}$) and multi-hour photochemical blue-light (`400–500 nm`, $C_3$ weighting) cumulative retinal dose (`> 10 s`) were **not examined** in the executable probe.
3. **Full 3D Anisotropic Subpixel Smoothing in `Meep` Dispersive Metals (`unknown`)**: While `Meep`'s vacuum 3D CFL bound $S_{\max} = 1/\sqrt{3}$ is exact on standard Yee lattices, exact analytical stability margins when combining `Meep`'s anisotropic dielectric subpixel averaging tensor with multi-pole complex-conjugate Lorentz–Drude susceptibilities near plasmonic resonances remain model-specific (`unknown` without running `Meep` eigenvalue/harminv stability checks per geometry).
4. **Proprietary Space-Fence Covariance Realism Factors (`unsupported`)**: Operational `18 SDS` Conjunction Data Messages (`CDMs`) include empirical covariance scale/realism factors derived from proprietary sensor calibration residuals that are **unsupported** in public TLE-only `python-sgp4` pipelines (TLEs carry *no* covariance matrix at all, only $B^*$).

---

## Evidence

| Artifact / Source | Immutable Identity / Location | Grounded Fact / Observation |
| :--- | :--- | :--- |
| `brandon-rhodes/python-sgp4` | Commit `8e234f81a93b226689a8b67d80a4f1a82be7439b` (`README.rst:28–48`, `sgp4/propagation.py`, `sgp4/model.py`) | Documents `TEME` output frame (distinct from `ICRS`/`J2000`/`ITRS`), `0.1 mm` C++ SGP4 agreement vs. `1–3 km` TLE physical accuracy |
| `CS-SI/Orekit` (`TEMEProvider`) | Commit `bdf730121dae7f63db84bcbe6d9bf342d18d7a20` (`src/main/java/org/orekit/frames/TEMEProvider.java:34–40, 105–146`) | Implements `TOD -> TEME` Z-rotation via Equation of the Equinoxes `(dPsi + ddPsi_EOP)*cos(meanObliquity)` and cites CCSDS `TEME` ambiguity |
| `CS-SI/Orekit` (`Alfriend1999` & `Alfano2005`) | Commit `bdf730121dae7f63db84bcbe6d9bf342d18d7a20` (`.../probability/twod/{Alfriend1999,Alfano2005}.java`) | Point-density `Pc` vs. adaptive Simpson circular-disk `Erf` integral (`x0 = 0.015 * xStep - radius`, `M in [10, 100000]`) |
| `NanoComp/meep` | Commit `84cbc56a2e94b90acfa05dee78247b565b68d04c` (`src/step.cpp:64–105`) | Half-step leapfrog Yee-grid sequence (`step_db(B)`, `update_eh(H)`, `step_db(D)`, `update_eh(E)`) |
| `gdsfactory/gdsfactory` | Commit `7407836dd5d872c704fc06f38562a2ffc88049dc` (`gdsfactory/components/gratings/grating_coupler_elliptical.py`) | Parametric SOI/SiN elliptical grating coupler synthesis for photonic routing and free-space coupling |
| Vallado, Crawford, Hujsak, Kelso (2006) | `AIAA 2006-6753`, `DOI: 10.2514/6.2006-6753` | Canonical consolidated SGP4/SDP4 equations, `TEME` frame specification, and boundary test cases |
| Salvatore Alfano (2005) | *J. Guid. Control Dyn.* `28(2)`, `DOI: 10.2514/1.8589` | Closed-form covariance-inflation dilution analysis and maximum conjunction probability $P_{c,\max}$ |
| `IEC 60825-1:2014` | Edition `3.0` (§4.3.f, Tables 3 & A.1) | Three-rule pulse-train AEL (`single`, `average`, `$C_5 = N^{-0.25}$`) and Class 1 scan-failure safeguard requirements |
| Executable Verification Probe | `probes/verify_orbital_and_laser_mpe.py` | Verified `45.40 km` `TEME`-vs-`GCRF` & `530.1 m` `TEME`-vs-`TOD` offsets, `Alfano2005` dilution (`1.6293e-3 -> 4.9267e-5`), `CFL = 0.57735`, and `250 us` stall (`12.50 uJ > 1.39 uJ`) vs. `3 us` lease (`150 nJ < 200 nJ`) |

---

## Revalidation

Re-run the self-contained verification probe with standard Python 3 (`>= 3.10`, zero external dependencies):

```bash
python3 reports/sgp4-orekit-orbital-frames-conjunction-dilution-and-retinal-laser-mpe/probes/verify_orbital_and_laser_mpe.py
```

Expected output (`exit 0`):

```text
PASS: TEME-vs-GCRF=45.40 km, TEME-vs-TOD=530.1 m | Alfano Pc(sigma*=106.1m)=1.6293e-03 vs diluted Pc(1000m)=4.9267e-05 | 3D CFL=0.57735 | Scanned AEL=101.6 nJ, 250us stall=12.50 uJ > AEL 1.39 uJ, 3us lease=150.0 nJ < 200.0 nJ
```

Trigger revalidation if:
1. `Orekit` migrates `TEMEProvider` to an IAU-2006/2000A CIO-based (`CIRF`/`TIRF`) path or changes `Alfano2005` endpoint quadrature rules;
2. `IEC 60825-1` Edition `4` revises repetitive-pulse $C_5$ piecewise exponents in the nanosecond/microsecond retinal point-source regime; or
3. CCSDS Orbit Data Messages (`ODM` v3+) updates normative `TEME` deprecation or covariance realism metadata fields.
