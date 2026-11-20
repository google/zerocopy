# Rothermel spread and ELMFIRE level sets, NIST FDS low-Mach pressure zones and time-step control, and FLEXPART Lagrangian dispersion: regime limits in the code

## Summary

- **ELMFIRE's Rothermel kernel** (`lautenberger/elmfire@f4927b7c`, `elmfire_spread_rate.f90`) applies the cubic moisture-damping polynomial `η_M = 1 − 2.59r + 5.11r² − 3.52r³`, with `r = M/Mx`, clamped to `[0, 1]`.
  - `η_M(1) = 0` exactly, so spread goes to zero *continuously* at the moisture of extinction. The slope jumps from −2.93 to 0 there, which is a kink, not a step (derived).
  - Step discontinuities do exist elsewhere. The fuel table is indexed by `NINT(100·M_live_herb)`, clamped to 30–120, so properties are piecewise constant in 1 % moisture steps.
  - The back/head spread ratio jumps from 1.0 to 0.914 at length-to-breadth ratio 1.001, which corresponds to roughly 0.013 mph of effective wind (derived).
- **ELMFIRE wind and slope limits.** The active wind-speed limit is Rothermel's original `0.9·IR`; the Andrews–Cruz–Rothermel (2013) limit `96.8·IR^(1/3)` is present but commented out. The slope factor is capped at the wind factor evaluated at the limit. The two limits cross at `IR = 1115 Btu ft⁻² min⁻¹` (211 kW m⁻²); above that intensity the commented-out limit would be more restrictive (derived).
- **ELMFIRE has no level-set reinitialization.** The level-set field is advanced by a two-stage RK2 with Superbee-limited upwind gradients. It is clamped to `[−1, 1]` in the predictor stage only, and nothing in the source reinitializes it.
  - The time step is `TARGET_CFL (0.4) · Δx / max(|u_x|, |u_y|)`, capped at 600 s. It is first adapted after time step 5; before that the initial `SIMULATION_DT = 5 s` is used.
  - Elliptical spread uses Anderson's length-to-breadth formula with coefficients 0.1147/0.0692 for wind in mph. These equal the commonly quoted 0.2566/0.1548 divided by 2.2369, the mph-per-m/s factor (derived).
- **FDS background pressure per zone.** FDS (`firemodels/fds@272b8dd9`) evolves a background pressure per zone with `dp̄/dt = (DSUM − USUM)/PSUM` (`divg.f90:1516–1518`).
  - For an adiabatic sealed compartment with ideal gas at constant γ, this reduces to `dp̄/dt = (γ − 1)·Q̇/V`: 800 Pa s⁻¹ for 100 kW in 50 m³ (derived, not run).
  - The pressure–velocity iteration stops after `MAX_PRESSURE_ITERATIONS = 10` even if the tolerances are not met, and raises no error. The step continues unconverged.
  - The time step shrinks when CFL ≥ 1.0 or VN ≥ 1.0 and grows by 10 % when CFL ≤ 0.8. The default simulation mode, VLES, uses the L2 velocity norm plus `|∇·u|`; FDS switches to the L1 norm when the cell aspect ratio exceeds 3.99.
- **FDS on D*/δx.** The pinned User's Guide defines `D*/δx` but states that taking any validation value as an "acceptable" minimum is inappropriate. The widely quoted "4–16" range is not endorsed by the pinned text.
- **FLEXPART well-mixed formulation.** FLEXPART's `advance.f90` (`flexpart/flexpart@3d7eebf7`, a 2019 snapshot) uses a Langevin update with Thomson-type drift `dσw/dz` and a Stohl–Thomson density correction, with perfect reflection at the ground and at the mixing height.
  - The shipped default `CTL = −5` turns off the Lagrangian-time-scale step. The vertical Langevin step then equals the synchronization interval, `LSYNCTIME = 900 s`, using the exponential update.
  - In a toy 1-D model built on the same update (not FLEXPART), dropping the drift term gave 2.2× excess concentration in the low-turbulence surface layer. With the drift term, the excess grew from 1.01× at dt/TL = 0.05 to 1.54× at dt/TL = 1 and 1.97× at dt/TL = 2.
- **WindNinja's mass-consistent solver** (`firelab/windninja@38fc7ca2`) stops conjugate-gradient iterations at an *absolute* residual 2-norm of 0.1, with a cap of 100,000 iterations. If CG fails it falls back to MINRES, and if neither converges it throws.

## Applicability

**Subjects and relationship.** This is a comparative report on four independent codes, one per regime, plus the method papers they implement or cite.

| Subject | Pinned revision (commit date) | Regime | How examined |
| --- | --- | --- | --- |
| `lautenberger/elmfire` | `f4927b7ce68cb74eb0eb117085cc920782c8644e` (2026-10-22) | Rothermel surface spread, Eulerian level set | source + `ELMFIRE_VnV_Suite` registry and README |
| `firemodels/fds` | `272b8dd9fbbb1ce8dbcf8a537863bb3d29f08a2b` (2026-11-19) | Low-Mach LES of fire, pressure zones | source + in-repository User's Guide and Technical Reference Guide LaTeX at the same revision |
| `firelab/windninja` | `38fc7ca2650f9665cf62e00984880705fe3ddd55` (2026-10-29) | Mass-consistent terrain wind | source (`src/ninja/ninja.cpp`) |
| `flexpart/flexpart` | `3d7eebf7c4909f59db5ec32c524f88fb846e9fe5` (2019-11-14) | Lagrangian particle dispersion | source (`src/*.f90`, `options/COMMAND`) |

The `flexpart/flexpart` GitHub repository's HEAD is a 2019 commit whose README calls it "the development version". FLEXPART version 11 (Bakels et al. 2024, doi:10.5194/gmd-17-7595-2024) post-dates it and was **not examined**. Findings apply to the pinned snapshot only; the FLEXPART 10.4 description (Pisso et al. 2019) is the closest published reference.

**Scope.**

- No upstream code in this report was compiled or executed. FDS needs MPI and FLEXPART needs GRIB libraries and meteorological input; ELMFIRE and WindNinja were also not built.
- Execution evidence comes from two kinds of probe, each labelled in place:
  - a toy 1-D Lagrangian stochastic model, explicitly *not* FLEXPART;
  - derived arithmetic on formulas quoted from source.
- Probe host: x86-64 Linux VM, Intel Xeon @ 2.60 GHz, 96 vCPU, 236 GiB RAM, Python 3.13.15, NumPy 2.3.5.
- AERMOD, HYSPLIT and FARSITE source code was not examined. None of the three is published in an official GitHub repository at a pinnable revision. Statements about them are documentation-level and are marked as such.

## Findings

### 1. Rothermel surface spread in ELMFIRE

#### 1.1 The kernel

`ROTHERMEL_SURFACE_SPREAD_RATE` (`elmfire_spread_rate.f90:13–145`) evaluates, per node:

```fortran
ILH = MAX(MIN(NINT(100.*M(5)),120),30)                 ! :66  live-herb moisture index, 1 % bins
FMT = FUEL_MODEL_TABLE_2D(C%IFBFM,ILH)                 ! :67
MEX_LIVE = FMT%MEX_LIVE*(1.-FMT%R_MPRIMEDENOME14SUM_MEX_DEAD*SUM_MPRIMENUMER) - 0.226  ! :71
MEX_LIVE = MAX(MEX_LIVE, FMT%MEX_DEAD)                 ! :72
QIG(:) = 250. + 1116.*M(:)                             ! :79  heat of pre-ignition (Btu/lb)
ETAM_DEAD = 1.0 - 2.59*MOMEX + 5.11*MOMEX2 - 3.52*MOMEX3 ; ETAM_DEAD = MAX(0.,MIN(ETAM_DEAD,1.))  ! :94-95
IR = IR_DEAD + IR_LIVE                                 ! :106 reaction intensity (Btu ft^-2 min^-1)
!   WS_LIMIT = 96.8*C%IR**0.3333333 !Andrews, Cruz, and Rothermel (2013) limit
WS_LIMIT = 0.9*C%IR !Original limit                    ! :108-109
WSMF_LIMITED = MIN(C%WSMF, WS_LIMIT)                   ! :110
PHIW_SURFACE = FMT%PHIWTERM * WSMF_LIMITED**FMT%B_COEFF                 ! :112
PHIS_MAX = FMT%PHIWTERM * WS_LIMIT**FMT%B_COEFF ; PHIS = MIN(FMT%PHISTERM*TANSLP2, PHIS_MAX)  ! :115-116
VS0 = (ADJ + PERTURB_ADJ)*DIURNAL_ADJUSTMENT_FACTOR*IR*FMT%XI/RHOBEPSQIG   ! :132 no-wind no-slope ROS (ft/min)
VELOCITY_DMS_SURFACE = VS0*(1.0 + PHIS + PHIW)         ! :134
```

The fuel-model coefficients are set in `elmfire_init.f90:1368–1383`:

- `B = 0.02526·σ^0.54`
- `φs = 5.275·β^−0.3·tan²θ`
- `φw = C·(β/βop)^−E·U^B`

These are Rothermel's (1972) forms as commonly stated (derived; the 1972 report itself was not re-read).

Basis: source.

#### 1.2 Extinction behaviour

`fire_derived.py` evaluates the damping polynomial (Basis: derived):

| r = M/Mx | 0 | 0.25 | 0.5 | 0.75 | 0.9 | 0.95 | 1.0 | > 1 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| η_M | 1.0000 | 0.6169 | 0.5425 | 0.4469 | 0.2420 | 0.1333 | 0.0000 | 0 (clamped) |

The derivative `−2.59 + 10.22r − 10.56r²` has discriminant −4.95 < 0, so `η_M` is strictly decreasing. At `r = 1` the derivative is −2.93, against 0 in the clamped region beyond.

Dead-fuel reaction intensity, and therefore `VS0` (proportional to `IR`), falls to zero **continuously** at extinction, with a finite-slope kink. A model built on this kernel does not have a value discontinuity at `M = Mx_dead`. Spread can still jump discontinuously across the burn/no-burn boundary through other inputs:

- **Live extinction moisture.** `MEX_LIVE` depends on dead moisture and is floored at `MEX_DEAD`.
- **Live-herb moisture binning.** `ILH = NINT(100·M_live_herb)` selects a different row of the 2-D fuel table at each 1 % step. For dynamic fuel models, the herbaceous load transfer and all derived coefficients are therefore piecewise constant in live moisture.

Basis: source + derived.

#### 1.3 Wind and slope limits

| IR (Btu ft⁻² min⁻¹) | active `0.9·IR` (ft/min, mph) | commented-out `96.8·IR^(1/3)` (ft/min, mph) |
| --- | --- | --- |
| 200 | 180 (2.05) | 566 (6.43) |
| 500 | 450 (5.11) | 768 (8.73) |
| 1115.5 | 1004 (11.41) | 1004 (11.41) |
| 2000 | 1800 (20.45) | 1220 (13.86) |
| 5000 | 4500 (51.14) | 1655 (18.81) |

Basis: derived.

- **Low intensity.** Below 1115 Btu ft⁻² min⁻¹ (211 kW m⁻²), the active limit caps midflame wind *more* severely than the 2013 limit. For example, at `IR = 200` the cap is 2 mph against 6.4 mph.
- **High intensity.** Above it, the active limit allows larger wind factors.
- **Slope cap.** Capping the slope factor at the wind factor evaluated at `WS_LIMIT` (`:115–116`) is an ELMFIRE design choice stated in a comment ("Max slope factor is equal to max wind factor"). It is not part of the Rothermel (1972) equations.
- **Effective wind.** The effective wind used for ellipse shape is limited again to `0.9·IR` when crown fire is off or below critical intensity (`elmfire_level_set.f90:2414`).

The Andrews, Cruz & Rothermel (2013) paper examines the wind-speed limit function. This report verified its bibliographic metadata but did not re-read its recommendations; the commented-out expression is ELMFIRE's attribution.

#### 1.4 Wind–slope vector combination, ellipse shape, and a back-spread discontinuity

`UX_AND_UY_ELLIPTICAL` (`elmfire_level_set.f90:2332–2562`) works in four steps:

- **Vector sum.** It adds slope and wind factors as vectors: `PHIX = PHISX + APHIW·sin(WD − 180°)` and `PHIY = PHISY + APHIW·cos(WD − 180°)`.
- **Head spread.** It sets `VELOCITY_DMS = VS0·(ACCELERATION_FACTOR + |φ|)` (`:2386–2401`).
- **Ellipse shape.** It computes the length-to-breadth ratio:

```fortran
WSMFEFF = WSMFEFF_COEFF * PHIMAG**B_COEFF_INVERSE                        ! :2413 effective midflame wind (ft/min)
LOW = MIN(0.936*EXP(0.1147*WSMFEFF*WSMFEFF_LOW_MULT) + 0.461*EXP(-0.0692*WSMFEFF*WSMFEFF_LOW_MULT) - 0.397, MAX_LOW)  ! :2415
IF (LOW > 0.999 .AND. LOW < 1.001) THEN ; BOH = 1.0                      ! :2418-2419
ELSE ; BOH = (LOW - SQRT(LOW*LOW-1)) / (LOW + SQRT(LOW*LOW-1)) ; ENDIF   ! :2421-2422
VBACK = BOH * VELOCITY_DMS                                               ! :2424
```

  The defaults are `WSMFEFF_LOW_MULT = 60.0/5280.0` (ft/min → mph) and `MAX_LOW = 8.0` (`elmfire_namelists.f90:826, 805`).
- **Normal velocity.** It maps the elliptical template onto the local front normal (`COMPUTE_SPREAD_VELOCITIES`, `:2518–2538`). The along-axis term is `A²cosθ/√(A²cos²θ + B²sin²θ) + (V_head − V_back)/2`, with `A = (V_head + V_back)/2` and `B = A/LOW`. The result is projected onto the horizontal through the slope-aspect factors `UXOUSX`/`UYOUSY`.

Derived consequences:

- **Coefficients.** `0.2566/2.23694 = 0.11471` and `0.1548/2.23694 = 0.06920`. ELMFIRE's coefficients therefore equal the commonly quoted Anderson (1983) coefficients rescaled from m/s to mph, consistent with its mph conversion. The unit of the original publication was not checked against its primary text.
- **Back-spread discontinuity.** `BOH(1.001) = 0.9144` from the formula, but `BOH = 1.0` inside `(0.999, 1.001)`, so the back-spread rate drops by 8.6 % of the head rate at `LOW = 1.001`. With `dLOW/dU|₀ = 0.07546 mph⁻¹`, this happens at `U ≈ 0.0133 mph` (1.2 ft/min). The jump is real but sits at practically calm wind.

| U (mph) | 0 | 2 | 5 | 10 | ≥ 20 |
| --- | --- | --- | --- | --- | --- |
| LOW | 1.000 | 1.182 | 1.590 | 2.781 | 8.0 (cap) |

Basis: source + derived.

#### 1.5 Upstream verification and validation inventory

`ELMFIRE_VnV_Suite/cases/Verification/CASE_REGISTRY.md` assigns stable identifiers to verification cases (`CASE01`–`CASE49`). Those that bear on this section include:

- `CASE15_CRO`: constant rate of spread.
- `CASE16_NSP`: no-spread limiting behaviour.
- `CASE17_SCV`: spatial convergence.
- `CASE18_TCV`: temporal convergence.
- `CASE21_WDE`: wind-driven elliptical spread.
- `CASE32_RCV`: raster-orientation covariance under a 90° rotation.
- `CASE33_SDO`: slope-driven directional spread.
- `CASE34_FMS`: standard fuel-model Rothermel sweep.
- `CASE35_WSS`: midflame wind response and limiting.
- `CASE36_SLS`: slope-factor response and limiting.
- `CASE37_DMS`: dead-fuel moisture damping and extinction.
- `CASE38_LMS`: static live-fuel damping.
- `CASE39_DHC`: dynamic herbaceous curing.
- `CASE40_WSD`: wind–slope vector addition.

Validation cases are `cases/Validation/landscape_scale/{camp_fire, thomas_fire, tubbs_fire}`. Compiled reports are committed as `main_report/verification_report.pdf` (10,913,978 B) and `validation_report.pdf` (1,714,934 B). Their contents, tolerances and pass/fail status were **not examined**.

Basis: documentation.

### 2. Front propagation: ELMFIRE level set versus marker/Huygens methods

#### 2.1 ELMFIRE level-set mechanics

| Element | ELMFIRE implementation | Location |
| --- | --- | --- |
| Equation | `∂φ/∂t + u_x ∂φ/∂x + u_y ∂φ/∂y = 0` with `(u_x, u_y)` from the elliptical template applied at the front normal | `RK2_INTEGRATE`, `elmfire_level_set.f90:2566–2608` |
| Time integration | two-stage RK2: predictor `φ* = φⁿ − Δt·(u·∇φ)`, corrector `φⁿ⁺¹ = ½(φⁿ + φ* − Δt·(u·∇φ*))` | `:2584`, `:2597` |
| Spatial gradient | upwind faces with a "half Superbee" limiter `max(0, max(min(R/2, 1), min(R, 1/2)))` | `HALF_SUPERBEE`, `:2143–2153`; `LIMIT_GRADIENTS`, `:2665–2746` |
| Normal | central differences, each component clamped to ±3e4, normalized by `max(|∇φ|, 1e-30)` | `CALC_NORMAL_VECTORS`, `:2302–2328` |
| Reinitialization | **none**. The predictor clamps `φ ∈ [−1, 1]` and resets NaN to 1; the corrector does not clamp. No reinitialization routine appears anywhere in `build/source/*.f90` | `:2585–2587` |
| Time step | after time step 5: `Δt = min(TARGET_CFL·Δt/CFL, SIMULATION_DTMAX)`, `CFL = max_nodes max(|u_x|, |u_y|)·Δt/Δx`; defaults `TARGET_CFL = 0.4`, `SIMULATION_DTMAX = 600 s`, initial `SIMULATION_DT = 5 s` | `CFL_AND_FLUX_LIMITER`, `:2612–2662`; `elmfire_namelists.f90:578–584` |
| Narrow band | tagged-cell lists with `BANDTHICKNESS = 2` | `elmfire_namelists.f90:796` |

Basis: source.

Consequences (derived):

- **Clamping in place of reinitialization.** Clamping replaces signed-distance reinitialization. Away from the front, `φ` saturates at ±1, so `|∇φ|` is not 1. Only the zero contour and the normal direction (normalized) matter for the spread velocity, which is why the scheme does not need a distance function. The price is that gradient-ratio limiting near saturated regions sees flattened data.
- **CFL norm.** The CFL estimate uses `max(|u_x|, |u_y|)` rather than `|u_x| + |u_y|`. For a dimension-by-dimension explicit upwind update, the sum is the textbook stability measure. `TARGET_CFL = 0.4` keeps `(|u_x| + |u_y|)Δt/Δx ≤ 0.8` for any direction.
- **Unadapted first steps.** The first five steps use the unadapted initial step.
- **Upstream note.** A comment at `:2466` records that the `IF (.NOT. C%BURNED)` guard "is not functioning", because `C%BURNED` is assigned only to `LIST_BURNED` nodes.

#### 2.2 Comparison with marker (Huygens) propagation

FARSITE (Finney 1998) propagates the perimeter as vertices expanded by elliptical wavelets, following Huygens' principle. Its code was **not examined**. The comparison below is therefore derived from the propagation mechanics, not from measured differences.

| Property | Eulerian level set (ELMFIRE) | Lagrangian markers (FARSITE-type) |
| --- | --- | --- |
| Front merging and holes | Automatic: topology is implicit in `φ`'s sign | Needs explicit detection of self-intersections and loop clipping |
| Resolution control | Raster `Δx`; numerical diffusion set by the limiter | Vertex spacing; needs re-insertion and removal of vertices |
| Anisotropy and grid bias | Raster orientation can bias spread (tested by `CASE32_RCV`) | Grid-free, but sensitive to vertex density on high-curvature fronts |
| Time step | CFL on the raster (`TARGET_CFL = 0.4`) | Bounded by perimeter-resolution and distance-check criteria (not examined) |
| Cost driver | Number of tagged narrow-band cells | Number of vertices and intersection tests |

Basis: derived. Raster-orientation covariance results from `CASE32_RCV` were not read.

### 3. Terrain wind input: WindNinja's mass-consistent solver

`ninja.cpp` solves the variational mass-consistency equation (comment at `:1512–1526`):

```text
∂/∂x(Rx ∂Φ/∂x) + ∂/∂y(Ry ∂Φ/∂y) + ∂/∂z(Rz ∂Φ/∂z) + H = 0,
Rx = Ry = 1/(2 αH²),  Rz = 1/(2 αV²),  H = ∂u0/∂x + ∂v0/∂y + ∂w0/∂z
```

The solver settings are:

- `alphaH = 1.0` (`:40`). The vertical modulus is `alphaV = alphaH/alphaStability`, or `alphaV = alphaH` when stability is off (`:1696–1784`).
- `MAXITS = 100000` and `stop_tol = 1E-1`, described in the source as the "2-norm of residual" (`:285–286`).
- The preconditioned CG solver uses SSOR, falling back to Jacobi if SSOR initialization fails (`:676–737`). If CG returns false, MINRES is tried (`:448–450`). If MINRES also fails, `"Solution did not converge.\nMAXITS reached."` is thrown (`:853–855`).

The stopping criterion is an absolute residual norm, not one relative to the right-hand side. Its meaning therefore changes with mesh size and wind magnitude (derived). Forthofer, Butler & Wagenbrenner (2014) compare mass-consistent and CFD approaches against measurements; this report verified the paper's metadata only. ELMFIRE consumes gridded wind fields; the coupling path from WindNinja output to ELMFIRE input was not examined.

Basis: source.

### 4. NIST FDS: low-Mach pressure zones, pressure iteration, and time-step control

#### 4.1 Background pressure per zone

FDS splits pressure into a background `p̄_m(z, t)`, one per pressure zone `m`, and a perturbation (Technical Reference Guide, `Equation_Chapter.tex:166–169`). The guide notes that compartments connected by HVAC "can each maintain individual background pressures".

`DIVERGENCE_PART_2` (`divg.f90:1429–1636`) works as follows:

- **Connected zones.** It equalizes connected zones by adding a relaxation volume flow, with `PRESSURE_RELAX_TIME = 1 s` (`cons.f90:661`; `divg.f90:1470–1505`). A zone connected to the exterior relaxes toward `P_0`.
- **Zone pressure rate.** It updates each zone's pressure:

```fortran
IF (ABS(PSUM(IPZ)) > TWENTY_EPSILON_EB) D_PBAR_DT_P(IPZ) = (DSUM(IPZ) - USUM(IPZ))/PSUM(IPZ)   ! :1517
DP(I,J,K) = DP(I,J,K) - (R_PBAR(K,IPZ)-RTRM(I,J,K))*D_PBAR_DT_P(IPZ)                      ! :1538
```

  `DSUM` is the zone integral of the thermodynamic divergence (`Σ VC·DP`). `PSUM` is the compressibility integral `Σ VC·(1/p̄ − RTRM)`. `USUM` is the net normal velocity times area summed over solid-boundary wall cells and cut faces of the zone. All three are accumulated in `DIVERGENCE_PART_1` (`divg.f90:723–776`).
- **Merging.** Zones merge when obstructions are created or removed (`MERGE_PRESSURE_ZONES`, `:1293–1319`).

Derived limit (not run): consider one sealed zone (`USUM = 0`) of ideal gas with constant γ, adiabatic walls, and total heat release `Q̇`.

- The source computes `RTRM = 1/(ρ c_p T)`. With `CONSTANT_SPECIFIC_HEAT_RATIO` this is set to `(γ−1)/γ · 1/p̄` (`divg.f90:602–612`), so `PSUM = V/(γ p̄)`.
- If heat release is the only contribution to the divergence, then `DSUM = (γ−1)Q̇/(γ p̄)`.
- Together these give `dp̄/dt = (γ − 1)·Q̇/V`.

| Q̇ (kW) | V (m³) | dp̄/dt (Pa/s, γ = 1.4) | time to +1 kPa (s) |
| --- | --- | --- | --- |
| 100 | 50 | 800 | 1.25 |
| 500 | 50 | 4000 | 0.25 |
| 1000 | 500 | 800 | 1.25 |

This is an upper bound: wall heat loss, leakage (`LEAK`/HVAC) and radiation out of the zone reduce it. It shows why sealed-compartment FDS runs are sensitive to leakage specification.

Basis: source + documentation + derived.

#### 4.2 Pressure–velocity iteration

`PRESSURE_ITERATION_LOOP` (`main.f90:1513–1634`) exits on any of the following:

- Both `PRESSURE_ERROR_MAX < PRESSURE_TOLERANCE` and `VELOCITY_ERROR_MAX < VELOCITY_TOLERANCE` (`:1620`).
- The iteration count reaches `MAX_PRESSURE_ITERATIONS` in the corrector, or `MAX_PREDICTOR_PRESSURE_ITERATIONS` in the predictor (`:1617–1618`).
- `SUSPEND_PRESSURE_ITERATIONS` is set, the cycle is past 10 and the iteration past 3, and the errors fall by less than `ITERATION_SUSPEND_FACTOR = 0.95` (`:1626–1629`).

Defaults (`cons.f90:522–532`, `read.f90:10037–10043, 10079`):

| Parameter | Default |
| --- | --- |
| `MAX_PRESSURE_ITERATIONS` | 10 |
| `MAX_PREDICTOR_PRESSURE_ITERATIONS` | −1, which means the same as the corrector |
| `VELOCITY_TOLERANCE` | 0, which means `0.5·CHARACTERISTIC_CELL_SIZE` |
| `PRESSURE_TOLERANCE` | 0, which means `20/min(1, CHARACTERISTIC_CELL_SIZE)²` |
| `SUSPEND_PRESSURE_ITERATIONS` | `.FALSE.` |
| `ITERATE_PRESSURE` | false only if `VELOCITY_TOLERANCE > 100` |

Reaching the iteration cap is not an error; the time step proceeds with the remaining normal-velocity error at solid and mesh boundaries. Per-step errors and locations are written as diagnostics. The *acceptability* of a run therefore rests on the user checking those diagnostics.

Basis: source.

#### 4.3 Time-step control

`CHECK_STABILITY` (`velo.f90:3027–3207`) computes the following:

- **CFL.** `CFL = Δt·max_cells(UVW)`, where `UVW` is `max(|u|/δx, |v|/δy, |w|/δz)` for norm 0, the sum for norm 1, or the L2 norm for norm 2, plus `|∇·u|` in each case (`:3065–3069`).
- **Von Neumann.** `VN` is the von Neumann number from the maximum effective viscosity.
- **Particles.** A particle CFL.
- **Decision** (`:3184–3199`):
  - If `CFL < CFL_MAX`, `VN < VN_MAX` and particle CFL < max (or the step is locked), the step is kept. If additionally `CFL ≤ CFL_MIN` and `VN < VN_MIN`, it grows to `1.1·Δt`, or `min(1.1·Δt, DT_INITIAL)` with `RESTRICT_TIME_STEP`.
  - Otherwise `Δt_new = 0.9·min(CFL_MAX/UVW, VN_MAX/(2·Σ1/δx²·ν), PARTICLE_CFL_MAX/u_p, DT_CLIP)`, and the step is redone (`main.f90:679–812`).

| Mode (`SIMULATION_MODE`) | `CFL_MAX/MIN` | `VN_MAX/MIN` | Velocity norm | Flux limiter |
| --- | --- | --- | --- | --- |
| `VLES` (default, `read.f90:1779`) | 1.0 / 0.8 | 1.0 / 0.8 | L2 (2) | Superbee |
| `LES` | 1.0 / 0.8 | 0.8 / 0.6 | L1 (1) | CHARM |
| `DNS` | 0.5 / 0.4 | 0.5 / 0.4 | L1 (1) | CHARM |
| `SVLES` | 1.0 / 0.8 | 1.0 / 0.8 | L2 (2) | Superbee |

Sources: `cons.f90:337–340` and `read.f90:1852–1885`. Additionally, `main.f90:141` sets `CFL_VELOCITY_NORM = 1` when the maximum cell aspect ratio exceeds 3.99 and the user did not specify a norm. The User's Guide motivates this with "beyond an aspect ratio of about 4:1 … required to avoid unphysical oscillations in the ambient temperature" (`FDS_User_Guide.tex:9025`).

The solution-procedure summary in the pinned Technical Reference Guide (`Time_Chapter.tex`) states the CFL check in max-norm form, which is the norm-0 case. The User's Guide table (`FDS_User_Guide.tex:8927, 8997–9005`) documents the norms as implemented.

Basis: source + documentation.

#### 4.4 Combustion mixing time and plume resolution

The default (non-DNS) mixing time is `τ_mix = max(τ_min, min(τ_d, τ_u, τ_g, τ_flame))`, where:

- `τ_min = max(TAU_CHEM = 1e-5 s, Δ/TURBULENT_FLAME_SPEED)`, with a flame speed of 100 m/s;
- `TAU_FLAME = 1e10 s`;
- the diffusive, SGS-turbulent and buoyant scales are `τ_d = Δ²/D_F`, `τ_u = C_U·Δ/√(2k_sgs/3)` and `τ_g = √(2Δ/g)`.

Sources: `fire.f90:930–946` and `cons.f90:347–349`. The source comments cite "FDS Tech Guide (5.13)–(5.16)".

Plume resolution is characterized by `D*/δx`, with `D* = (Q̇/(ρ∞ c_p T∞ √g))^(2/5)` (`FDS_User_Guide.tex:1157–1161`). The pinned User's Guide then states (`:1163`) that the Validation Guide's `D*/δx` values "range over two orders of magnitude and were chosen based on a grid resolution study … Taking any of these values as an 'acceptable' minimum is inappropriate."

Derived cell sizes (`ρ∞ c_p T∞ √g = 1111 kW m⁻⁵ᐟ²`; the `D*/δx` values 4 and 16 are shown only because the range is widely quoted, not as guidance):

| Q̇ (kW) | D* (m) | δx at D*/δx = 4 | δx at D*/δx = 16 | cells per m³ at 16 |
| --- | --- | --- | --- | --- |
| 100 | 0.382 | 0.095 m | 0.024 m | 73,658 |
| 1000 | 0.959 | 0.240 m | 0.060 m | 4,648 |
| 5000 | 1.825 | 0.456 m | 0.114 m | 674 |

Cell count scales as `(D*/δx)³`, so quadrupling resolution multiplies cells by 64. With CFL time stepping, cost scales as `(D*/δx)⁴` (derived).

Basis: source + documentation + derived.

### 5. Atmospheric dispersion: Gaussian plume versus Lagrangian particles

#### 5.1 Gaussian steady-state assumptions (AERMOD; documentation level)

The steady Gaussian plume centreline concentration scales as `Q/(u σy σz)`. At fixed σ it diverges as `u → 0`: halving `u` doubles `C` (derived). AERMOD (Cimorelli et al. 2005, Part I; Perry et al. 2005, Part II on 17 field databases; metadata verified) is a steady-state model.

U.S. EPA guidance, retrieved through a web search summary and not read in primary form here, states that AERMOD does not calculate concentrations for calm or missing hours. It describes a calms-processing averaging rule as a regulatory default, and minimum-σv/low-wind options. The AERMOD source code was not examined, so its exact calm threshold and low-wind formulas are **unknown** to this report.

Basis: documentation (secondary) + derived.

#### 5.2 FLEXPART turbulent velocity update

`advance` (`advance.f90:352–512`) updates horizontal turbulent velocities with Ornstein–Uhlenbeck steps:

```fortran
if (dt/tlu.lt..5) then ; up=(1.-dt/tlu)*up+rannumb(nrand)*sigu*sqrt(2.*dt/tlu)            ! :372-373
else ; ru=exp(-dt/tlu) ; up=ru*up+rannumb(nrand)*sigu*sqrt(1.-ru**2) ; endif             ! :375-376
```

For the vertical component, it takes `ifine` sub-steps `dtf = dt/ifine`:

```fortran
! turbswitch = .true., dt/TL < 0.5 (Gaussian turbulence): normalized w/sigw formulation   ! :446-448
wp=((1.-dtftlw)*wp+rannumb(nrand+i)*sqrt(2.*dtftlw)+dtf*(dsigwdz+rhoaux*sigw))*real(icbt)
delz=wp*sigw*dtf
! turbswitch = .false.: Markov chain for w itself                                     ! :458-461
rw=exp(-dtftlw)
wp=(rw*wp+rannumb(nrand+i)*sqrt(1.-rw**2)*sigw+tlw*(1.-rw)*(dsigw2dz+rhoaux*sigw**2))*real(icbt)
delz=wp*dtf
if (abs(delz).gt.h) delz=mod(delz,h)                                                 ! :476
if (delz.lt.-zt) then ; icbt=-1 ; zt=-zt-delz                  ! reflection at ground  :482-484
else if (delz.gt.(h-zt)) then ; icbt=-1 ; zt=-zt-delz+2.*h     ! reflection at h       :485-487
```

- **Drift and density terms.** The `dsigwdz` and `dsigw2dz` terms are the well-mixed drift for inhomogeneous Gaussian turbulence (Thomson 1987). `rhoaux = (dρ/dz)/ρ` is the density correction (Stohl & Thomson 1999).
- **Reflection.** Reflection flips the sign of the velocity on the next update through `icbt = −1`.
- **Skewed CBL option.** With `CBLFLAG = 1` and `−h/L > 5`, a skewed-turbulence routine `cbl` is used instead. It contains a NaN fallback that resamples `wp = σw·ξ` and counts occurrences (`nan_count2`, `:434–441`). The source comment asks the user to "reduce ifine if this number became a non-negligible fraction".
- **Next step.** `ldt = int(min(TL, h/(2|w'σw|), 0.5/|dσw/dz|)·ctl)`, floored at `mintime` (`:504–510`).

Basis: source.

#### 5.3 The shipped default disables the TL-based step

`options/COMMAND` ships with `LSYNCTIME = 900`, `CTL = −5.0` ("uses LSYNCTIME if CTL<0") and `IFINE = 4` ("used only if CTL>1").

`readcommand.f90:244–272, 379–385` then sets:

- `turbswitch = .false.` and `ifine = 1` when `ctl < 0.1`;
- `ctl = 1/ctl`, then `method = 0` and `mintime = lsynctime` for `ctl ≤ 0`.

With `CBLFLAG = 1`, the code forces `ctl ≥ 5` and `ifine·ctl ≥ 50`, with printed warnings. With the shipped options, `ctl = 1/(−5) = −0.2`, so `method = 0`. In the boundary-layer time loop, `method = 0` sets `ldt = abs(lsynctime)` (`advance.f90:283–290`): the turbulent step is the 900 s synchronization interval. The update uses the exponential `w`-form (`:458–461`); it is unconditionally stable, but its drift term is evaluated once per 900 s.

Basis: source.

#### 5.4 Toy-model check of well-mixedness and step sensitivity (not FLEXPART)

`well_mixed_toy.py` uses the §5.2 normalized update in 1-D, with constant density, perfect reflection and the `mod(Δz, h)` fold. Its settings are `h = 1000 m`, `TL = 120 s`, and an inhomogeneous profile `σw(z) = 0.2 + 1.3·(z/h)·√(1 − z/h)` m/s chosen for the toy, which is not a FLEXPART/Hanna profile. It starts 40,000 particles uniformly, runs 3 h, and reports the concentration in the bottom 5 % and top 5 % of the layer relative to uniform (1.0 is well mixed):

| dt/TL | with dσw/dz drift: bottom, top | without drift: bottom, top |
| --- | --- | --- |
| 0.05 | 1.011, 1.022 | 2.182, 1.324 |
| 0.2 | 1.061, 0.998 | 2.273, 1.325 |
| 0.5 (exponential form) | 1.225, 1.002 | 2.457, 1.378 |
| 1.0 | 1.544, 0.975 | 2.797, 1.281 |
| 2.0 | 1.967, 0.929 | 3.001, 0.993 |

Basis: execution (toy model of a Langevin update of the FLEXPART form; 18 s wall). The sampling standard error in a 5 % slab is about ±0.02.

The toy shows two things:

- Without the drift term, particles pile up where σw is small.
- With the drift term, the well-mixed property degrades as dt/TL grows. That is relevant to §5.3, where dt = 900 s can be many TL near the surface.

It does not quantify FLEXPART's actual error. FLEXPART uses Hanna profiles, height-dependent TL, `ifine` sub-steps and the `w`-form at large steps, none of which the toy reproduces.

#### 5.5 Deposition mass accounting in FLEXPART

- **Dry deposition.** Dry deposition probability accumulates as `prob = 1 + (prob − 1)·exp(−v_d·|dt|/(2·href))` for particles below `2·href` (`advance.f90:582–599`, "correction by Petra Seibert, 10 April 2001"). Per synchronization step, `timemanager.f90:640–650` applies `drydeposit = m·prob·decfact` and `m ← m·(1 − prob)·decfact`. Particle-plus-deposit mass is therefore conserved exactly apart from the decay factor.
- **Wet deposition.** Wet deposition removes `m·(1 − exp(−Λ·|Δt|))·grfraction` and keeps `restmass = m − wetdeposit` (`wetdepo.f90:104–112`). The removed mass is assigned to the deposition grid, so this is also conservative by construction; the behaviour when `restmass ≤ smallnum` was not examined.

Basis: source.

### 6. Comprehensibility (C1) and model refinement (C2)

**C1.**

- **ELMFIRE.** ELMFIRE keeps the Rothermel arithmetic in about 120 lines with inline unit comments. The traps are invisible from inputs:
  - the original-versus-2013 wind limit sits in a comment, not an option;
  - 1 % live-herb binning;
  - the `BOH` window.
- **FDS.** FDS's acceptability conditions are spread across three places: diagnostics (velocity error), defaults (10 iterations), and user-guide prose (D*/δx). Its convergence failure is silent by design.
- **FLEXPART.** FLEXPART's most consequential switch for well-mixedness, the sign of `CTL`, is a one-line option whose comment ("uses LSYNCTIME if CTL<0") does not say that drift is then evaluated once per synchronization interval.

**C2.**

- **ELMFIRE.** ELMFIRE unifies wind and slope as one vector `φ` (a good orthogonal choice). It then re-introduces special cases: a slope cap tied to the wind limit, a crown-fire `MAX(φw_surface, φw_crown)` switch, and a `LOW ≈ 1` window.
- **FDS.** FDS treats sealed and connected compartments with one zone equation plus a relaxation term. Leaks and HVAC remain separate submodels feeding `USUM`.
- **FLEXPART.** FLEXPART carries three vertical-velocity formulations (normalized Euler, normalized exponential, `w`-exponential) plus the skewed CBL scheme, selected by `turbswitch`, `dt/TL` and `CBLFLAG`. A single exponential-integrator form with drift and density correction would cover the Gaussian cases uniformly (derived suggestion, not evaluated).

### 7. Performance and resource footprint (L1–L6)

| Level | ELMFIRE | FDS | WindNinja | FLEXPART |
| --- | --- | --- | --- | --- |
| L1 authoring | not measured | not measured | not measured | not measured |
| L2 build | not measured | not measured | not measured | not measured |
| L3 setup and compile latency | not measured | not measured | not measured | not measured |
| L4 execution | not measured; time step bounded by `TARGET_CFL = 0.4` and 600 s (source) | not measured; cost ∝ (D*/δx)⁴ (derived) | not measured; up to 100,000 CG iterations (source) | not measured; default turbulent step 900 s (source) |
| L5 certificate checking | not applicable | not applicable | not applicable | not applicable |
| L6 footprint | committed VnV PDFs 10.9 MB and 1.7 MB; full repository blobs 1,005,676 KiB (git tree listing) | `Source/*.f90` 33 files; `ccib.f90` 932,483 B and `geom.f90` 1,403,748 B are the largest (git tree) | not measured | `src/*.f90` 160 files (git tree) |
| Toy probes (host above) | — | — | — | well-mixed toy 18 s wall; derived scripts < 1 s |

Basis: source (tree listings) + execution (toy timing).

### 8. Validation coverage (V1–V4)

- **V1 (specification adequacy).** ELMFIRE's verification registry includes analytic and limiting-behaviour cases (`CASE15`–`CASE18`, `CASE34`–`CASE38`) that directly target §1.2–1.3. Whether `CASE37_DMS` tests the kink at `Mx`, and whether `CASE35_WSS` tests which wind limit is active, was not checked. FDS ships verification and validation guides built from the same repository; their contents were not read.
- **V2 (differential testing).** `CASE32_RCV` (raster-rotation covariance) is a metamorphic test of level-set grid bias. No cross-code differential test (ELMFIRE versus a marker method; FLEXPART versus HYSPLIT) was performed here.
- **V3 (concurrency and physical).** FDS MPI/OpenMP determinism, ELMFIRE MPI decomposition, and FLEXPART MPI (`*_mpi.f90`) were not examined.
- **V4 (field replay).** ELMFIRE's landscape validation cases are the Camp, Thomas and Tubbs fires; their metrics were not read. ISO 16730-1:2015 sets verification and validation requirements for fire-safety calculation methods; its text (paywalled) was not examined.

## Boundaries

- **Not examined (execution).** No ELMFIRE, FDS, WindNinja or FLEXPART binary was built or run. All behavioural claims are source-, documentation- or derivation-based, except the toy LPDM.
- **Not examined (FLEXPART version).** FLEXPART version 11 and the GitLab-hosted development history after the pinned 2019 GitHub snapshot. Defaults such as `CTL = −5` may differ there.
- **Not examined (other dispersion codes).** HYSPLIT (Stein et al. 2015; metadata only) and AERMOD source code. The AERMOD calm-hour statement in §5.1 rests on a secondary search summary of EPA guidance.
- **Not examined (FARSITE).** FARSITE code. The §2.2 comparison is derived, not measured. An unofficial GitHub copy (`mbedward/farsite`) exists but was not inspected.
- **Unknown (Rothermel 1972).** Whether ELMFIRE's `QIG = 250 + 1116·M`, the `η_M` coefficients, and the `MEX_LIVE` expression match the 1972 report text to the digit. They match the commonly stated forms, but the report was not re-read.
- **Unknown (Andrews et al. 2013).** Whether the 2013 paper recommends replacing the `0.9·IR` limit outright or under conditions. Only its title and metadata were verified.
- **Unknown (FDS unconverged steps).** How often FDS reaches `MAX_PRESSURE_ITERATIONS` in sealed multi-mesh compartments, and with what divergence error. No FDS run was made.
- **Known not to apply.** The sealed-zone rate `(γ − 1)Q̇/V` does not apply to zones with leakage, HVAC, open vents, or significant wall heat loss. It is an adiabatic upper bound.
- **Not established (D*/δx).** This report does not establish that `D*/δx = 4–16` is adequate for any FDS output. The pinned User's Guide explicitly declines to set an acceptable minimum.
- **Not established (toy LPDM).** The toy LPDM's 1.5–2× bottom-layer excess at dt/TL ≥ 1 is not a property of FLEXPART runs.
- **Not examined (ELMFIRE scope).** Spotting (`elmfire_spotting.f90`), suppression, WUI/building spread, CFFDRS, crown-fire models, and ELMFIRE MPI. Also the ELMFIRE VnV PDFs' numerical tolerances.
- **Not examined (WindNinja scope).** WindNinja's OpenFOAM path (`ninjafoam.cpp`), diurnal and stability parameterizations, and the effect of the absolute `stop_tol = 0.1` on wind accuracy.
- **Not examined (NFPA).** NFPA 92 smoke-control requirements.
- **Not measured.** All L1–L4 and L6 quantities for the upstream codes beyond the tree-listing sizes.

## Evidence

**Source pins** (retrieved through the GitHub API and `raw.githubusercontent.com` on 2026-11-20 UTC; each was the default-branch HEAD on that date):

- `lautenberger/elmfire@f4927b7ce68cb74eb0eb117085cc920782c8644e`:
  - `build/source/elmfire_spread_rate.f90` lines 13–145.
  - `build/source/elmfire_level_set.f90` lines 80–85, 404–409, 1094–1098, 2143–2153, 2302–2328, 2332–2562, 2566–2608 and 2612–2749.
  - `build/source/elmfire_namelists.f90` lines 578–584, 796, 805, 810–811 and 825–826, plus `elmfire_init.f90` lines 1368–1383.
  - `ELMFIRE_VnV_Suite/README.md`, `ELMFIRE_VnV_Suite/cases/Verification/CASE_REGISTRY.md`, and the repository tree listing.
- `firemodels/fds@272b8dd9fbbb1ce8dbcf8a537863bb3d29f08a2b`:
  - `Source/divg.f90` lines 598–628, 722–780, 1293–1319 and 1429–1545.
  - `Source/main.f90` lines 141, 619, 679–812 and 1494–1634.
  - `Source/velo.f90` lines 3027–3207, `Source/read.f90` lines 1779, 1840–1905, 9943–9990, 10025–10079 and 5483–5522, `Source/cons.f90` lines 337–353, 424, 522–532 and 661, `Source/fire.f90` lines 891–1004.
  - `Manuals/FDS_User_Guide/FDS_User_Guide.tex` lines 1157–1163, 8927, 8997–9025, plus `Manuals/FDS_Technical_Reference_Guide/Equation_Chapter.tex` lines 166–169 and `Time_Chapter.tex`.
- `firelab/windninja@38fc7ca2650f9665cf62e00984880705fe3ddd55`: `src/ninja/ninja.cpp` lines 40, 280–292, 440–456, 673–862 and 1512–1526, and 1696–1784.
- `flexpart/flexpart@3d7eebf7c4909f59db5ec32c524f88fb846e9fe5`:
  - `src/advance.f90` lines 1–110, 270–300, 352–512, 578–600 and 640–740.
  - `src/readcommand.f90` lines 20–25, 110–120, 240–275 and 375–388, plus `src/timemanager.f90` lines 636–660.
  - `src/wetdepo.f90` lines 100–118, `src/par_mod.f90:112`, `options/COMMAND` lines 17–19 and 35, `README.md`.

**Literature** (metadata verified via the Crossref REST API on 2026-11-20 unless noted):

- Rothermel (1972), USDA FS Res. Pap. INT-115, doi:10.2737/INT-RP-115.
- Andrews, Cruz, Rothermel, Int. J. Wildland Fire 22(7):959–969 (2013), doi:10.1071/WF12122.
- Finney (1998), USDA FS RMRS-RP-4, doi:10.2737/RMRS-RP-4.
- Lautenberger, Fire Safety J. 62:289–298 (2013), doi:10.1016/j.firesaf.2013.08.014.
- McGrattan et al., FDS Technical Reference Guide Volume 1, 6th ed. (2013), doi:10.6028/NIST.SP.1018e6. The DOI `10.6028/NIST.SP.1018` resolves instead to the FDS version 4 technical reference (2006).
- Forthofer, Butler, Wagenbrenner, Int. J. Wildland Fire 23(7):969–981 (2014), doi:10.1071/WF12089.
- Cimorelli et al., J. Appl. Meteor. 44(5):682–693 (2005), doi:10.1175/JAM2227.1.
- Perry et al., J. Appl. Meteor. 44(5):694–708 (2005), doi:10.1175/JAM2228.1.
- Stein et al., Bull. Amer. Meteor. Soc. 96(12):2059–2077 (2015), doi:10.1175/BAMS-D-14-00110.1. The variant `10.1175/BAMS-D-14-0110.1` does not resolve.
- Pisso et al., Geosci. Model Dev. 12:4955–4997 (2019), doi:10.5194/gmd-12-4955-2019.
- Bakels et al., Geosci. Model Dev. 17:7595–7627 (2024), doi:10.5194/gmd-17-7595-2024 (cited only to scope out FLEXPART 11).
- Thomson, J. Fluid Mech. 180:529–556 (1987), doi:10.1017/S0022112087001940.
- Stohl and Thomson, Boundary-Layer Meteorol. 90:155–167 (1999), doi:10.1023/A:1001741110696.
- Anderson's length-to-breadth formula (USDA FS INT-305, 1983) was identified through web search. Its DOI was not confirmed through Crossref, and it is not listed as a subject.

**Derived script `fire_derived.py`** (standard library only; prints every derived number in §1.2–1.4 and §4.4):

```python
import math
eta = lambda r: 1 - 2.59*r + 5.11*r*r - 3.52*r**3
print([round(eta(r), 4) for r in (0, .25, .5, .75, .9, .95, 1.0)], -2.59 + 10.22 - 10.56)
ir_x = (96.8/0.9)**1.5; print(ir_x, ir_x*1.055056/(0.3048**2*60))       # 1115.4 Btu/ft2/min, 211.1 kW/m2
print(0.2566*0.44704, 0.1548*0.44704)                                     # 0.11471, 0.06920
L = 1.001; print((L - math.sqrt(L*L-1))/(L + math.sqrt(L*L-1)))           # 0.9144
print(0.001/(0.936*0.1147 - 0.461*0.0692))                                # 0.0133 mph
den = 1.204*1.005*293.15*math.sqrt(9.81)                                  # 1111.0
for Q in (100, 1000, 5000): D = (Q/den)**0.4; print(Q, D, D/4, D/16, (16/D)**3)
for Q, V in ((100, 50), (500, 50), (1000, 500)): r = 0.4*Q*1e3/V; print(Q, V, r, 1000/r)
```

**Toy LPDM `well_mixed_toy.py`** (NumPy; RNG seed 12345; prints the §5.4 table):

```python
import numpy as np
h, TL = 1000.0, 120.0; rng = np.random.default_rng(12345)
sigw  = lambda z: 0.2 + 1.3*(z/h)*np.sqrt(np.clip(1 - z/h, 0, None))
dsigw = lambda z, e=1e-3: (sigw(np.clip(z+e, 0, h)) - sigw(np.clip(z-e, 0, h)))/(2*e)
def run(dt, drift, n=40000, T=3*3600.0):
    z = rng.uniform(0, h, n); wp = rng.standard_normal(n)
    for _ in range(int(T/dt)):
        s = sigw(z); ds = dsigw(z) if drift else 0.0
        if dt/TL < 0.5: wp = (1 - dt/TL)*wp + rng.standard_normal(n)*np.sqrt(2*dt/TL) + dt*ds
        else: r = np.exp(-dt/TL); wp = r*wp + rng.standard_normal(n)*np.sqrt(1 - r*r) + TL*(1 - r)*ds
        dz = wp*s*dt; dz = np.where(np.abs(dz) > h, np.mod(dz, h), dz); zn = z + dz
        lo, hi = zn < 0, zn > h; zn = np.where(lo, -zn, zn); zn = np.where(hi, 2*h - zn, zn)
        wp = np.where(lo | hi, -wp, wp); z = np.clip(zn, 0, h)
    return np.mean(z < 0.05*h)/0.05, np.mean(z > 0.95*h)/0.05
for ratio in (0.05, 0.2, 0.5, 1.0, 2.0):
    for drift in (True, False): print(ratio, drift, run(ratio*TL, drift))
```

**Observation date.** All evidence was gathered on 2026-11-20 (UTC).

## Revalidation

1. **ELMFIRE.**
   - Diff `ROTHERMEL_SURFACE_SPREAD_RATE` lines 66–134 in a newer revision. In particular, check whether line 108 (the 2013 limit) is uncommented, whether the `ILH` binning changed, and whether the slope cap at lines 115–116 remains.
   - Diff `UX_AND_UY_ELLIPTICAL` lines 2413–2424 for the `LOW` window, `RK2_INTEGRATE` for the ±1 clamp, and `CFL_AND_FLUX_LIMITER` for the CFL norm and the `ITIMESTEP > 5` gate.
   - `grep -rn -i reinit build/source` should stay empty for §2.1 to hold.
2. **FDS.**
   - Check `cons.f90` for `MAX_PRESSURE_ITERATIONS`, `CFL_MAX/MIN` and `VN_MAX/MIN`.
   - Check `read.f90` for the `SIMULATION_MODE` default and per-mode table, `main.f90:141` for the aspect-ratio switch, and `divg.f90` for the `D_PBAR_DT` expression.
   - Re-grep `FDS_User_Guide.tex` for "acceptable'' minimum is inappropriate".
3. **FLEXPART.** Check `options/COMMAND` (`CTL`, `LSYNCTIME`, `IFINE`), `readcommand.f90` (the `turbswitch` and `method` logic) and `advance.f90` lines 446–461 and 476–510. For FLEXPART 11, repeat these checks on that code base; nothing here transfers automatically.
4. **WindNinja.** `grep -n "stop_tol\|MAXITS" src/ninja/ninja.cpp`.
5. **Probes.** Rerun `fire_derived.py`, which is deterministic, and `well_mixed_toy.py` (RNG seed 12345, about 18 s). The toy checks only itself; it is a template for testing a real LPDM's well-mixed behaviour with that model's own σw and TL profiles.
