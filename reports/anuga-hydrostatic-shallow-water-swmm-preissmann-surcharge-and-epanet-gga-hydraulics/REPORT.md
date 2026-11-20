# Well-balanced wet/dry shallow water (ANUGA), EXTRAN versus Preissmann-slot surcharge (EPA SWMM 5.2.4), and EPANET 2.3 gradient-algorithm hydraulics: invariants, regularizations, and measured failure regimes

## Summary

- **ANUGA (anuga_core `44ed9a1f`) gets lake-at-rest and depth positivity from one edge formula, not from separate mechanisms.** Every edge flux first forms `z_half = max(zl, zr)` and `h_side = max(h_edge + z_edge - z_half, 0)`, which is the hydrostatic reconstruction of Audusse et al. (2004). It then applies a Kurganov–Noelle–Petrova central-upwind flux whose mass-diffusion term jumps on `max(stage, z_half)`. Finally it adds a pressure/bed term (`pressuregrad_work`) that cancels exactly for still water whenever the reconstruction keeps the stage uniform. Negative depths that survive the update are clipped by `protect`. The clipping is not conservative: the code computes the added volume, and it warns when the volume added in one time step exceeds `1e-4` of the total domain water volume.
- **ANUGA's Manning friction is semi-implicit, so it can only damp momentum.** The update is `m_new = (m + dt*E) * m / (m - dt*S*m)` with `S <= 0`, which never reverses the sign of `m` at near-zero depth. An explicit update can reverse it. At `h = 1 mm`, `n = 0.03` and `u = 1 m/s`, the explicit factor is `1 + dt*S = -7.8` for `dt = 0.1 s` (derived).
- **ANUGA's documentation and code disagree on the default flow algorithm.** `Domain.__init__` calls `set_flow_algorithm()`, whose default argument is `'DE0'`: first-order Euler, CFL 0.9, β = 0.5, `minimum_allowed_height = 1e-12`. The pinned flow-algorithm guide labels `DE1` the "General-purpose default". The guide also quotes measured penalties for DE0, such as keeping only 66 % of a propagating wave's amplitude.
- **SWMM 5.2.4 surcharge, measured on a 3-conduit test system.** `SURCHARGE_METHOD SLOT` used the Sjöberg slot `w = 0.5423·exp(-(y/D)^2.4)·Wmax` (floored at `0.01·Wmax` above `y/D = 1.78`). At routing steps of 0.5–10 s it gave continuity errors of −0.005 % to −0.016 % and no non-converging steps. At 30 s it failed, with a −1.08 % continuity error and peak conduit flows of 1.02 m³/s against a 0.6 m³/s inflow. `EXTRAN` gave −0.01 % to −0.064 % and transient node-depth spikes to the rim at 0.5–1 s steps, with up to 12 % non-converging steps at 10–30 s.
- **SWMM's variable time step cannot prevent slot instability.** `link_getFroude` returns 0 for a full closed conduit, and the Courant limiter skips links with Fr ≤ 0.01, so the slot's pressure-wave celerity never enters the time step. In the probe, `VARIABLE_STEP 0.75` with a 30 s maximum still produced a −1.10 % continuity error.
- **EPANET 2.3.06 removes the gradient algorithm's zero-flow singularity with a linear head-loss branch.** Below `hgrad < RQTOL`, the code switches to a linear head loss (default `RQTOL = 1e-7` in internal ft/cfs units). The input parser rejects `RQTOL >= 1`.
- **EPANET demand-driven versus pressure-driven analysis, measured in a main-break test.** The demand-driven run reported −2.49 m pressure at the far junction while still delivering its full 10 L/s. The pressure-driven run (Wagner-type, `Pmin = 0`, `Preq = 20 m`, `Pexp = 0.5`) delivered 2.70 L/s at +1.46 m and reported an 11.497 L/s demand deficit.
- **EPANET water-quality reactions are forward Euler per quality step.** EPANET reproduces `(1 + kb·dt)^(T/dt)` to about 1e-5 relative. For `kb = -24 /day` over a 2 h plug-flow pipe, the errors against `exp(kb·T)` are −1.7 % (1 min step), −8.4 % (5 min) and −26 % (15 min). The default segment-merge tolerance (`TOLERANCE 0.01` mg/L) adds a separate ±0.3–0.7 % age-mixing error at slow decay.

## Applicability

**Subjects and their relationship.** This is a comparative report on three independent solvers, one per hydraulic regime. Each is studied at one pinned revision; no code is shared between them.

| Subject | Pinned revision (commit date) | Version string in source | Regime |
| --- | --- | --- | --- |
| `anuga-community/anuga_core` | `44ed9a1ff7c676de0d52c6cce72ab6e35a031245` (2026-11-13) | main branch | 2-D unstructured finite-volume shallow water, wet/dry |
| `USEPA/Stormwater-Management-Model` | `07c371f8a0d477da1d9d4e7c0d75719664f62fec` (2025-02-23) | `VERSION 52004` (`src/solver/consts.h:19`), i.e. 5.2.4 | 1-D link-node dynamic-wave sewer routing with surcharge |
| `OpenWaterAnalytics/EPANET` | `57d8bd8ad60e89b57f2a1ac591f05c8e13589866` (2026-10-26) | `CODEVERSION 20306` (`src/types.h:35`), report banner 2.3.06 | Pressurized network hydraulics (GGA) and Lagrangian water quality |
| `ec-jrc/lisflood-code` | `05a2f58bfd986e33086d52c0947bcff6f452f62b` (2026-09-07) | master branch | Catchment kinematic-wave channel routing, included as a contrast |

The papers listed in `REPORT.json` are the published method definitions these codes implement or cite. Their bibliographic metadata (authors, venue, volume, pages, DOI) was verified through Crossref. Claims about their content are limited to what is stated below and are labelled `derived` where they rest on the standard statement of the method rather than a re-reading of the paper.

**Observation scope.**

- ANUGA was examined by source reading of the C kernels (`anuga/shallow_water/gpu/core_kernels.c` and `gpu_device_helpers.h`), the Python domain and configuration, and the documentation and tests. ANUGA itself was not built or run.
- The ANUGA execution results in this report come from a 1-D re-implementation of the edge formula. This is a toy model, labelled as such wherever it appears.
- EPA SWMM and EPANET were compiled from the pinned sources with `gcc -O2` and run on the inputs reproduced under **Evidence**:
  - SWMM: `src/run/main.c` plus `src/solver/*.c`, built with `-fopenmp`.
  - EPANET: `run/main.c` plus `src/*.c`, plus two small toolkit harnesses.
- Execution host for all measurements: x86-64 Linux VM, Intel Xeon @ 2.60 GHz, 96 vCPU, 236 GiB RAM, gcc 15.2.0 (Debian), Python 3.13.15, NumPy 2.3.5. The host was shared, and wall times varied by up to about 1.8× between repeats.

**Configurations covered.**

- SWMM: dynamic-wave routing only, `INERTIAL_DAMPING PARTIAL`, `NORMAL_FLOW_LIMITED BOTH`, `MAX_TRIALS 8`, `HEAD_TOLERANCE 0.0015 m`, `THREADS 1`, circular conduits, no ponding.
- EPANET: Hazen–Williams and Darcy–Weisbach head loss, single-period demand-driven and pressure-driven runs, first-order bulk decay, no wall reaction, no tanks.

Results are not claimed for other cross-section shapes, ponding, storage nodes, pumps, controls, or tanks except where source reading is cited.

## Findings

### 1. ANUGA discontinuous-elevation (DE) solver

#### 1.1 The edge flux

`core_compute_fluxes_central` (`core_kernels.c:3412–3809`) loops over cells and, for each of the three edges, forms:

```c
// core_kernels.c:3586, 3603-3604, 3609
double z_half  = fmax(zl, zr);                         // max bed at the edge (riverwall may raise it)
double h_left  = fmax(hle + zl - z_half, 0.0);
double h_right = fmax(hre + zr - z_half, 0.0);
if (h_left == 0.0 && h_right == 0.0) { edgeflux = 0 }  // both sides dry after reconstruction
```

It then calls `gpu_flux_function_central`, which the source annotates as the "Kurganov-Noelle-Petrova scheme" (`gpu_device_helpers.h:273`):

```c
// gpu_device_helpers.h:333-364 (rotated frame, s_max >= 0 >= s_min)
if (denom < epsilon) { flux = 0; pressure_flux = 0.5*g*0.5*(h_left^2 + h_right^2); }
flux_0 = (s_max*u_l*h_left - s_min*u_r*h_right
          + s_max*s_min*(max(w_r, z_half) - max(w_l, z_half))) / (s_max - s_min);
flux_1 = (s_max*u_l*uh_l - s_min*u_r*uh_r + local_fr*s_max*s_min*(uh_r - uh_l)) / (s_max - s_min);
pressure_flux = 0.5*g*(s_max*h_left^2 - s_min*h_right^2) / (s_max - s_min);
```

Velocities are computed from the *unreconstructed* edge depth (`u = uh_edge / h_edge` when `h_edge > 0`, else 0) and rescaled by the reconstructed depth: `uh = h_side·u` (`gpu_compute_velocity_terms`, `gpu_device_helpers.h:218–234`). The momentum flux carries no pressure. Pressure enters per cell through the following term (`core_kernels.c:3739–3742`):

```text
pressuregrad_work = L_edge * ( -g/2 * (h_left^2 - hle^2 - (hle + hc)*(zl - zc)) + pressure_flux )
xmom_update -= n_x * pressuregrad_work ;  ymom_update -= n_y * pressuregrad_work
```

The time step is the minimum over full (non-ghost) cells of `radius_k / max_edge_speed_k` (`core_kernels.c:3746–3755`), scaled by the algorithm's CFL factor (`shallow_water_domain.py:6098`).

Basis: source.

#### 1.2 Lake-at-rest (C-property) and dry-neighbour balance

The balance holds for each cell; no global argument is needed (derived from §1.1).

- **Still water, both sides wet** (`w_l = w_r = w`, `u = 0`). The reconstructed depths are equal: `h_left = h_right = w - z_half`. The stage-jump term is `max(w, z_half) - max(w, z_half) = 0`, so the mass flux vanishes. With `s_max = -s_min = c`, `pressure_flux = g/2·(w - z_half)^2`.
- Substituting into `pressuregrad_work` cancels the `h_left^2` and `pressure_flux` terms. What remains is `L·g/2·(hle^2 + (hle + hc)(zl - zc))`.
- If the reconstruction keeps the stage uniform inside a still-water cell (`hle + zl = hc + zc`), then `(hle + hc)(zl - zc) = hc^2 - hle^2`. The bracket reduces to `L·g/2·hc^2`, a per-cell constant. Its normal-weighted sum over the cell's edges vanishes because `Σ n_e L_e = 0` for any closed polygon.
- **Wet cell beside a dry bed** above the water surface: `z_half > w` gives `h_left = h_right = 0`, so the edge carries no flux, and `pressure_flux = 0`. With uniform stage, the bracket again reduces to `L·g/2·hc^2`, so the cell stays balanced.

This argument assumes the edge reconstruction preserves a uniform stage. Whether ANUGA's limiters do so at every wet/dry configuration was not verified (see **Boundaries**).

Among tests found by keyword search, explicit still-water assertions cover the ADER-2 path:

- `test_ader2.py:44–60`: flat bed, `atol = 1e-14`.
- `test_ader2.py:62–76`: bed `z = 0.01x`, uniform stage 1.0, `atol = 1e-10`.

Toy-model check (Basis: execution, toy model of the ANUGA edge formula, not ANUGA): see §1.7.

#### 1.3 Positivity, clipping, and the conservation ledger

| Mechanism | Code | Effect | Conservation |
| --- | --- | --- | --- |
| Reconstruction clamp | `h_side = max(...,0)` (`core_kernels.c:3603–3604`) | No negative depth enters the Riemann solver | Conservative: it alters flux inputs, not stored mass |
| `protect` | `core_protect` (`core_kernels.c:2784–2814`); fused `core_prepare_step_on` (`:2896–2906`) | `h < minimum_allowed_height` ⇒ momentum := 0; `h < 0` ⇒ stage := bed; returns `Σ(-h)·area` | **Adds water** equal to the returned "mass_error" |
| `fix_negative_cells` | `core_kernels.c:2965–2992` | Cells with `stage - bed < 0` and `tri_full_flag > 0` are reset to the bed with zero momentum; returns the count | Adds water |
| `negative_cells_volume` | `core_kernels.c:3005–3025` | Read-only: volume that the clamp will add; must be called after the flux update and before the clamp | Ledger only |
| Warning | `negative_volume_warning_fraction = 1.0e-4` (`config.py:214`); test at `shallow_water_domain.py:6254` (`negative_volume > fraction * total_volume`) | Warns with "possible loss of conservation" when the volume added by clamping in one step exceeds that fraction of the total domain water volume | — |

The cell-based kernel solves every interior Riemann problem twice, once from each side. The source states that "the dual evaluation is only antisymmetric to floating-point roundoff" (`core_kernels.c:3814–3820`). An opt-in edge-based kernel makes the exchange exactly antisymmetric. Mass conservation of the default kernel is therefore exact only up to round-off.

Basis: source.

#### 1.4 Friction stiffness at near-zero depth

Manning friction accumulates `S·m` into a semi-implicit update (`core_kernels.c:3031–3064`), where

```text
S = -g n^2 |q| / h^(7/3)    for h >= minimum_allowed_height and n > 1e-15,   else S = 0.
```

`core_update_conserved_quantities` (`core_kernels.c:2442–2459`) applies it as

```c
num = xmom_c - timestep * xmom_siu[k];
if (xmom_c != 0.0 && num * xmom_c > 0.0) xmom_new = xmom_new * xmom_c / num;   // = (m + dt E) / (1 - dt S)
```

Because `S <= 0`, the denominator satisfies `1 - dt·S >= 1`. The friction factor therefore lies in `(0, 1]`: it cannot reverse the flow, and it does not blow up as `h → minimum_allowed_height`.

Worked example (derived): `h = 1e-3 m`, `u = 1 m/s` (`|q| = 1e-3 m²/s`), `n = 0.03`, `g = 9.8`.

- `h^(7/3) = 1e-7`, so `S = -9.8·9e-4·1e-3/1e-7 = -88.2 s⁻¹`.
- With `dt = 0.1 s`, an explicit update multiplies momentum by `1 + dt·S = -7.82`: the sign reverses and the magnitude grows.
- The semi-implicit factor is `1/(1 + 8.82) = 0.102`.

The legacy explicit kernels `_openmp_manning_friction_flat/sloped` still exist in `sw_domain_openmp.c:236–364`. The comment there says they are "NOT reachable from any non-test production code path".

Basis: source + derived.

#### 1.5 Flow-algorithm settings and a documentation discrepancy

| Algorithm | Setter (`shallow_water_domain.py`) | Time integrator | CFL | β (wet/dry) | `minimum_allowed_height` |
| --- | --- | --- | --- | --- | --- |
| `DE0` | `_set_DE0_defaults` (3792) | forward Euler | 0.9 | 0.5 / 0.0 | 1e-12 |
| `DE1` | `_set_DE1_defaults` (3872) | RK2 | 1.0 | 1.0 / 0.0 | 1e-5 |
| `DE_ader2` | `_set_DE_ader2_defaults` (3933) | ADER-2 Cauchy–Kovalewski predictor | 1.0 | 1.0 / 0.0 | 1e-5 |
| `DE2` | `_set_DE2_defaults` (3988) | SSP-RK3 | 1.0 | 1.0 / 0.0 | 1e-5 |

- `Domain.__init__` calls `self.set_flow_algorithm()` (line 673), and `set_flow_algorithm(self, algorithm: str = 'DE0')` (line 4788) makes DE0 the constructed default. `config.py:140` also sets `flow_algorithm = 'DE0'`.
- The pinned guide `docs/source/setup_anuga_script/flow_algorithms.rst:42` labels DE1 the "General-purpose default — robust and accurate".
- The same guide (lines 75–98) and the DE0/DE_ader2 setter comments quote upstream measurements. These are documentation claims, not reproduced here:
  - DE0 keeps 66 % of a forced wave's amplitude across the `deep_wave` case, against 97 % for DE1.
  - DE0 carries 88 % of the prescribed discharge on `rundown_mild_slope_coarse`.
  - Raising DE0's β to 1.0 makes forward Euler unstable: the stage reaches 25–29 against a forcing of 1.0, and the dry dam break has total variation 112 against the exact 10.0.

Basis: source + documentation.

#### 1.6 LISFLOOD routing as a contrast case

LISFLOOD's channel routing solves a kinematic wave, `A = α Q^β` with `β` read from the `beta` map and the source comment noting `2/3·β = 2/5` (`routing.py:321–343`). Each pixel solves `Q + (α·dx/dt)·Q^β = inflow` by Newton iteration (`kinematic_wave_parallel_tools.py:74–131`, citing Chow et al. 1988 §9.6):

```python
if upstream_inflow <= NEWTON_TOL: discharge[pix] = 0          # NEWTON_TOL = 1e-12
dis = max(dis - error / factor, NEWTON_TOL)                    # positivity by clamping
if dis == NEWTON_TOL: discharge[pix] = 0
```

- With no pressure term, the lake-at-rest/C-property question is **known not to apply**: still water and backwater cannot be represented.
- Positivity is enforced by clamping the Newton iterate. Inflows at or below `1e-12 m³/s` are zeroed, which is a bounded mass sink of at most `1e-12 m³/s` per pixel per sub-step (derived).
- Wet/dry fronts, steep-bed dam breaks, and friction stiffness in the shallow-water sense are outside this model.

Basis: source.

#### 1.7 Toy-model execution of the reconstruction (not ANUGA)

`hr_toy.py` (reproduced under **Evidence**) transcribes the §1.1 formulas to 1-D at first order, with forward Euler, CFL 0.9 and mirrored ghost cells. It compares them against a strawman variant written for this report: no reconstruction, centred pressure flux, and a centred bed-slope source `-g h ∂z/∂x`. That variant is not an upstream scheme.

| Case | ANUGA edge formula (toy) | Strawman (toy) |
| --- | --- | --- |
| Lake at rest, `w = 0.5 m`, steps 0 → 0.3 → 0.1 m, dry island at 0.8 m, 2000 steps | max \|uh\| = 5.4e-16 m²/s; max \|w − w0\| = 2.8e-16 m | max \|uh\| = 0.60 m²/s; max \|w − w0\| = 0.49 m |
| Dry dam break: 2 m water column on a flat bed (x < 20 m) released into a dry flat reach and a dry 1:10 adverse slope rising to a 3 m crest, with a dry 1:10 lee slope beyond; 4000 steps | relative mass change −8.9e-16; clipped volume 0; min h 0 | relative mass change +8.9e-3, all from clipping (clipped/initial = 8.9e-3) |

Basis: execution (toy model of the ANUGA edge formula; Python 3.13.15/NumPy 2.3.5; 2.6 s wall). The toy says nothing about ANUGA's second-order extrapolation, limiters, unstructured meshes, or GPU paths.

### 2. EPA SWMM 5.2.4 surcharge: EXTRAN versus Preissmann slot

#### 2.1 The two mechanisms in code

- **Default.** `project.c:846–847` sets `SurchargeMethod = EXTRAN` and `CrownCutoff = 0.96`. `dynwave_init` (`dynwave.c:159–160`) switches `CrownCutoff` to `SLOT_CROWN_CUTOFF = 0.985257` when SLOT is selected. The other constants are `OMEGA = 0.5`, `DEFAULT_SURFAREA = 12.566 ft²`, `DEFAULT_HEADTOL = 0.005 ft` and `DEFAULT_MAXTRIALS = 8` (`dynwave.c:60–66`).
- **EXTRAN node update** (`setNodeDepth`, `dynwave.c:676–741`):
  - A node is surcharged when `yCrown > 0 && yLast > yCrown`. Ponded nodes do not surcharge; closed storage units surcharge when `surDepth > 0`.
  - When surcharged, the depth update is not storage-based. It is `dy = corr·dQ/Σ(dQ/dH)`, with `corr = 0.6` for upstream terminal nodes, no under-relaxation, and the result clamped to at least `yCrown - FUDGE`.
  - Near the crown, `yLast < 1.25·yCrown`, the denominator is blended with the last free-surface area through `exp(-15·f)`, `f = (yLast − yCrown)/yCrown`.
  - Conduit depths are capped at `yFull` (`dwflow.c:124–129`), and the top width is frozen at `W(0.96·D)` (`dwflow.c:592–605`). For circular pipes that is 0.3919·D from the `W_Circ` table.
- **SLOT** (`getSlotWidth`, `dwflow.c:575–588`):

```c
if (SurchargeMethod != SLOT || xsect_isOpen(xsect->type) || yNorm < CrownCutoff) return 0.0;
if (yNorm > 1.78) return 0.01 * xsect->wMax;
return xsect->wMax * 0.5423 * exp(-pow(yNorm, 2.4));     // "Sjoberg formula"
```

  Above full depth, the flow area is `aFull + (y − yFull)·wSlot` (`dwflow.c:609–619`), so the ordinary storage-based node update continues through surcharge. Depths above `yFull` are allowed only under SLOT.

Basis: source.

#### 2.2 Derived slot geometry

`slot_derived.py` (under **Evidence**) mirrors SWMM's linear lookup of the 51-point `W_Circ` table (`xsect.dat:67–75`, `lookup` in `xsect.c:1474–1499`).

- **Crossing with the table width.** The table width equals the Sjöberg width at `y/D = 0.985242`, which is within 1.5e-5 of `SLOT_CROWN_CUTOFF = 0.985257`. At the cutoff the two widths are 0.20640·D and 0.20661·D, so the switch is width-continuous to 2e-4·D for circular pipes. The upstream rationale for the constant is not stated in the code.
- **Continuity at 1.78.** The Sjöberg formula gives 0.01003·Wmax at `y/D = 1.78`, so the switch to the 0.01·Wmax floor is continuous to 3e-5·Wmax.
- **Slot celerity.** With `c = sqrt(g·A_full/w_slot)` for `D = 0.6 m` and a CFL step of `L/c` for `L = 200 m`:

| y/D | w_slot / D | c (m/s) | L/c (s) |
| --- | --- | --- | --- |
| 0.985 | 0.2066 | 4.73 | 42.3 |
| 1.0 | 0.1995 | 4.81 | 41.6 |
| 1.2 | 0.1152 | 6.33 | 31.6 |
| 1.5 | 0.0385 | 10.96 | 18.2 |
| ≥ 1.78 | 0.0100 | 21.5 | 9.3 |

The floor `w = 0.01·Wmax` caps the slot celerity, here at 21.5 m/s. That is about two orders of magnitude below waterhammer celerity in real pipes, so the slot represents a strongly compliant pipe, not elastic transients (derived).

#### 2.3 The Courant limiter skips surcharged conduits

```c
// link.c:861-864 (link_getFroude)
if ( y <= FUDGE ) return 0.0;
if ( !xsect_isOpen(xsect->type) &&
     xsect->yFull - y <= FUDGE ) return 0.0;      // full closed conduit -> Fr = 0
// dynwave.c:856-861 (getLinkStep): skip links with negligible flow, area or Fr
if ( q <= FUDGE || Conduit[k].a1 <= FUDGE || Link[i].froude <= 0.01 ) continue;
// dynwave.c:903-904 (getNodeStep): skip nodes at or above crown depth
```

For non-skipped links, the step is `t = V/q · (modLength/length) · Fr/(1+Fr) · CourantFactor`, which equals `L/(u + c)` for open-channel celerity `c` (derived). Full closed conduits and surcharged nodes contribute nothing. Under SLOT, the slot celerity of §2.2 therefore never limits `VARIABLE_STEP`.

Basis: source; consequence confirmed in §2.4.

#### 2.4 Measured surcharge behaviour (real SWMM 5.2.4 build)

The system has three 200 m circular conduits (D = 0.6 m, n = 0.013, slope 0.0025, Manning full capacity about 0.31 m³/s, derived), joining junctions J1→J2→J3 (max depth 4 m) to a free outfall. The inflow at J1 is a triangular hydrograph: 0 → 0.6 m³/s at 1 h → 0 at 2 h. The simulation lasts 6 h.

| Method | Step (s) | Continuity error (%) | Flooding (m³) | Max depth J1, J2, J3 (m) | Max depth at report steps (m) | Peak \|Q\| C1, C2, C3 (m³/s) | Avg iterations | Non-converging steps (%) | Instability index |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| EXTRAN | 0.5 | −0.025 | 8 | 4.00, 4.00, 4.00 | 4.00, 2.81, 1.63 | 0.56, 0.56, 0.56 | 2.02 | 0.17 | all stable |
| EXTRAN | 1 | −0.062 | 8 | 4.00, 3.06, 3.08 | 4.00, 2.81, 3.08 | 0.56 ×3 | 2.02 | 0.24 | all stable |
| EXTRAN | 5 | −0.05 | 8 | 4.00, 2.82, 1.63 | 4.00, 2.81, 1.63 | 0.56 ×3 | 2.53 | 0.69 | all stable |
| EXTRAN | 10 | −0.01 | 8 | 4.00, 2.82, 1.63 | same | 0.56 ×3 | 2.72 | 10.83 | all stable |
| EXTRAN | 20 | −0.05 | 8 | 4.00, 2.82, 1.63 | same | 0.56 ×3 | 2.74 | 11.85 | all stable |
| EXTRAN | 30 | −0.064 | 8 | 4.00, 2.82, 1.63 | same | 0.56 ×3 | 2.79 | 12.36 | all stable |
| SLOT | 0.5 | −0.005 | 3 | 4.00, 2.93, 1.79 | 4.00, 2.93, 1.78 | 0.58 ×3 | 2.00 | 0.0 | all stable |
| SLOT | 1 | −0.005 | 3 | same | same | 0.58 ×3 | 2.00 | 0.0 | all stable |
| SLOT | 5 | −0.006 | 3 | same | same | 0.58 ×3 | 2.00 | 0.0 | all stable |
| SLOT | 10 | −0.016 | 3 | same | same | 0.58 ×3 | 2.01 | 0.0 | all stable |
| SLOT | 20 | −0.09 | 3 | 4.00, 2.93, 1.78 | same | 0.58 ×3 | 2.29 | 0.0 | all stable |
| SLOT | 30 | **−1.08** | 35 | 4.00, 4.00, 2.95 | 4.00, 4.00, 2.49 | **0.96, 1.02, 0.62** | 2.79 | 10.56 | C1 14, C2 14, C3 12 |
| EXTRAN | var ≤ 30 (0.75) | −0.089 | 8 | 4.00, 2.81, 1.63 | same | 0.56 ×3 | 2.81 | 12.53 | all stable |
| SLOT | var ≤ 30 (0.75) | **−1.099** | 87 | 4.00, 4.00, 2.28 | 4.00, 3.64, 2.19 | **1.25, 0.81, 0.64** | 2.78 | 9.78 | all stable |

Basis: execution (real SWMM 5.2.4 built from the pinned source; the flooding column converts the report's `10^6 ltr` values to m³).

Interpretation:

- **SLOT at small steps.** At steps of 0.5–5 s, SLOT's continuity error was 5–12× smaller than EXTRAN's. At 10 s the two were comparable (−0.016 % versus −0.010 %). At every step up to 10 s, SLOT also iterated less and showed no intra-report-step spikes. 10 s is roughly the slot CFL step of 9.3 s at the 0.01·Wmax floor.
- **SLOT above the slot CFL step.** At 20 s the error grew to −0.09 %; at 30 s SLOT failed badly, amplifying conduit flow beyond the inflow peak.
- **EXTRAN.** EXTRAN never blew up but produced depth spikes to the rim at J2/J3 inside reporting intervals at 0.5–1 s steps. Its non-convergence rose above 10 % at 10 s and longer steps.
- **Hidden instability.** The VARIABLE_STEP row confirms §2.3. The instability index reports "all links are stable" even though the continuity error is −1.10 % and the C1 peak is 2.1× the inflow, so a stable index is not evidence of a correct surcharge solution.

Basis: execution + derived. This is one system with one hydrograph; the step thresholds scale with conduit length and slot floor and are not universal.

#### 2.5 Relationship to shock-capturing mixed-flow schemes

León et al. (2009) apply Godunov-type schemes to transient mixed (free-surface/pressurized) flows. SWMM's link-node Picard iteration is not a Godunov scheme. It has no Riemann solver at the pressurization front, and its slot celerity is capped by the 0.01·Wmax floor. A report reader should treat the probe's SLOT results as properties of SWMM's discretization, not of the slot concept in general.

Basis: documentation (bibliographic) + source + derived.

### 3. EPANET 2.3.06: gradient algorithm, demand models, status logic, quality

#### 3.1 Zero-flow regularization in `pipecoeff`

```c
// hydcoeffs.c:657-672
q = ABS(hyd->LinkFlow[k]);
hgrad = hyd->Hexp * r * pow(q, hyd->Hexp - 1.0);      // H-W: Hexp = 1.852 -> hgrad -> 0 as q -> 0
if (hgrad < hyd->RQtol) { hgrad = hyd->RQtol / hyd->Hexp; hloss = hgrad * q; }   // linear branch
else hloss = hgrad * q / hyd->Hexp;
...
hyd->P[k] = 1.0 / hgrad;   hyd->Y[k] = hloss / hgrad;   // GGA coefficients
```

- **Defaults.** `RQTOL 1E-7`, `CHECKFREQ 2`, `MAXCHECK 10`, `DAMPLIMIT 0`, `MAXITER 200`, `HACC 0.001` (`input1.c:25–38`). `QZERO = 1.e-6` cfs is used as "equivalent to zero flow" (`hydraul.c:23`).
- **Input validation.** The `[OPTIONS] RQTOL` parser rejects values ≥ 1 with error 213 (`input3.c:2203–2207`).
- **Other closures.**
  - Closed links use `P = 1/CBIG` with `CBIG = 1e8` (`hydcoeffs.c:35, 643–648`).
  - Darcy–Weisbach switches to Hagen–Poiseuille below Re ≈ 2000 (`hydcoeffs.c:712–717`). That branch is linear in `q` and needs no regularization.
  - Emitters use the same RQtol branch (`hydcoeffs.c:525–528`).

Measured, using the full-precision toolkit harness `enquery` on a symmetric loop whose exact cross-pipe flow is 0 (Hazen–Williams, C = 120):

| RQTOL | Trials | Relative error at exit | Cross-pipe flow (L/s) | J2 head (m) |
| --- | --- | --- | --- | --- |
| 1e-12 | 5 | 9.6e-9 | 1.04e-7 | 59.096272338 |
| 1e-7 (default) | 5 | 9.6e-9 | 1.04e-7 | 59.096272338 |
| 1e-3 | 5 | 8.5e-9 | −1.5e-9 | 59.096272330 |
| 1e-1 | 5 | 3.7e-13 | −1.5e-11 | 59.096272330 |
| ≥ 1 | — | parser error 200/213 | — | — |

With a 5 % demand asymmetry (21 vs 20 L/s), every RQTOL < 1 gave 0.4764466 L/s in 4 trials. Darcy–Weisbach runs took 4 trials irrespective of RQTOL.

Basis: execution. On this network the regularization changes only how closely the exact zero is approached (1e-7 versus 1e-11 L/s); it does not change convergence speed. Behaviour on large looped networks with many near-zero pipes was not examined.

#### 3.2 Demand-driven versus pressure-driven delivery under a main break

- **Pressure-driven demand.** It is modelled as an emitter-like head loss: `hloss = Preq·(D/Dfull)^(1/Pexp)` (comment in `demandcoeffs`, `hydcoeffs.c:550–553`).
- **Barriers.** Two smooth barrier functions keep `0 ≤ D ≤ Dfull` (`addlowerbarrier`/`addupperbarrier`, `hydcoeffs.c:69–101`). Each adds `(a ∓ sqrt(a² + 1e-6))/2` with `a = 1e9·dq`.
- **Convergence.** `pdaconverged` (`hydsolver.c`) re-evaluates `q = Dfull·((p − Pmin)/(Preq − Pmin))^Pexp`, clipped to `[0, Dfull]`, and requires `|q − D| ≤ 0.0001 cfs` at every junction. It also accumulates `DeficientNodes` and `DemandReduction`.
- **Defaults.** `DemandModel = DDA`, `Pmin = 0`, `Preq = MINPDIFF`, `Pexp = 0.5` (`input1.c:117–120`).

Measured (`main_break_probe.py`). The network is reservoir 60 m → J1 (el 20) → J2 (el 20) → J3 (el 25), with pipes of 1000 m and 300/250/150 mm diameter (H-W 120). Each junction demands 10 L/s. The break is an emitter at J2 with Ce = 40 L/s/m^0.5.

| Case | J1 p (m) | J2 p (m) | J3 p (m) | J3 delivered (L/s) | J2 total outflow (L/s) | Trials | Report messages |
| --- | --- | --- | --- | --- | --- | --- | --- |
| A: DDA, no break | 39.20 | 38.28 | 30.21 | 10.00 | 10.00 | 2 | — |
| B: DDA, break | 28.83 | 5.57 | **−2.49** | **10.00** | 104.44 (break 94.44) | 6 | `WARNING: Negative pressures` |
| C: PDA, break | 29.18 | 6.73 | 1.46 | **2.70** | 109.58 (break 103.78 + demand 5.80) | 6 | `2 nodes had demands reduced by a total of 57.48%`; flow balance: consumer 18.503, deficit 11.497, emitter 103.782 L/s |
| D: PDA, no break | 39.20 | 38.28 | 30.21 | 10.00 | 10.00 | 2 | — |

Consistency checks (derived):

- Case B break flow: `40·sqrt(5.57) = 94.40` L/s.
- Case C: J2 demand is `10·sqrt(6.73/20) = 5.80`; J3 demand is `10·sqrt(1.46/20) = 2.70`.
- The reported 57.48 % equals `11.497/20`, the deficit relative to the full demand of the two deficient nodes.

The DDA run conserved flow while reporting physically impossible delivery at negative gauge pressure (Wagner et al. 1988 motivate pressure-dependent formulations for this situation). The break also drew about 10 % more under PDA (103.8 vs 94.4 L/s), because reduced customer withdrawal raised the J2 head.

Basis: execution + derived.

#### 3.3 Check-valve and pump status cycling

`hydsolver` (`hydsolver.c:60–213`) iterates as follows:

- Each trial builds and solves `A·H = F`.
- Valve status is checked every trial when `DampLimit = 0`; otherwise only when `relerr ≤ DampLimit`, and then flow changes are relaxed by 0.6.
- Pumps, check valves (CVs) and tank pipes are checked every `CheckFreq` trials until `MaxCheck`.
- After convergence, a full `linkstatus`/`pswitch` pass runs; any status change restarts the iteration.
- If `MaxIter` is exhausted and `ExtraIter > 0`, `ExtraIter` more trials run with statuses frozen. This mechanism exists "in case of status cycling" (`hydsolver.c:110`).

The decision rules (`hydstatus.c`):

- **`cvstatus`.** A CV closes if `dh < −Htol`, or if `q < −Qtol` when `|dh| ≤ Htol`, and opens if `dh > Htol` with `q ≥ −Qtol`. Inside the dead band it keeps its previous status. This hysteresis is what prevents chatter.
- **`pumpstatus`.** A pump goes to `XHEAD` when `dh > Hmax·setting² + Htol`. A constant-horsepower pump with `q < TINY` goes to `TEMPCLOSED`. The comment notes "No check is made to see if flow exceeds pump's max. flow".

Defaults are `HTOL 0.0005 ft` and `QTOL 0.0001 cfs` (`input1.c:27–28`). Status cycling itself was not provoked in a probe.

Basis: source.

#### 3.4 Water-quality transport and reaction discretization

- **Transport.** Transport is Lagrangian, by plug-flow segments (`qualroute.c`). At each quality step `Qstep`, the volume released into a link's upstream end is `|Q|·dt`. It is merged into the last segment if `|c_seg − c| < Ctol` (by volume-weighted averaging), and otherwise starts a new segment (`qualroute.c:323–366`). `Ctol` defaults to `CHEMTOL 0.01` (`input1.c:30`), or `AGETOL 0.01 h` for age.
- **Reaction.** `pipereact` applies forward Euler (`qualreact.c:269–316`):

```c
dcbulk = rbulk * dt;  dcwall = rwall * dt;  cnew = MAX(0.0, c + dcbulk + dcwall);
```

  `bulkrate` handles zero-order, Michaelis–Menten (order < 0), and n-th order kinetics with an optional limiting concentration. It guards `pow(0, <0)`.
- **Mass balance.** The reported mass ratio is `(outflow + final + max(reacted, 0)) / (initial + inflow − min(reacted, 0))` (`quality.c:580–608`). For both Net1 and Net3 at this revision it reads `1.00000`.

Measured with `quality_step_probe.py` (single pipe, D = 300 mm, travel time T = 7200 s, steady 10 L/s, first-order bulk decay):

| kb (1/day) | Quality step | EPANET C/C0, Ctol = 0.01 | EPANET C/C0, Ctol ≤ 1e-4 | `(1+kb·dt)^(T/dt)` | `exp(kb·T)` | Error vs exact (Ctol ≤ 1e-4) |
| --- | --- | --- | --- | --- | --- | --- |
| −1 | 30 s | 0.913995 | 0.920031 | 0.920031 | 0.920044 | −0.0015 % |
| −1 | 5 min | 0.923127 | 0.919911 | 0.919911 | 0.920044 | −0.0145 % |
| −1 | 15 min | 0.919642 | 0.919642 | 0.919642 | 0.920044 | −0.044 % |
| −24 | 1 min | 0.133072 | 0.133072 | 0.133073 | 0.135335 | −1.67 % |
| −24 | 5 min | 0.123900 | 0.123900 | 0.123901 | 0.135335 | −8.45 % |
| −24 | 15 min | 0.100112 | 0.100112 | 0.100113 | 0.135335 | −26.0 % |

Two separable error sources (derived):

- **Euler error.** With a tight merge tolerance, EPANET equals the forward-Euler prediction to about 1e-5 relative, so the reaction error is pure Euler error in `kb·dt`.
- **Segment-merge error.** With the default 0.01 mg/L tolerance, merging water of different ages adds an error of either sign: −0.66 % at 30 s and +0.34 % at 5 min for kb = −1/day. It vanishes when the per-step concentration change exceeds `Ctol`.

For `kb·dt < −1` the Euler factor is negative and is clipped to 0 by `MAX(0, ·)`. At kb = −240/day, the 15 min step returned exactly 0.

Basis: execution + source.

### 4. Cross-system invariants, comprehensibility (C1) and model refinement (C2)

| Invariant | ANUGA | SWMM 5.2.4 | EPANET 2.3.06 | LISFLOOD |
| --- | --- | --- | --- | --- |
| Positivity (`h ≥ 0`, `D ≥ 0`, `c ≥ 0`) | Reconstruction clamp, then non-conservative `protect` with a volume ledger | `yNew < 0 ⇒ 0` (`dynwave.c:744`); depth floors `FUDGE` | PDA barriers; quality `MAX(0, c)` | Newton clamp at `1e-12` |
| Steady-state preservation | Exact lake-at-rest by edge algebra | Not examined | Exact zero cross-flow approached to 1e-7–1e-11 L/s | Known not to apply |
| Singular derivative near zero | Friction `h^(−7/3)` made unconditionally damping | Surcharged node: area → slot width or `Σ dQ/dH` | H-W gradient → 0 replaced by a linear branch | Newton derivative `1 + b·a·Q^(b−1)` with `Q ≥ 1e-12` |
| Mass ledger | `mass_error` + `negative_cells_volume` + warning at 1e-4 | Continuity error (%) and node flow-balance error | Flow balance + quality mass ratio | Not examined |

**C1 (human comprehensibility).** The ANUGA invariant fits in about five lines of arithmetic (§1.2), and the source comments are unusually explicit about why parameters must not be changed. The DE0/DE1 default mismatch is a real hidden trap. A user who reads only the guide will believe DE1 is in force.

The SWMM failure modes are not legible from its own diagnostics:

- The "all links are stable" message coexisted with a −1.10 % continuity error and 2.1× flow amplification.
- EXTRAN's intra-step rim spikes are visible only by comparing "Maximum Depth" with "Reported Max Depth".

EPANET's PDA reporting ("Demand Deficit", deficient-node percentage) is directly auditable. In contrast, its DDA warning gives no deficit at all.

**C2 (simplicity and orthogonality).** Each code has a minimal unifying abstraction available, and in each case the code partly takes it and partly adds special cases:

- **ANUGA** unifies wet/dry, well-balancing and positivity in one reconstruction, a deep-module success. The residual non-conservative clip is a second mechanism enforcing the same `h ≥ 0` invariant.
- **SWMM** carries two surcharge mechanisms (EXTRAN node algebra, SLOT storage) plus two crown cutoffs. The slot is the more uniform model, because surcharge becomes ordinary storage, but the time-step control was not generalized with it (§2.3). The special case moved into the stability limiter rather than disappearing.
- **EPANET** expresses PDA, emitters and leakage as head-loss elements in the same GGA matrix, a genuine orthogonal design. Status logic (CV, PRV, PSV, FCV, pump) remains a separate discrete layer with its own hysteresis constants.

### 5. Performance and resource footprint (L1–L6)

| Level | ANUGA | SWMM 5.2.4 | EPANET 2.3.06 | LISFLOOD |
| --- | --- | --- | --- | --- |
| L1 authoring/maintenance | not measured | not measured | not measured | not measured |
| L2 build (from scratch, single `gcc -O2` invocation, serial) | not measured (Meson/Cython build not run) | 10.2 s and 17.9 s wall on two runs; peak compiler RSS 50.7 MB; 50,301 lines in `src/solver/*.[ch]` | 6.0 s and 9.8 s wall on two runs; peak compiler RSS 68.3 MB; 29,231 lines in `src/*.[ch]` | not applicable (Python/Numba; JIT not measured) |
| L3 elaboration/compile latency of models | not measured | input parse included in L4 | input parse included in L4 | not measured |
| L4 execution (CLI process incl. start-up, median of 30) | ANUGA not run; toy 1-D: 2.6 s for 4 runs of 2000–4000 steps (Python) | probe system, 6 h simulated: 171 ms at 1 s EXTRAN, 146 ms at 1 s SLOT, 14.4 ms at 10 s SLOT | Net1 24 h hyd+qual 10.9 ms; Net3 12.1 ms; 1-period PDA 9.3 ms | not measured |
| L5 certificate/verification checking | not applicable | not applicable | not applicable | not applicable |
| L6 footprint | not measured | binary 528,224 B (text 447,222 B); peak RSS 2.4 MB | binary 297,152 B (text 254,870 B); peak RSS 3.2 MB | not measured |

Basis: execution (host and commands under **Evidence**). The EPANET binary SHA-256 was identical across the two builds, so the build is reproducible on this host (`815f6566…a30f`).

### 6. Validation coverage (V1–V4)

- **V1 (specification adequacy, non-vacuity).**
  - ANUGA: the upstream tests pin well-balance (`test_ader2.py`), wet/dry clamp volume conservation within 1e-6 m³ (`test_DE_gpu_omp.py:3722–3748`), and the negative-volume warning (`test_negative_cells_warning.py`).
  - The probes in this report are discriminating checks. The SWMM probe separates the two surcharge methods. The EPANET quality probe separates Euler error from merge error. The main-break probe falsifies DDA's physical plausibility.
  - No mutation testing of the codes was performed.
- **V2 (differential/compiler testing).**
  - CPU/GPU agreement is tested inside ANUGA, for example `assert_allclose(..., atol=1e-10)` between compute modes in `test_DE_gpu_omp.py`.
  - A test comment records a known defect: "a process that has built several mode-2 domains gets wrong results from a later one (stage off by ~1 m from the 3rd-4th)" (`_FrictionSyncCase` docstring). This is documentation of an upstream GPU-path issue; it was not reproduced here.
  - No cross-solver differential testing (for example SWMM versus a Godunov mixed-flow code) was performed.
- **V3 (concurrency, crash, physical).** SWMM's OpenMP `findLinkFlows`/`findNodeDepths` was run with `THREADS 1` only. Thread-count sensitivity of results was not measured.
- **V4 (plant falsification, field replay).** No field or laboratory data were replayed. Dam-break benchmarks with measured data, and EPANET calibration against SCADA, are not examined.

## Boundaries

- **Not examined: ANUGA execution.** ANUGA itself was not built or executed. All ANUGA behaviour statements are source/documentation-based, or come from the 1-D toy, which omits second-order extrapolation, limiters, unstructured geometry, riverwalls, culverts, ADER/RK paths and GPU offload.
- **Unknown: ANUGA second-order conservation.** Whether ANUGA's second-order DE1/DE_ader2 extrapolation preserves lake-at-rest exactly at wet/dry fronts with discontinuous bed. The `atol = 1e-10` upstream test covers a fully wet sloped bed only.
- **Unknown: ANUGA steep-bed dam break.** How much water ANUGA's `protect` adds in a realistic steep-bed dam break. The ledger exists (`negative_cells_volume`), but no ANUGA run was made.
- **Not examined: the Kurganov–Petrova 2007 positivity CFL bound** as it applies to ANUGA's edge-radius time step (`radius/max_speed`). The toy stayed positive at CFL 0.9 at first order; that is not a proof for ANUGA.
- **Not examined: LISFLOOD.** LISFLOOD's MCT (Muskingum–Cunge–Todini) routing, split routing, reservoirs, and its full water balance. Only the kinematic-wave pixel solver was read.
- **Known not to apply: LISFLOOD steady states.** Lake-at-rest and backwater cannot be represented in LISFLOOD kinematic routing.
- **Not examined: SWMM scope.**
  - Non-circular closed sections: the slot crossing argument of §2.2 is specific to `W_Circ`.
  - Storage-node surcharge, ponding, force mains, inlets, and SWMM's `THREADS > 1`.
- **Not examined: SWMM's documented formulation.** The SWMM Reference Manual Volume II (EPA/600/R-17/111) was not read for this report; SWMM claims rest on source and execution.
- **Unknown: whether the 1.5e-5 offset** between `0.985257` and the computed table/Sjöberg crossing `0.985242` reflects a different interpolation or a rounded design value.
- **Not established: SLOT step limits.** The table does not show that SLOT is unstable above a universal step, nor that EXTRAN is always safe at long steps. Both results are for one system and one hydrograph.
- **Not examined: EPANET hydraulics scope.**
  - Tanks, pumps, PRV/PSV/FCV, rule-based controls, leakage (`leakage.c`), and multi-period runs.
  - Status cycling was not provoked.
  - The EPANET 2.2 User Manual (EPA/600/R-20/133) was not read; EPANET claims rest on source and execution.
- **Not established: RQTOL on large networks.** RQTOL was observed to have no effect on convergence speed only on a 4-junction loop.
- **Not examined: EPANET quality scope.** Wall reactions, tank mixing models, and water age.
- **Unknown: EPANET results below 1e-9.** At kb = −240/day, EPANET returned 1e-9 and 0 where forward Euler predicts 8.5e-10 and 3.1e-10. Behaviour in this regime was not investigated.
- **Not examined (cited only): Todini & Pilati (1988).** Cited by the EPANET source as the gradient algorithm. The original chapter was not examined, and no DOI exists.
- **Not examined: regulatory guidance and field data.** FEMA P-946 and other inundation-mapping guidance, and all field or laboratory datasets.
- **Not measured.** L1, L3, L5, ANUGA/LISFLOOD L2/L4/L6, and energy/power.

## Evidence

**Source pins** (all retrieved through the GitHub API and `raw.githubusercontent.com` on 2026-11-20 UTC; each revision was the default-branch HEAD on that date):

- `anuga-community/anuga_core@44ed9a1ff7c676de0d52c6cce72ab6e35a031245`:
  - `anuga/shallow_water/gpu/core_kernels.c` lines 2400–2470, 2784–2814, 2833–2945, 2965–3025, 3031–3064, 3412–3809 and 3814–3820.
  - `anuga/shallow_water/gpu/gpu_device_helpers.h` lines 210–369.
  - `anuga/shallow_water/sw_domain_openmp.c` lines 199–364.
  - `anuga/shallow_water/shallow_water_domain.py` lines 673, 3792–4040, 4788–4831, 5100–5115, 6083–6098 and 6254.
  - `anuga/config.py` lines 12, 45, 140, 193, 196 and 214.
  - `docs/source/setup_anuga_script/flow_algorithms.rst` lines 1–200.
  - `anuga/shallow_water/tests/test_ader2.py` lines 44–76, `test_DE_gpu_omp.py` lines 3658–3748, and `test_negative_cells_warning.py`.
- `USEPA/Stormwater-Management-Model@07c371f8a0d477da1d9d4e7c0d75719664f62fec`:
  - `src/solver/dwflow.c` lines 100–170 and 575–619.
  - `src/solver/dynwave.c` lines 60–66, 117–161, 636–762 and 799–921.
  - `src/solver/link.c` lines 847–871, `project.c` lines 757–760 and 846–847, `xsect.c` lines 955–956 and 1474–1499, `xsect.dat` lines 67–75, `consts.h:19`.
- `OpenWaterAnalytics/EPANET@57d8bd8ad60e89b57f2a1ac591f05c8e13589866`:
  - `src/hydcoeffs.c` lines 34–35, 69–101, 502–539, 542–619, 622–732 and 735–782.
  - `src/hydsolver.c` lines 60–213, plus `hasconverged` and `pdaconverged`.
  - `src/hydstatus.c` lines 175–239, `src/input1.c` lines 24–38 and 117–137, `src/input3.c` lines 1895–2045 and 2203–2207, `src/hydraul.c:23`.
  - `src/qualroute.c` lines 323–366, `src/qualreact.c` lines 269–438, `src/quality.c` lines 580–608, `src/types.h:35`.
- `ec-jrc/lisflood-code@05a2f58bfd986e33086d52c0947bcff6f452f62b`: `src/lisflood/hydrological_modules/kinematic_wave_parallel_tools.py` lines 26–131 and `routing.py` lines 81–91 and 318–343.

**Literature** (metadata verified via the Crossref REST API on 2026-11-20):

- Audusse, Bouchut, Bristeau, Klein, Perthame, SIAM J. Sci. Comput. 25(6):2050–2065 (2004), doi:10.1137/S1064827503431090.
- Kurganov and Petrova, Commun. Math. Sci. 5(1):133–160 (2007), doi:10.4310/CMS.2007.v5.n1.a6.
- Kurganov, Noelle, Petrova, SIAM J. Sci. Comput. 23(3):707–740 (2001), doi:10.1137/S1064827500373413.
- León, Ghidaoui, Schmidt, García, J. Hydraul. Res. 47(2):147–156 (2009), doi:10.3826/jhr.2009.3157.
- Wagner, Shamir, Marks, J. Water Resour. Plann. Manage. 114(3):276–294 (1988), doi:10.1061/(ASCE)0733-9496(1988)114:3(276).
- Van Der Knijff, Younis, De Roo, Int. J. Geogr. Inf. Sci. 24(2):189–212 (2010), doi:10.1080/13658810802549154. The DOI `10.1080/13658810902949023`, which is sometimes quoted for this paper, did not resolve.

**Build commands** (host described under **Applicability**):

```sh
# EPANET (from repository root)
gcc -O2 -w -Iinclude -Isrc -o runepanet run/main.c src/*.c -lm
gcc -O2 -w -Iinclude -Isrc -o enquery    enquery.c   src/*.c -lm   # toolkit harness below
gcc -O2 -w -Iinclude -Isrc -o qualprobe  qualprobe.c src/*.c -lm
# SWMM (from repository root; src/solver/error.txt and xsect.dat are #included)
gcc -O2 -fopenmp -w -Isrc/solver/include -Isrc/solver -o runswmm src/run/main.c src/solver/*.c -lm
```

**SWMM probe input** (`surcharge_probe.py` writes this template with `{method}` ∈ {EXTRAN, SLOT}, `{step}` ∈ {0.5, 1, 5, 10, 20, 30} and `{vstep}` ∈ {0, 0.75}; it runs `runswmm in.inp out.rpt out.out` and parses `Continuity Error (%)`, `Node Depth Summary`, `Link Flow Summary`, `Routing Time Step Summary` and `Highest Flow Instability Indexes`). The input file must not end with an `[END]` line, which SWMM 5.2.4 rejects with `ERROR 205`.

```text
[OPTIONS]
FLOW_UNITS CMS / INFILTRATION HORTON / FLOW_ROUTING DYNWAVE
START 01/01/2020 00:00:00, END 06:00:00, REPORT_STEP/WET_STEP/DRY_STEP 00:01:00
ROUTING_STEP {step} / VARIABLE_STEP {vstep} / ALLOW_PONDING NO / INERTIAL_DAMPING PARTIAL
NORMAL_FLOW_LIMITED BOTH / SURCHARGE_METHOD {method} / MAX_TRIALS 8 / HEAD_TOLERANCE 0.0015 / THREADS 1
[JUNCTIONS] J1 10.0 4.0 0 0 0 ; J2 9.5 4.0 0 0 0 ; J3 9.0 4.0 0 0 0
[OUTFALLS]  O1 8.5 FREE NO
[CONDUITS]  C1 J1 J2 200 0.013 0 0 0 0 ; C2 J2 J3 ... ; C3 J3 O1 ...
[XSECTIONS] C1..C3 CIRCULAR 0.6 0 0 0 1
[INFLOWS]   J1 FLOW HYD FLOW 1.0 1.0 0
[TIMESERIES] HYD 00:00 0.0 ; 01:00 0.6 ; 02:00 0.0 ; 06:00 0.0
[REPORT] INPUT NO / CONTROLS NO / NODES ALL / LINKS ALL
```

**EPANET probe inputs.**

- `main_break_probe.py`:
  - `[OPTIONS] UNITS LPS, HEADLOSS H-W, PRESSURE METERS, DEMAND MODEL {DDA|PDA}, MINIMUM PRESSURE 0, REQUIRED PRESSURE 20, PRESSURE EXPONENT 0.5, TRIALS 200, ACCURACY 0.001, UNBALANCED CONTINUE 10, [TIMES] DURATION 0`.
  - Pipes `P1 R J1 1000 300 120`, `P2 J1 J2 1000 250 120`, `P3 J2 J3 1000 150 120`; `[EMITTERS] J2 40` in the break cases.
- `zero_flow_probe.py` plus `enquery`:
  - Junctions `J1 10 0`, `J2 10 20`, `J3 10 {20|20.01|21}`; reservoir `R 60`.
  - Pipes `P0 R J1 500 400`, `PA J1 J2 800 250`, `PB J1 J3 800 250`, `PX J2 J3 300 150`, with C = 120 (H-W) or roughness 0.1 mm (D-W).
  - `RQTOL {1e-12..1e-1}`, `ACCURACY 1e-6`.
- `quality_step_probe.py` plus `qualprobe`:
  - Pipe `P1 R J1 1018.5916 300 120`, `J1` demand 10 L/s, `[QUALITY] R 1.0`, `[REACTIONS] ORDER BULK 1, GLOBAL BULK {kb}, GLOBAL WALL 0`.
  - `DURATION 48:00`, `HYDRAULIC TIMESTEP 1:00`, `QUALITY TIMESTEP {0:00:30|0:01|0:05|0:15}`, `TOLERANCE {0.01|1e-4|1e-6}`.
  - J1 quality is read after the final `EN_nextQ`.

The toolkit harness `enquery.c` prints full-precision values. The listing below is condensed from the harness used; its print format differs, but the same API calls produce the values in §3.1.

```c
#include <stdio.h>
#include "epanet2_2.h"
int main(int argc, char **argv) {          /* enquery file.inp LINKID [NODEID ...] */
  EN_Project ph; int idx; double v, it, re, h, p, d, e;
  EN_createproject(&ph); if (EN_open(ph, argv[1], "/dev/null", "") > 100) return 1;
  EN_solveH(ph); EN_getstatistic(ph, EN_ITERATIONS, &it); EN_getstatistic(ph, EN_RELATIVEERROR, &re);
  EN_getlinkindex(ph, argv[2], &idx); EN_getlinkvalue(ph, idx, EN_FLOW, &v);
  printf("iterations=%.0f relerr=%.3e flow=%.12e\n", it, re, v);
  for (int a = 3; a < argc; a++) { EN_getnodeindex(ph, argv[a], &idx);
    EN_getnodevalue(ph, idx, EN_HEAD, &h); EN_getnodevalue(ph, idx, EN_PRESSURE, &p);
    EN_getnodevalue(ph, idx, EN_DEMAND, &d); EN_getnodevalue(ph, idx, EN_EMITTERFLOW, &e);
    printf("%s head=%.9f p=%.9f demand=%.9f emitter=%.9f\n", argv[a], h, p, d, e); }
  EN_close(ph); EN_deleteproject(ph); return 0; }
```

`qualprobe.c` uses the same pattern: `EN_solveH`, then `EN_openQ`, `EN_initQ(EN_NOSAVE)`, and a loop of `EN_runQ`, `EN_getnodevalue(EN_QUALITY)` and `EN_nextQ` until `tstep == 0`.

**Toy model core (`hr_toy.py`).** This is the 1-D transcription of the ANUGA edge formula. The listing is a scalar restatement of the vectorized NumPy code that was run. The full script, about 150 lines, adds the strawman variant, the two cases of §1.7, mirrored ghost cells and the protect clip.

```python
def edge(wl, ul, hle, zl, wr, ur, hre, zr, g=9.8):
    zh = max(zl, zr); hl = max(hle + zl - zh, 0.0); hr = max(hre + zr - zh, 0.0)
    if hl == 0.0 and hr == 0.0: return 0.0, 0.0, 0.0, hl, hr, 0.0
    uL = ul if hle > 0 else 0.0; uR = ur if hre > 0 else 0.0
    cL, cR = (g*hl)**0.5, (g*hr)**0.5
    smax = max(uL + cL, uR + cR, 0.0); smin = min(uL - cL, uR - cR, 0.0); d = smax - smin
    if d < 1e-12: return 0.0, 0.0, 0.25*g*(hl*hl + hr*hr), hl, hr, 0.0
    f0 = (smax*uL*hl - smin*uR*hr + smax*smin*(max(wr, zh) - max(wl, zh)))/d
    f1 = (smax*uL*uL*hl - smin*uR*uR*hr + smax*smin*(uR*hr - uL*hl))/d
    pf = 0.5*g*(smax*hl*hl - smin*hr*hr)/d
    return f0, f1, pf, hl, hr, max(smax, -smin)
# left cell (n=+1): dw -= f0; duh -= f1 + (-g/2*(hl^2 - hle^2) + pf)
# right cell (n=-1): dw += f0; duh += f1 + (-g/2*(hr^2 - hre^2) + pf)
# dt = 0.9*dx/max_speed; protect: h<1e-12 => uh=0; h<0 => w=z (clipped volume recorded)
```

**Observation dates.** All source reading, builds, probes and literature checks took place on 2026-11-20 (UTC).

## Revalidation

1. **ANUGA edge formula.**
   - Diff `core_kernels.c` around `core_compute_fluxes_central` (the `z_half`/`h_left`/`h_right`/`pressuregrad_work` lines) and `gpu_flux_function_central` against a newer revision. If unchanged, §1.1–1.3 carry over.
   - Run upstream `pytest anuga/shallow_water/tests/test_ader2.py::TestAder2WellBalance` to confirm the well-balance tests.
2. **ANUGA default.** `grep -n "def set_flow_algorithm" anuga/shallow_water/shallow_water_domain.py` and `grep -n "General-purpose default" docs/source/setup_anuga_script/flow_algorithms.rst` show whether the default/documentation discrepancy persists.
3. **SWMM.**
   - Diff `getSlotWidth` (`dwflow.c`), the crown-cutoff constants and `setNodeDepth` (`dynwave.c`), and `link_getFroude` (`link.c`).
   - Rebuild with the command above and rerun `surcharge_probe.py`. Three rows discriminate: SLOT at 10 s should give about −0.016 %; SLOT at 30 s about −1.08 % with C2 peak > 0.6; and SLOT with `VARIABLE_STEP 0.75` should stay unstable.
   - If a newer SWMM includes slot celerity in `getLinkStep`, the last row will change.
4. **EPANET.**
   - `grep -n "RQTOL\|CHECKFREQ\|MAXCHECK\|CHEMTOL" src/input1.c` and diff `pipecoeff`, `demandheadloss`, `pdaconverged` and `pipereact`.
   - Rerun `main_break_probe.py`: case B should still report −2.49 m with 10.00 L/s delivered, and case C 2.70 L/s with an 11.497 L/s deficit.
   - Rerun `quality_step_probe.py` with `TOLERANCE 1e-4`: kb = −24/day at a 5 min step should give 0.123900, the Euler value.
5. **LISFLOOD.** Diff `solve1Pixel` in `kinematic_wave_parallel_tools.py` (the `NEWTON_TOL` clamp and the zeroing).
6. **Toy.** Rerun `hr_toy.py`. Lake-at-rest residuals at the 1e-16 level confirm only that the transcription is unchanged; they do not test ANUGA.
