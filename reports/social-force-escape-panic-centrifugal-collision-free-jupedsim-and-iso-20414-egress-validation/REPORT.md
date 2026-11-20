# Social-force, escape-panic, generalized centrifugal-force and collision-free speed models in JuPedSim; PedPy fundamental-diagram methods; ISO 20414 / NIST TN 1822 egress-model verification and the gaps for high-density incidents

## Summary

- **JuPedSim's "SocialForceModel" is the Helbing–Farkas–Vicsek (2000) escape-panic model.** At `PedestrianDynamics/jupedsim@789178048117975d136f849bcdf4add962a9004a`, the model doc cites DOI `10.1038/35035023` and implements:
  - an isotropic exponential repulsion `A exp((r_ij − d_ij)/B)`, with contact pushing `k(r_ij − d_ij)` and sliding friction `κ(r_ij − d_ij)Δv·t` when `d < r_ij`;
  - semi-implicit Euler integration (`v ← v + F/m·dt; x ← x + v·dt`).

  The Helbing–Molnár (1995) anisotropic, field-of-view-weighted form is **not** implemented: a source comment reads `// todo reduce range of force to 180 degrees`. `Basis: source`
- **All JuPedSim models update synchronously, check overlap only at insertion, and fail hard on wall crossing.** Each step computes every agent's move from the same generation and then swaps (`operational_decision_system.hpp:46-58`). `check_model_constraint` runs only when an agent is added. If a displacement leaves the walkable mesh, the run aborts with `SimulationError("move_on_surface(): path hit a wall")` (`geometry/location.cpp:202-208`). Agent–agent overlap during a run is therefore tolerated silently, while wall penetration aborts. `Basis: source + execution`
- **Measured on the real engine (60-agent evacuation through a 1 m door, 3 seeds).**

  | Model | Time-step behaviour | Overlap and completion |
  |---|---|---|
  | collision-free speed (CFSM) | no aborts; evacuation time rises monotonically with `dt`, from 60.9 s at 0.005 s to 75.1 s at 0.1 s (+23 %) | no overlap at `dt ≤ 0.05` |
  | anticipation velocity (AVM) | 69.7–73.4 s across `dt` | one of 3 runs at `dt = 0.05` left 21 agents gridlocked |
  | social force (SFM) | `dt ≥ 0.05` aborted with the wall-crossing error | at `dt ≤ 0.02`, every run left one agent permanently stuck in front of the door |
  | generalized centrifugal force (GCFM) | gridlocked or aborted in every base-geometry run | in a geometry without a wall behind the exit it completed in 160–178 s, with minimum centre distances near 0.09 m |

  `Basis: execution`
- **A lone SFM agent cannot pass a 1.0 m door with the model's default state.** Defaults: `v0 = 0.8 m/s`, `A = 2000 N`, `B = 0.08 m`, `r = 0.3 m`, `m = 80 kg`, `τ = 0.5 s`. The agent stops 0.34 m before the door plane, in both a corridor-door and a thin-wall-door geometry, at `dt = 0.01`. The analogous equilibrium for `v0 = 1.2`, starting at rest at `x = 7.7`, stays at `x = 7.7888` for every `dt` tested (0.001, 0.01 and 0.05). It passes at 1.2 m width, at `v0 ≥ 1.2` with a running start, or with `obstacle_scale ≤ 1000 N`. This is a static force equilibrium of the implementation, not an integration artefact. Source inspection shows each wall segment contributes its own closest point, so a convex door-post corner is counted once per incident segment. `Basis: execution + source + derived`
- **The choice of density/speed method changes a fundamental diagram most in the transition regime.** PedPy implements classic (`N/A`), Voronoi, passing (per-pedestrian) and line/N-t methods. These formulas were re-implemented and applied to the same JuPedSim corridor trajectories, from free flow to 0.5 m bottleneck jams. The methods agreed within 0.01 m/s in free flow. Density-binned mean speeds differed by up to 0.47 m/s between methods at 1.25–1.50 m⁻². A linear speed–density fit gave `v0` from 0.59 to 1.20 m/s and `ρmax` from 3.5 to 7.2 m⁻², depending only on the method. In jams, the line method (`ρ = J/(v·b)`) produced 17.7 m⁻², above the 7.2 m⁻² close-packing limit for the simulated 0.2 m discs. `Basis: execution of JuPedSim + re-implementation of PedPy formulas (not PedPy itself)`
- **The examined verification tests stop below crowd-disaster densities.** NIST TN 1822 lists 17 verification tests. Verif.5.2 places 100 people in an 8×5 m room, which TN 1822 itself describes as high density: footnote 7 reads "a density of 2.5 people/m2 ... chosen in order to investigate flow rates in the case of congested areas". In the test definitions read, no test asserts behaviour at the 4–7 m⁻² densities where Helbing and Mukerji (2012) identify "crowd turbulence", with crowd pressure defined as "density times variability of body movements". Its only flow test (IMO Test 4 / Verif.5.2) is a **ceiling**: flow "should not exceed 1.33 p/s". ISO 20414:2020 organizes verification into basic, behavioural, fire–people and building-specific components (clause structure examined). Its test-level content was not examined. `Basis: normative + documentation + derived`

## Applicability

Subjects:

- **JuPedSim (`PedestrianDynamics/jupedsim@789178048117975d136f849bcdf4add962a9004a`).** Source was inspected. The library and its `pyjupedsim` Python extension were built from that tree, with vendored submodules at the gitlinks recorded in the tree: CGAL `28811b67`, pybind11 `97bf890d`, fmt `1be298e1`, googletest `063de7e9`, benchmark `192ef100`, corrosion `1499b14e`. The build used CMake 4.5.1, Ninja and GCC 15.2.0 with `CMAKE_BUILD_TYPE=Release`, `BUILD_TESTS=OFF` and default `USE_IPO=ON`. The final stub-generation step failed only because `pybind11_stubgen` was absent; the extension module itself built. The Rust `floorfield` crate dependencies were resolved from its `Cargo.lock`. Execution used the raw `pyjupedsim._Simulation` binding, because the `jupedsim` Python wrapper requires `shapely`, which was absent. All probes ran on this build.
- **PedPy (`PedestrianDynamics/PedPy@0604d9af80eeced0fe16d65d503ea78381dae11a`).** Source only; **not executed** (no `pandas`/`shapely` on the host). The method-comparison results execute a numpy re-implementation of PedPy's documented formulas.
- **Vadere (`pedestrian-dynamics-HM/vadere@917aeaf5c430b828a723b34bf02cf095464f9c91`).** Source, scenario files and CI configuration were inspected; not built or run. Its primary repository is hosted on GitLab; the GitHub repository examined is the research group's GitHub copy, and parity with GitLab was not checked.
- **ISO 20414:2020 (first edition, 2020-11).** Only the publicly available preview was examined: foreword, introduction, clause 1 scope, clause 3 term list and the table of contents. The test-level content of clauses 5–10 was **not** examined.
- **NIST TN 1822 (DOI 10.6028/NIST.TN.1822).** Full text examined.
- **Papers.** Helbing–Molnár 1995, Helbing–Farkas–Vicsek 2000, Chraibi–Seyfried–Schadschneider 2010, Tordeux–Chraibi–Seyfried 2016, Xu–Chraibi–Seyfried 2021, Seyfried et al. 2005, Zhang et al. 2011 and Steffen–Seyfried 2010 were cited by metadata verified through Crossref; their equations were read from the JuPedSim implementation, not from the papers. Helbing–Mukerji 2012 was read in full (open access).

The report characterizes the JuPedSim implementations at one revision, compares PedPy's measurement definitions, and maps two V&V protocols onto JuPedSim and Vadere. Execution findings apply only to the stated geometries, parameter values and build.

Host: Intel Xeon @ 2.60 GHz, 96 vCPUs, 236 GB RAM, Linux 7.1. The host was shared, with load average 75–200 during runs, so absolute timings carry roughly ±50 % noise (two repeats of the engine benchmark differed by up to 1.9×).

## Findings

### 1. Equations of motion and integration as implemented

| Model (JuPedSim class) | State update per step | Interaction law | Overlap/oscillation handling | Defaults (source) |
|---|---|---|---|---|
| `SocialForceModel` = HFV 2000 escape panic | `v' = v + [(v0 e0 − v)/τ + Σf/m]·dt`; `x' = x + v'·dt` (`social_force_model.cpp:53-55,122-126`) | `n·[A e^{(r−d)/B} + k(r−d)⁺] + t·κ(r−d)⁺(Δv·t)` (`160-180`); walls use the same form with `obstacle_scale` | contact forces only; no velocity clamp; second-order dynamics can overshoot | `A = 2000 N`, `B = 0.08 m`, `k = 1.2e5`, `κ = 2.4e5`, `m = 80 kg`, `τ = 0.5 s`, `v0 = 0.8 m/s`, `r = 0.3 m`; neighbour cut-off 2.5 m; walls queried within 4 m |
| `GeneralizedCentrifugalForceModel` (Chraibi et al. 2010) | `v' = v + (F_driv + ΣF_rep + ΣF_wall)/m·dt` with velocity-dependent ellipses (`generalized_centrifugal_force_model.cpp:81-90`) | `F = −m k_ij (η v0 + v_ij)² / d_eff`, `k_ij = (v·e + abs(v·e))/(2abs(v))` (`244-262`); Hermite-interpolated cut-offs, capped at `max_*_repulsion_force` | force capped in the overlap region (`266-270`); `mindist = 0.5` hard-coded "for performance reasons" (`220-221`) | `η = 0.3` (neighbour), `0.2` (wall); `m = 1 kg`, `τ = 0.5`, `v0 = 1.2`, `a_min = 0.2`, `b_min = 0.2`, `b_max = 0.4`, `a_v = 1`; interaction range 2 m |
| `CollisionFreeSpeedModel` (Tordeux et al. 2016) | `e = normalize(e0 + Σ a e^{(l−d)/D} n_ij + Σ walls)`; `x' = x + min(max(s/T, 0), v0)·e·dt` (`collision_free_speed_model.cpp:61-73,120-126`) | first-order; `s` = distance minus `l` to the nearest neighbour ahead whose lateral offset is `≤ r_i + r_j` (`128-147`) | velocity vanishes as `s → 0`; neighbours outside the forward corridor do not limit speed | `a = 8`, `D = 0.1 m`, wall `5` / `0.02 m`, `T = 1 s`, `v0 = 1.2`, `r = 0.2` |
| `AnticipationVelocityModel` (Xu et al. 2021) | direction relaxed with reaction time, `e' = e + (e_calc − e)/τ_r·dt` (`72-93`); speed `s/T` | repulsion uses gap reduced by `(v_i − v_j)·e_ij·t_a` (`253-256`) | **random "creep"**: if `abs(s/T) < 0.01`, speed set to +0.01, −0.01 or 0 m/s by RNG (`170-187`); wall sliding applied after the spacing-based speed (`63-64`) | `T = 1.06`, `t_a = 1.0`, `τ_r = 0.3`, `v0 = 1.2`, `r = 0.2`, `pushout_strength = 0.3` |

Also present: `CollisionFreeSpeedModelV2` (per-agent repulsion parameters; otherwise identical to V1 in the compared lines), `CollisionFreeSpeedModelV3` and `WarpDriverModel` (Wolinski–Lin–Pettré 2016). These were not probed. `Basis: source`

Insertion checks are inconsistent across models:

- CFSM, V2 and AVM reject an agent if `r_i + r_j ≥ d` or a wall lies within `r`.
- SFM rejects only if `current_state.radius >= distance` (`social_force_model.cpp:102`), the agent's **own** radius rather than the sum, and checks walls only within `radius/2` (`112-119`). An SFM agent can therefore be inserted overlapping a neighbour by up to `r_j`.

`Basis: source`

### 2. Measured time-step and parameter sensitivity (real engine)

Scenario (`support/jps_probe.py`):

- **Geometry.** An 8×8 m room has a 1.0 m door at `x = 8`, `y ∈ [3.5, 4.5]`. Behind it is a 2 m corridor whose last 0.5 m is the exit stage ("base").
- **Agents.** 60 agents start on a 0.75 m grid jittered by ±0.1 m (3 seeds), all with `v0 = 1.2 m/s` and other state at defaults.
- **Metrics.** Over the run, the minimum centre distance and the maximum circular overlap `2r − d` are recorded. The "backward-step fraction" is the share of agent-steps moving away from the door or exit centre, a crude oscillation indicator.

| Model | `dt` (s) | completed | t50 (s) | t90 (s) | evac (s) | min centre dist (m) | max overlap (m) | backward frac |
|---|---|---|---|---|---|---|---|---|
| CFSM | 0.005 | 3/3 | 31.5 | 54.3 | 60.9 [59.5–62.7] | 0.441 | 0 | 0.177 |
| CFSM | 0.01 | 3/3 | 33.6 | 56.3 | 62.9 | 0.450 | 0 | 0.185 |
| CFSM | 0.02 | 3/3 | 35.9 | 61.3 | 67.6 | 0.448 | 0 | 0.196 |
| CFSM | 0.05 | 3/3 | 37.6 | 64.7 | 71.2 | 0.436 | 0 | 0.204 |
| CFSM | 0.1 | 3/3 | 38.4 | 67.9 | 75.1 [73.9–76.2] | 0.412 | 0.004 (max 0.013) | 0.216 |
| AVM | 0.005 | 3/3 | 36.1 | 63.5 | 70.2 | 0.420 | 0 | 0.026 |
| AVM | 0.01 | 3/3 | 36.6 | 63.1 | 69.7 | 0.420 | 0 | 0.026 |
| AVM | 0.05 | 2/3 (21 stuck) | 36.3 | 64.0 | 70.6 | 0.394 | 0.009 | 0.119 |
| AVM | 0.1 | 3/3 | 38.2 | 66.3 | 73.4 | 0.412 | 0.001 | 0.022 |
| SFM | 0.005 | 0/3 (1 stuck each) | 33.2 | 80.2 | – | 0.579 | 0.021 | 0.316 |
| SFM | 0.01 | 0/3 (1 stuck each) | 32.4 | 69.8 | – | 0.585 | 0.015 | 0.309 |
| SFM | 0.02 | 0/3 (1 stuck each) | 34.4 | 74.5 | – | 0.588 | 0.012 | 0.311 |
| SFM | 0.05, 0.1 | 0/3 | – | – | – | 0.11–0.34 before abort | 0.26–0.49 | – |
| GCFM | 0.005 | 0/3 (56 of 60 remain at 300 s) | – | – | – | 0.092 | n/a (ellipses) | 0.123 |
| GCFM | 0.01–0.1 | 0/3 | – | – | – | 0.017–0.17 | n/a | – |

At SFM `dt ≥ 0.05` and GCFM `dt ≥ 0.01` (except one GCFM run at 0.01 that gridlocked), every run aborted with `SimulationError: move_on_surface(): path hit a wall`. All stuck SFM agents sat at `(7.789, 4.000)`. `Basis: execution`

Extended geometry ("ext"), where the corridor continues to `x = 14` so that no wall sits behind the exit stage, at `dt` 0.005/0.01:

- GCFM completed 3/3, with evacuation 171.6 / 169.3 s and minimum centre distance 0.09–0.11 m.
- SFM still left one agent at `(7.789, 4.0)` in every run.
- CFSM (60.6 / 62.7 s) and AVM (70.2 / 69.7 s) were unchanged within seed spread.

A single GCFM agent started at `(4, 4)` in the base geometry decelerates in front of and inside the 1 m corridor, with speed falling from 1.04 m/s at `x = 6.9` to under 0.04 m/s by `x = 9.09`. It enters the exit zone (`x ≥ 9.5`) only at `t = 85.0 s`. A lone SFM agent started at `(6, 4)` exits at 4.5 s. GCFM wall repulsion reaches 2 m beyond the ellipse, so the dead-end wall behind the exit area repels agents that are trying to reach it (derived). `Basis: execution + derived`

±10 % perturbations at `dt = 0.01` (3 seeds; shown as mean t90 in s, with the baseline first):

| Model | baseline | param −10 % / +10 % |
|---|---|---|
| CFSM | 56.3 | `T`: 52.4 / 58.4; `D`: 54.7 / 54.0; `v0`: 58.7 / 53.0 |
| AVM | 63.1 | `T`: 61.4 / 65.8; `t_a`: 62.3 / 62.6; `v0`: 67.4 / 59.0 |
| SFM | 69.8 | `A`: 79.3 / 74.9; `τ`: 69.9 / 75.8; `v0`: 90.4 / 70.2 |

For SFM, the stuck-agent outcome flipped with parameters: all 3 runs **completed** at `τ = 0.45` (evacuation 86.7 s) and at `v0 = 1.32` (89.0 s), but none completed at baseline or at the other settings.

Derived reading:

- For CFSM and AVM, the time gap `T` and desired speed `v0` have comparable effects on t90, −7 % to +7 %. Both exceed the effect of the repulsion range `D` (CFSM) or the anticipation time `t_a` (AVM), which is at most 3 %, and the seed spread of the baselines, ±1–3 %.
- For SFM, a ±10 % change can switch a qualitative outcome (complete vs trapped). This is a stronger form of parameter sensitivity than the force-model literature's usual "oscillation and overlap" complaint.

`Basis: execution + derived`

### 3. The SFM door-post equilibrium

`support/jps_sfm_door.py` places one agent at `(6, 4)` with an exit beyond a door of width `w` (`dt = 0.01`). In the corridor variant the door at `x = 8` is followed by a 2 m corridor; in the thin-wall variant a 0.2 m wall separates two rooms.

| Geometry | `w` (m) | `v0` (m/s) | result |
|---|---|---|---|
| corridor | 1.0 | 0.8 (default) | stopped at `x = 7.660`, speed `7.5e-3` |
| thin wall | 1.0 | 0.8 | stopped at `x = 7.666` |
| thin wall | 1.0 | 1.2 | passed (momentum) |
| corridor | 1.0 | 1.2, start at rest at `x = 7.6` or `7.7` | stopped at `x = 7.7888` for `dt` ∈ {0.001, 0.01, 0.05} |
| corridor / thin wall | 1.2, 1.4 | 0.8 | passed |
| corridor, `obstacle_scale` 0 or 1000 N | 1.0 | 1.2, start at `7.7` | passed |

`Basis: execution`

Mechanism:

- `AgentView::walls_in_range` maps every wall segment within range to a `WallView` with its own `closest_point` (`agent_view.hpp:133-152`), and the SFM sums `obstacle_force` over all of them (`social_force_model.cpp:47-51`). At a convex door-post vertex, both incident segments return that vertex. `Basis: source`
- In the corridor geometry, counting each of the two posts twice and taking `e0 = (1, 0)`, the computed x-repulsion at the observed equilibria is 78 % of `m·v0/τ`. The calculation is `4 · A e^{(r−d)/B} · (8−x)/d`, with `d = sqrt((8−x)² + 0.5²)`. At `x = 7.7888` and `v0 = 1.2` it gives 149.7 N against 192 N; at `x = 7.660` and `v0 = 0.8` it gives 99.9 N against 128 N. The remaining 22 % is **not** explained here; see Boundaries. `Basis: derived`

### 4. Fundamental-diagram measurement methods (PedPy) and their effect

PedPy definitions at `0604d9a`:

| Method | PedPy function (file:lines) | Definition | Relation to Zhang et al. 2011 methods |
|---|---|---|---|
| classic density | `compute_classic_density` (`density_calculator.py:30-77`) | `ρ = N(t)/A(M)` using `shapely.contains` | Method C |
| Voronoi density | `compute_voronoi_density` (`80-155`) | `ρ = Σ_i abs(V_i ∩ M)/abs(V_i) / A(M)` (line 135) | Method D |
| passing density | `compute_passing_density` (`158-209`) | mean of classic `ρ(t)` over `[t_in, t_out)` per pedestrian | Method B |
| individual speed | `compute_individual_speed` (`speed_calculator.py:36-`) | `abs(X(t+n) − X(t−n))/(2n/fps)`; border modes EXCLUDE / ADAPTIVE / SINGLE_SIDED | – |
| Voronoi speed | `compute_voronoi_speed` (`263-`) | `Σ v_i abs(V_i ∩ M)/A(M)` | Method D |
| passing speed | `compute_passing_speed` (`341-376`) | `d·fps/abs(f_out − f_in)` | Method B |
| N-t flow | `compute_n_t`, `compute_flow` (`flow_calculator.py:33-182`) | only the first crossing per pedestrian counts; `J = ΔN/Δt`, with Δt between the first and last crossing in each `delta_frame` window | Method A |

PedPy warns that Voronoi cells "might be cut at unexpected places" in non-convex walkable areas (`method_utils.py:478-`) and offers a `Cutoff` to bound cell size. Steffen and Seyfried (2010) is the reference for the minimal-scatter Voronoi method. `Basis: source + documentation`

**Measured effect** (`support/fd_methods_probe.py`). JuPedSim CFSM was run in a 100 m × 2 m corridor (`v0 = 1.34`, `r = 0.2`, `T = 1`, `dt = 0.01`, 10 frames/s). There were five configurations: free flow (80 agents) and 240 agents behind a 2 m-long bottleneck of width 1.2, 0.9, 0.7 or 0.5 m at `x = 70`. Measurements used area `M = [60, 62] × [0, 2]` and a line at `x = 61`. Voronoi cells were computed by nearest-site assignment on a 0.05 m lattice, a discretized tessellation without cut-off.

Density-binned mean speed (m/s) with the number of points in parentheses, pooled over the five configurations:

| density bin (m⁻²) | A (line) | B (passing) | C (classic) | D (Voronoi, lattice) | max − min |
|---|---|---|---|---|---|
| 0.00–0.25 | – | – | – | 0.655 (229) | – |
| 0.50–0.75 | 1.296 (10) | 1.303 (84) | 1.198 (501) | 1.252 (544) | 0.105 |
| 1.00–1.25 | 0.686 (7) | 0.916 (81) | 0.915 (309) | 0.877 (442) | 0.230 |
| 1.25–1.50 | 0.460 (17) | 0.669 (102) | 0.731 (317) | 0.261 (1461) | **0.470** |
| 1.50–1.75 | 0.299 (14) | 0.418 (59) | 0.464 (964) | 0.272 (1042) | 0.192 |
| 1.75–2.00 | 0.280 (17) | 0.358 (82) | 0.196 (1338) | 0.328 (662) | 0.162 |
| 2.50–2.75 | 0.187 (13) | 0.217 (25) | 0.207 (251) | 0.194 (193) | 0.030 |
| 3.75–4.00 | 0.053 (3) | 0.108 (32) | 0.106 (400) | 0.097 (438) | 0.055 |

Linear fit `v = v0 (1 − ρ/ρmax)`, pooled:

| Method | `v0` (m/s) | `ρmax` (m⁻²) | ρ range observed (m⁻²) |
|---|---|---|---|
| A | 0.59 | 7.21 | 0.43–17.74 |
| B | 1.20 | 3.48 | 0.31–4.87 |
| C | 0.66 | 5.34 | 0.25–6.00 |
| D | 0.63 | 5.55 | 0.05–6.16 |

In free flow alone (80 agents, no bottleneck), all four methods gave mean speeds of 1.294–1.296 m/s. `Basis: execution of JuPedSim + re-implementation of PedPy formulas`

Further measured properties of the methods:

- Method A's `ρ = J/(v_A·b)` reached 17.7 m⁻², and 12.1 m⁻² behind the 0.7 m bottleneck, as crossing speeds approached zero. This exceeds the hexagonal close-packing limit for `r = 0.2 m` discs, `0.9069/(π·0.2²) = 7.2 m⁻²` (derived), so the line method produces physically impossible densities in jams.
- Method B only includes pedestrians who cross both boundaries of `M` within the run: 117 of 240 for the 0.5 m bottleneck, 147 of 240 for 0.7 m. It is therefore censored toward the pedestrians who got through.
- Re-implementation cost: 30–822 s wall and 68–506 MB peak RSS per configuration, dominated by the discretized Voronoi step.

Derived reading:

- The methods agree in free flow (within 0.01 m/s) and diverge most in the transition regime (1–2 m⁻²). There, the Voronoi method's bin means fall below the classic method's at 1.25–1.75 m⁻². One hypothesis, not isolated here, is that a continuous Voronoi density places a slow, partially overlapping crowd edge in a lower density bin than an integer head count would. The linear fit is used only as a common yardstick and is a poor functional form for these data; the binned table is the primary result.
- The Voronoi method assigns a small but non-zero density to frames in which only the edge of a distant pedestrian's cell touches `M`. This produces low-density, low-speed points (0–0.25 m⁻² bin) that a classic count cannot produce.
- Any parameter calibrated against such a diagram is conditional on the method. Examples are the jam density, or the time gap `T` and free speed `v0` of a velocity model, which shape its congested and free-flow branches.

### 5. ISO 20414 and NIST TN 1822 mapped onto JuPedSim and Vadere

**ISO 20414:2020 structure (normative; preview only).** The scope is "microscopic (agent-based) models", with partial use for macroscopic models. Clause list:

- 4 Documentation;
- 5 Verification: 5.2 basic, 5.3 behavioural, 5.4 fire–people interaction and 5.5 building-specific components;
- 6 Validation: 6.2 methods of analysis, 6.3 component and 6.4 global validation;
- 7 probabilistic models;
- 8 QA;
- 9 uncertainty;
- 10 acceptance criteria;
- Annex A, reporting template; Annex B, examples.

ISO 20414 is "complementary to ISO 16730-1", and it excludes "transportation systems in motion (e.g. trains, ships)".

**NIST TN 1822 (documentation).** It has five core components and 17 verification tests, split between `AN_VERIF` (analytical) and `EB_VERIF` (emergent behaviour):

- Verif.1.1: pre-evacuation distributions.
- Verif.2.1–2.10: corridor speed, stairs, corner, demographics, visibility, incapacitation, elevators, counter-flow, groups, disabilities.
- Verif.3.1–3.3: exit allocation, social influence, affiliation.
- Verif.4.1: dynamic exit availability.
- Verif.5.1: congestion.
- Verif.5.2: maximum flow. This is IMO Test 4: "100 persons ... room of size 8 m by 5 m with a 1 m exit ... flow rate ... should not exceed 1.33 p/s".

Validation comparisons use the Euclidean relative difference (ERD), Euclidean projection coefficient (EPC) and secant cosine (SC). Stochastic models get run-count convergence criteria.

| TN 1822 test | JuPedSim at 789178 (derived from source) | Vadere at 917aeaf (scenario files + test processors) |
|---|---|---|
| Verif.2.1 corridor speed | trivially reproducible (single agent, `v0`); no packaged test | `rimea_01_pathway_*` scenarios |
| Verif.2.3 corner | no packaged test; `notebooks/corner.ipynb` demo | `rimea_06_corner*` |
| Verif.2.4 demographics | per-agent `v0` | `rimea_07_speeds_*` |
| Verif.2.8 counter-flow | examples `example8_headon_*.py` (demos, no assertions) | not identified by name |
| Verif.3.1 exit allocation | journeys/stages give deterministic allocation | `rimea_10_pathfinding`, `rimea_11_exit_selection_*` |
| Verif.5.1 congestion | demos only | `rimea_12_evacuation_*`, `rimea_13_stairs*` |
| Verif.5.2 max flow | **measured here**: CFSM mean evacuation rate 60/60.9 s ≈ 0.99 p/s through a 1 m door, including walking time, under 1.33 p/s (this geometry, not the IMO 8×5 m room with 100 persons) | `rimea_04_flow_*` (fundamental-diagram flow tests) |
| Verif.1.1 pre-evacuation | no pre-movement parameter found in operational-model states; agents can be added at chosen times | `rimea_05_react*` |

Vadere's assertion machinery:

- CI runs every `Scenarios/ModelTests` scenario with `java -enableassertions` (`Tools/ContinuousIntegration/run_vadere_console_with_all_scenario_files.py:146-160`; `.gitlab-ci.yml:86-93`). A scenario passes if the process exits 0 within the timeout.
- Assertions come from test processors: `TestEvacuationTimeProcessor` (minimum/maximum bounds), `TestNumberOverlapsProcessor` (`overlaps <= maxOverlaps`, line 50), `TestPedestrianWaitingTimeProcessor` and others. Occurrence counts of processor type strings across `ModelTests`: 23 waiting-time, 8 pedestrian-evacuation-time, 4 evacuation-time, 2 service-time and 2 overlap test processors. The non-asserting `PedestrianOverlapProcessor` occurs 135 times, and each `FundamentalDiagram{A,B,C,D}Processor` occurs 10 times.
- Vadere's ODE models default to adaptive Dormand–Prince 4(5) with step 1e-4–1.0 and tolerances `1e-5` absolute / `1e-4` relative (`AttributesODEIntegrator.java:17-21`). Euler, RK4, DP853 and velocity Verlet are alternatives (`IntegratorFactory.java:23-47`). JuPedSim uses only fixed-step semi-implicit Euler. Köster, Treml and Gödel (2013) analyse why such fixed-step choices matter.

`Basis: source`

JuPedSim tests at the pinned revision are unit-level: 304 lines beginning with `TEST` in `libsimulator/test/*.cpp` and 311 `def test_` functions across 27 Python test files. A name search finds no RiMEA, IMO or ISO 20414 scenario suite. `Basis: source`

### 6. High-density behaviours no standard test constrains, and the trajectory data each needs

Helbing and Mukerji (2012):

- define a "crowd quake" as having "no systematic flow direction, but people are pushed around by fluctuating forces", with "crowd pressure (defined as density times variability of body movements)";
- quote Fruin: "At occupancies of about 7 persons per square meter the crowd becomes almost a fluid mass";
- note that "once the crowd density exceeds between 4 or 5 persons per square meter, congestion can build up quickly".

`Basis: documentation`

| Behaviour | Why no examined test constrains it (derived) | Trajectory data required |
|---|---|---|
| crowd turbulence / pressure `ρ·Var(v)` | TN 1822 tests stop at congestion and flow ceilings; no test asserts a pressure field or its spatial location | body-centre trajectories at ≥ 10–25 frames/s within the dense zone, at densities ≥ 4–7 m⁻², long enough to estimate local velocity variance; dense-crowd video tracking with occlusion handling |
| force-chain / domino falling | none of the four JuPedSim models represents falling, posture or contact-force chains; SFM contact forces exist but no test checks force magnitudes | trajectories plus fall events (time, location), ideally head and shoulder tracks; contact-force or pressure-mat data are rarely available |
| stop-and-go waves in congested queues | TN 1822 Verif.5.1 is qualitative | long trajectories along a queue axis; wave speed from space–time diagrams |
| model breakdown modes (overlap, gridlock, wall-crossing aborts) | no V&V test checks model integrity at high density; Vadere asserts overlap counts in only 2 scenarios | not field data: synthetic stress tests with assertions on overlap, gridlock and errors, sweeping `dt` and parameters (as in §2) |
| inflow/outflow counter-streams on a ramp (Duisburg geometry) | Verif.2.8 counter-flow is a room test at moderate density | bidirectional trajectories in a T/ramp geometry at high density |

### 7. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 | Source size: JuPedSim `libsimulator/src` (C++), of which `operational_models` | 11,785 and 3,350 lines (`wc -l`) | measured |
| L1 | PedPy `pedpy/` (Python), of which `methods/` | 10,200 and 4,412 lines | measured |
| L1 | Vadere `*.java` | 219,906 lines in 1,977 files | measured |
| L1 | Authoring and repair effort, agent token budgets | not measured | – |
| L2 | JuPedSim from-scratch Release build (`ninja -j16`, LTO on, 85 of 86 steps) | 1 min 51.7 s wall, 945 s user, 365 s sys; largest child RSS 2.49 GB | measured |
| L2 | Vadere (Maven) build | not measured | – |
| L3 | Geometry build and floor-field setup latency | not separated; not measured | – |
| L4 | Engine-only `iterate()` cost, 60 agents, 500 steps, two repeats | SFM 90–123, GCFM 87–100, CFSM 84–130, AVM 4.4–8.6 µs per agent-iteration | measured |
| L4 | Probe runs including Python-side metrics | 210–260 µs per agent-iteration (SFM/CFSM), 34–41 (AVM) | measured |
| L4 | Why AVM is ~10–20× cheaper | SFM, CFSM and GCFM query walls within a fixed 4 m every step (`wall_search_radius = 4.0`); AVM queries only within `wall_buffer + r` (0.3 m) | derived hypothesis, not profiled |
| L5 | Proof or certificate checking | – | known not to apply |
| L6 | `pyjupedsim` extension `.so` | 9,802,080 B; `libsimulator.a` 102,847,550 B; Rust `libfloorfield.a` 26,850,884 B | measured |
| L6 | Peak RSS of the batch driver, which spawns per-run processes | 34 MB for the driver; per-run RSS not separated | measured (partial) |
| L6 | Peak RSS of the measurement-method probe (simulation + re-implemented methods) | 68 MB (80 agents, free flow) to 506 MB (240 agents, 0.5 m bottleneck) | measured |

### 8. Comprehensibility, simplicity and validation coverage (C1–C2, V1–V4)

- **C1.** In velocity models the speed is an explicit function of a visible spacing, so a modeller can predict what a time-gap change does. In force models an outcome depends on the sum of several exponentials and the corner multiplicity of wall segments, which a modeller cannot predict from the parameter table. §3 shows such a non-local footgun: geometry topology (segments per vertex) changes forces. The SFM–CFSM difference in insertion checks (§1) is another hidden inconsistency. `Basis: derived`
- **C2.** One invariant, "agents do not interpenetrate each other or walls", is enforced by four different mechanisms: speed-to-zero (CFSM), force caps (GCFM), contact forces (SFM), and a global mesh-walk abort. A single post-step admissibility projection would make the invariant uniform without changing model laws: reject or clip any displacement that would create overlap. It would move the cost into a solver rather than remove it. This is a design hypothesis, not an upstream feature. `Basis: derived`
- **V1** (specification non-vacuity). No examined JuPedSim test asserts a quantitative crowd outcome against a reference. Vadere asserts bounds through test processors. **V2.** Cross-model differential runs (§2) are the cheapest discriminator found: they exposed the SFM trap and GCFM gridlock. **V3** (concurrency/crash). The JuPedSim update is sequential in one thread (`for` loop, `operational_decision_system.hpp:48`); not examined further. **V4** (field replay). No examined repository replays incident trajectories. NIST TN 1822 lists experimental datasets for component validation, and §6 lists what is missing. `Basis: source + derived`

## Boundaries

- **Not examined:**
  - PedPy execution. §4 numbers come from a re-implementation that approximates Voronoi cells on a lattice.
  - Vadere build or run.
  - ISO 20414 clauses 5–10 content (paywalled). The test-level mapping uses NIST TN 1822 instead, and the correspondence between TN 1822 tests and ISO 20414 sub-clauses is **unknown**.
  - The RiMEA guideline text. The RiMEA-to-IMO correspondence in the table is inferred from scenario names.
  - The JuPedSim C++ unit tests (`BUILD_TESTS=OFF`, because the configuration requires `pytest`).
  - CollisionFreeSpeedModelV2/V3 and WarpDriver behaviour.
  - Multi-floor geometries.
- **Unknown:**
  - The remaining 22 % of the SFM door-equilibrium force balance (§3). A non-unit floor-field direction `e0` or additional boundary segments from mesh splitting are candidates; neither was checked.
  - Whether GCFM's poor base-geometry performance persists with parameters calibrated in the GCFM paper. Only JuPedSim defaults were run (mass 1 kg).
  - Whether GCFM's zero force from wall endpoints (`generalized_centrifugal_force_model.cpp:314-316` returns 0 unless the closest point is an orthogonal projection) contributes to the wall-crossing aborts. Plausible; not isolated.
- **Known not to apply:** the §2 evacuation times are not IMO Test 4 results (different room and population), and the CFSM flow of 0.99 p/s is specific to `T = 1`, `v0 = 1.2` and `r = 0.2`.
- **Unsupported stronger conclusions:**
  - "SFM is unusable": no. Defaults plus one geometry produce the trap, and `v0`, `τ` or `obstacle_scale` changes remove it.
  - "CFSM is collision-free at any `dt`": no. 0.013 m overlap appeared at `dt = 0.1`.
  - "The Voronoi method is more accurate": the probe measures disagreement between methods, not accuracy.

## Evidence

Observation date for all source, execution and literature evidence: 2026-11-20 (UTC).

- **Source** (pinned revisions above):
  - jupedsim `libsimulator/src/`:
    - `operational_models/social_force_model/social_force_model.cpp:17-180`, `social_force_model.hpp` (cut-off and defaults), `social_force_model_state.hpp`;
    - `generalized_centrifugal_force_model/generalized_centrifugal_force_model.cpp:52-465`;
    - `collision_free_speed_model/collision_free_speed_model.cpp:41-167`;
    - `anticipation_velocity_model/anticipation_velocity_model.cpp:30-298`;
    - `operational_decision_system.hpp:38-68`;
    - `simulation.cpp:91-127,236-271`;
    - `geometry/location.cpp:180-208`;
    - `agent_view.hpp:37-47,131-152`;
    - `floorfield_routing_engine.hpp:17-21`.
  - jupedsim `python_bindings_jupedsim/*.cpp` (doc strings and defaults); `python_modules/jupedsim/jupedsim/simulation.py:78` (`dt` default 0.01).
  - pedpy `pedpy/methods/{density,speed,flow}_calculator.py`, `method_utils.py:478-`.
  - vadere:
    - `VadereState/.../AttributesODEIntegrator.java:17-21`;
    - `VadereSimulator/.../ode/IntegratorFactory.java:16-47`;
    - `.../processor/tests/TestNumberOverlapsProcessor.java:50`, `TestProcessor.java:25-44`, `TestEvacuationTimeProcessor.java:51-62`;
    - `Tools/ContinuousIntegration/run_vadere_console_with_all_scenario_files.py:115-200`;
    - `.gitlab-ci.yml:72-110`;
    - `Scenarios/ModelTests/**`.
- **Execution.** Support material:
  - `support/jps_probe.py` (scenario and metrics) and `support/jps_batch.py`, `jps_batch_ext.py` (the sweeps); raw results in `jps_batch_out.jsonl` and `jps_batch_ext_out.jsonl`;
  - `jps_summarize.py` produces `jps_summary.txt`;
  - single-agent probes `jps_sfm_single.py`, `jps_sfm_door.py` (with `jps_sfm_door_out.txt`) and `jps_gcfm_single.py`;
  - `jps_iterate_bench.py` with `jps_iterate_bench_out.txt`;
  - `fd_methods_probe.py` with `fd_methods_out.txt` and `fd_methods_time.txt`, plus the dumped per-configuration points `fd_cfg0.json` to `fd_cfg4.json`. Configurations run with `fd_methods_probe.py one <i> <out.json>` and are pooled with `fd_methods_probe.py pool <files>`.

  All run as `PYTHONPATH=<dir containing pyjupedsim*.so> python3 <script>`.
- **Normative and documentation:**
  - ISO 20414:2020 public preview (first edition 2020-11): table of contents and clause 1.
  - NIST TN 1822 full text: Table 1, IMO Test 4 text, Verif.5.2, and ERD/EPC/SC definitions.
  - Helbing & Mukerji 2012 full text: note 3, §3.4 and point 9.
  - DOIs verified through Crossref on the observation date:
    - Helbing–Molnár 1995: 10.1103/PhysRevE.51.4282;
    - HFV 2000: 10.1038/35035023;
    - Seyfried et al. 2005: 10.1088/1742-5468/2005/10/P10002;
    - Chraibi et al. 2010: 10.1103/PhysRevE.82.046111;
    - Helbing–Mukerji 2012: 10.1140/epjds7;
    - NIST TN 1822: 10.6028/NIST.TN.1822;
    - Tordeux et al. 2016: 10.1007/978-3-319-33482-0_29;
    - Kleinmeier et al. 2019 (Vadere): 10.17815/CD.2019.21;
    - Xu et al. 2021: 10.1016/j.trc.2021.103464;
    - Zhang et al. 2011: 10.1088/1742-5468/2011/06/P06004;
    - Steffen–Seyfried 2010: 10.1016/j.physa.2009.12.015;
    - Köster et al. 2013: 10.1103/PhysRevE.87.063305;
    - Chraibi et al. 2011: 10.3934/nhm.2011.6.425;
    - Wolinski et al. 2016: 10.1145/2980179.2982442;
    - Ronchi 2021: 10.1016/j.firesaf.2020.103020 (metadata only).

## Revalidation

1. **SFM door trap.** Takes about 1 s. Build `pyjupedsim` at the new revision and run `python3 support/jps_sfm_door.py corridor 1.0 0.8`. "STOPPED" at `x ≈ 7.66` means the trap persists. Then diff `social_force_model.cpp` and `agent_view.hpp::as_seen_from_agent`; any corner deduplication or force anisotropy changes the outcome.
2. **Time-step sensitivity.** `python3 support/jps_batch.py out.jsonl 32` takes about 10 min on 32 cores. Then `python3 support/jps_summarize.py out.jsonl` and compare against the §2 tables.
3. **Integrity semantics.** `grep -n "move_on_surface\|check_model_constraint" libsimulator/src/{operational_decision_system.hpp,geometry/location.cpp,simulation.cpp}`. If overlap checks move into `iterate()`, §1–§2 conclusions about tolerated overlap no longer hold.
4. **PedPy definitions.** Diff `pedpy/methods/*_calculator.py` from `0604d9a`. With `pandas`/`shapely` available, validate `fd_methods_probe.py` against PedPy itself on the dumped trajectories.
5. **Vadere.** Recount test processors with `grep -rhoE 'processor\.tests\.[A-Za-z]+' Scenarios/ModelTests | sort | uniq -c`.
