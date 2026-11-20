# Large-Angle GZ Righting Hydrostatics, Free-Surface Tank Sloshing Moments, Parametric Roll Resonance, and Cryogenic LNG Rollover Boil-Off

## Summary

Ship stability computers, offshore ballast-transfer controllers, and cryogenic Liquefied Natural Gas (LNG) terminal/carrier relief systems rely on coupled hydrostatics, free-surface fluid dynamics, and multi-component cryogenic equations of state where small-angle, linear, or single-phase abstractions break down catastrophically. Direct source inspection of four upstream engineering solvers (`capytaine`, `MSS`, `DualSPHysics`, and `CoolProp`), paired with regulatory standards (`IMO Resolution MSC.267(85)` / 2008 IS Code and `IMO MSC.1/Circ.1627`) and standalone IEEE-754 double-precision numerical probes, establishes five governing findings:

1. **Large-Angle $GZ(\phi)$ Breakdown and Silent Mesh Hydrostatics Bugs (`capytaine` & `MSS`):** Linear restoring models (`MSS` `Gmtrx.m` and `hydroVessel.m:137`, `- vessel.G * eta`) and wall-sided righting formulas ($\sin\phi(GM_0 + \frac{1}{2}BM_0\tan^2\phi)$) fail severely once deck-edge immersion occurs. On a flared non-wall-sided hull ($B_{\text{wl}} = 32\text{ m}, D = 16.5\text{ m}, T = 10\text{ m}, GM_0 = 1.20\text{ m}$), exact constant-displacement $GZ(\phi)$ peaks at $0.86\text{ m}$ ($27^\circ$) and turns negative ($-0.106\text{ m}$, capsize) by $45^\circ$, whereas the wall-sided formula predicts $+4.15\text{ m}$ ($+4002\%$ non-conservative sign reversal) and linear `Gmtrx` predicts $+0.94\text{ m}$. In `capytaine`, direct source inspection revealed three concrete hydrostatic hazards: (a) `AbstractMesh.immersed_part(free_surface=...)` (`abstract_meshes.py:426`) hardcodes `origin=(0, 0, 0)` instead of `(0, 0, free_surface)`, ignoring non-zero draft/wave-crest elevations; (b) `transversal_metacentric_radius` and `longitudinal_metacentric_radius` (`hydrostatics.py:79,86`) integrate `y**2` and `x**2` about the coordinate origin rather than the waterplane centroid `(x_f, y_f)`, inflating $BM_T$ by $+A_{wp} y_f^2 / \nabla$ ($+12.0\%$ for $y_f = 2\text{ m}$ on a $20\text{ m}$-beam barge); and (c) `SurfaceIntegralsMixin.volume` (`surface_integrals.py:41-55`) silently averages `(Vx, Vy, Vz)` without verifying $|V_x - V_z| \approx 0$, allowing 2% flipped bottom panel normals to corrupt $V$ ($-1.33\%$), $A_{wp}$ ($-4.00\%$), and $\mathrm{CoB}_z$ without warning.
2. **Cubic Width Scaling of Free-Surface Moments and `2008 IS Code` Area Failures:** Because slack tank transverse inertia $i_T = \frac{1}{12} l_t b_t^3$ scales as $b_t^3$, adding a single longitudinal centerline baffle reduces free-surface metacentric loss $\Delta GM = \rho_t i_T / \Delta$ by $4\times$. In a standalone probe of a top-heavy car-carrier hull ($GM_0 = 0.65\text{ m}$), opening 4 unbaffled ballast tanks simultaneously (the *MV Cougar Ace* 2006 mechanism) drives $GM_{\text{eff}} = -0.229\text{ m}$ and a $12.3^\circ$ angle of loll; crucially, even with 4 *baffled* tanks where $GM_{\text{eff}} = +0.193\text{ m} > 0.15\text{ m}$ passes the linear GM floor, the `2008 IS Code` large-angle energy criterion $e_{30\text{--}40} = 0.0006 < 0.030\text{ m}\cdot\text{rad}$ still fails.
3. **Mathieu Parametric Roll and Opposite-Sign Integrator Artifacts (`IMO MSC.1/Circ.1627` & `MSS`):** When head/following swell modulates waterplane stiffness at $\omega_e \approx 2\omega_0$ above the damped Ince–Strutt threshold $\delta GM / GM_m > 4\zeta$, fixed-step time integrators induce opposite safety errors: `MSS`'s `euler2.m` (whose header claims "Euler's 2nd-order method" while line 17 implements 1st-order Forward Euler `xnext = x + h*xdot`) injects spurious energy and triggers $35.6^\circ$ **false parametric roll** at $\Delta t = 0.5\text{ s}$ on a physically stable sub-critical hull ($\mu = 0.20 < 0.24$, true $3.0^\circ$), whereas 1st-order Backward Euler injects artificial damping that suppresses a genuine $41.0^\circ$ super-critical parametric roll ($\mu = 0.45$, far above the IMO $25^\circ$ Level-2 `C2` threshold) down to $9.37^\circ$ at $\Delta t = 0.2\text{ s}$ and $3.00^\circ$ at $\Delta t = 0.5\text{ s}$ (**dangerous false stability**).
4. **Weakly Compressible SPH Sloshing Constraints (`DualSPHysics`):** `DualSPHysics` computes violent nonlinear tank-sloshing loads via 32-bit `float` Monaghan–Tait EOS (`FunSphEos.h:38-40`, $\gamma = 7$) requiring artificial sound speed $c_0 \ge 10 v_{\max}$ ($\Delta\rho/\rho_0 \le 1\%$), driving explicit CFL timesteps ($\Delta t \le \mathrm{CFL}\cdot h/c_0$, `CFL = 0.2`) to microsecond scales. Fourtakas et al. (2019) density diffusion (`DDT_DDT2`, `JSphCpu.cpp:933-940`) subtracts the hydrostatic density profile to stop free-surface slump, is explicitly disabled against DBC boundaries (`deltap1 = boundp2 ? FLT_MAX : ...`) and floating particles (`JSphCpu.cpp:777`), and doubles interaction passes under 2nd-order Symplectic time stepping (`JSphCpuSingle.cpp:897-932`) versus Verlet (`:873-888`).
5. **Cryogenic LNG Helmholtz Flash Pathologies (`CoolProp`) and Stratified Rollover Superheat Spikes:** In `CoolProp`'s GERG-2008 Helmholtz mixture engine (`ReducingFunctions.cpp:528-555`, `VLERoutines.cpp:2172-2335`), cryogenic LNG flash evaluations at $80\text{--}115\text{ K}$ expose removable $0/0$ singularities when two trace components have zero mole fraction, local Newton convergence onto non-physical $dp/d\rho > 0$ roots yielding $\phi_i \in \{0, \infty\}$ (`110 K` n-pentane trials), unstable middle-branch density roots ($dp/d\rho < 0$), and GDEM overflow ($\ln \phi_i \sim O(10^4)$). Physically, in a Klosek–McKinley two-layer `50,000 m^3` La-Spezia-scale probe, preferential $\mathrm{N}_2$ boil-off ($-0.5\text{ mol}\%$) *reduces* top-layer density by $-1.31\text{ kg/m}^3$ (nitrogen-induced auto-stratification), whereas stronger initial stratification ($\Delta\rho_0 = 5.36\text{ vs }2.47\text{ kg/m}^3$) delays rollover ($434.7\text{ vs }83.9\text{ h}$) while trapping more bottom superheat ($+4.65\text{ K} / 164.4\text{ GJ}$), amplifying the 2-hour rollover BOG spike from $46.4\times$ to $127.8\times$ normal boil-off ($162.4\text{ vs }1.27\text{ t/h}$).

## Applicability

These findings govern:

- **Maritime Stability & Sloshing Software:** Boundary-element potential-flow hydrostatic/hydrodynamic preprocessors (`capytaine`), 6-DoF marine craft maneuvering and seakeeping simulators (`MSS`), GPU/CPU Smoothed Particle Hydrodynamics tank-sloshing solvers (`DualSPHysics`), and onboard loading computers enforcing `IMO Resolution MSC.267(85)` (2008 IS Code) and `IMO MSC.1/Circ.1627` (Second Generation Intact Stability Criteria).
- **Cryogenic LNG Custody & Rollover Thermodynamic Engines:** Multi-component Helmholtz free-energy equation-of-state libraries (`CoolProp` GERG-2008 / Kunz–Wagner 2012) and lumped/CFD double-diffusive stratified rollover predictors (Bates & Morrison 1997) applied to $\mathrm{CH}_4\text{--}\mathrm{C}_2\mathrm{H}_6\text{--}\mathrm{C}_3\mathrm{H}_8\text{--}\mathrm{N}_2$ mixtures near $80\text{--}125\text{ K}, 0.1\text{--}12\text{ MPa}$.
- **Pinned Upstream Revisions Examined via Direct Source Inspection:**
  - `capytaine/capytaine` @ `b81111ae1a4e4312efbb00023b2dd0837aa312b1` (`src/capytaine/bodies/hydrostatics.py`, `src/capytaine/meshes/abstract_meshes.py`, `surface_integrals.py`).
  - `cybergalactic/MSS` @ `22142414efa679f3926176eac36dae29e2ab93d1` (`LIBRARY/modeling/Gmtrx.m`, `gvect.m`, `LIBRARY/numericalMethods/euler2.m`, `CRAFT/hydroVessel.m`, `HYDRO/vessels_capytaine/S175/S175.md`, `mssExamples/exShipHydrostatics.m`).
  - `DualSPHysics/DualSPHysics` @ `ef3721a861fda961f0e2f9ec4cd317b19de99086` (`src/source/FunSphEos.h`, `JSph.cpp`, `JSphCpu.cpp`, `JSphCpuSingle.cpp`).
  - `CoolProp/CoolProp` @ `55db41ea9355b5f988f24e30518387a4597f14a8` (`src/Backends/Helmholtz/ReducingFunctions.h`, `ReducingFunctions.cpp`, `VLERoutines.cpp`, `FlashRoutines.cpp`).
- **Subject Relationships & Observation Boundaries:** `MSS` consumes frequency-domain hydrodynamic tables generated by `capytaine` (e.g., `MSS/HYDRO/vessels_capytaine/S175/s175.mat`, documented in `S175.md`) for 6-DoF time-domain vessel motion; `DualSPHysics` supplies high-fidelity nonlinear internal tank sloshing loads where potential-flow BEM cannot model breaking waves or baffles; `CoolProp` supplies the multi-component cryogenic fluid densities, fugacities, and flash enthalpies driving LNG cargo-tank stratification and rollover boil-off envelopes. Upstream source structure and bugs are verified directly (`Basis: source`); numerical stability curves, Mathieu integrator error tables, and two-layer rollover projections were measured in standalone Python 3.13 IEEE-754 double-precision probes (`Basis: execution (standalone numerical probe)`), not compiled GPU/C++/MATLAB runs of the four upstream binaries.

## Findings

### 1. Large-Angle Righting-Arm Hydrostatics and Panel-Mesh Failure Modes

#### 1.1 Exact Non-Wall-Sided $GZ(\phi)$ vs. Wall-Sided and Linear Restoring Approximations

For a floating vessel of fixed displacement volume $\nabla$, heel angle $\phi$, and vertical center of gravity $KG$, the static righting lever $GZ(\phi)$ equals the horizontal separation between the instantaneous immersed center of buoyancy $B(\phi) = (y_B(\phi), z_B(\phi))$ (re-solved for equilibrium draft $d_{\text{wl}}(\phi)$ such that submerged volume stays equal to $\nabla$) and $G = (0, KG)$:

$$GZ(\phi) = y_B(\phi)\cos\phi + (z_B(\phi) - KG)\sin\phi = KN(\phi) - KG\sin\phi$$

Two widespread engineering simplifications break down outside small heel angles:
1. **Linear metacentric restoring (`MSS` `Gmtrx.m:35-38`, `hydroVessel.m:137`):** $GZ_{\text{lin}}(\phi) = GM_0\,\phi$, where $GM_0 = KB + BM_0 - KG$ and $BM_0 = I_T / \nabla$. `MSS` `hydroVessel.m:137` evaluates `- vessel.G * eta` with a constant upright $6 \times 6$ stiffness matrix `G` computed about the center of flotation and transformed via `Hmtrx` (`Gmtrx.m:38-41`), while `gvect.m:22-28` applies nonlinear $\sin\phi, \cos\phi$ restoring only for fully submerged bodies with fixed $r_{bB}$.
2. **Wall-sided formula:** $GZ_{\text{ws}}(\phi) = \sin\phi\left(GM_0 + \frac{1}{2}BM_0\tan^2\phi\right)$, exact only while sides remain vertical and neither bilge emerges nor deck edge submerges.

Basis: execution (standalone Python constant-displacement 2D polygon-clipping hydrostatics probe on a non-wall-sided flared hull: $B_{\text{keel}} = 22\text{ m}$, $B_{\text{chine}} = 30\text{ m}$ at $z = 3.5\text{ m}$, $B_{\text{deck}} = 34\text{ m}$ at $D = 16.5\text{ m}$, upright draft $T = 10.0\text{ m}$, $B_{\text{wl}} = 32.0\text{ m}$, $A_{\text{sub}} = 292.5\text{ m}^2$, $KB = 5.246\text{ m}$, $BM_0 = 9.336\text{ m}$, $KG = 13.382\text{ m}$, $GM_0 = 1.200\text{ m}$).

| Heel $\phi$ (deg) | Exact $GZ(\phi)$ (m) | Wall-Sided $GZ_{\text{ws}}(\phi)$ (m) | Linear $GM_0 \phi$ (m) | Wall-Sided Error | Deck Edge Immersed (DEI) |
| ---: | ---: | ---: | ---: | ---: | :---: |
| 0 | 0.0000 | 0.0000 | 0.0000 | +0.0% | No |
| 10 | 0.2342 | 0.2336 | 0.2094 | -0.3% | No |
| 20 | 0.6274 | 0.6219 | 0.4189 | -0.9% | No |
| 25 | 0.8441 | 0.9361 | 0.5236 | **+10.9%** | **Yes** |
| 30 | 0.8072 | 1.3780 | 0.6283 | **+70.7%** | Yes |
| 35 | 0.5989 | 2.0010 | 0.7330 | **+234.1%** | Yes |
| 40 | 0.2823 | 2.8839 | 0.8378 | **+921.7%** | Yes |
| 45 | **-0.1063** | +4.1492 | +0.9425 | **-4002.4% (sign flip)** | Yes |
| 60 | **-1.6146** | +13.1665 | +1.2566 | **-915.5% (sign flip)** | Yes |

Before deck-edge immersion ($\phi \le 20^\circ$), linear `Gmtrx` underestimates righting arm by $-33.2\%$ ($0.419\text{ vs }0.627\text{ m}$) because it omits the quadratic waterplane flare stiffening $\frac{1}{2}BM_0 \tan^2\phi\sin\phi$. Once the starboard deck edge submerges between $20^\circ$ and $25^\circ$, exact $GZ(\phi)$ peaks at $0.86\text{ m}$ ($27^\circ$) and crosses zero (angle of vanishing stability $\phi_v$) at $43.8^\circ$; both the wall-sided formula ($+4.15\text{ m}$ at $45^\circ$) and linear `Gmtrx` ($+0.94\text{ m}$) predict vigorous positive restoring righting moments in the capsize region.

#### 1.2 Verified Hydrostatic Pathologies in `capytaine` Source Code

Direct inspection of `capytaine/capytaine@b81111ae1a4e4312efbb00023b2dd0837aa312b1` reveals three concrete source-level hydrostatic invariants and bugs (`Basis: source + execution (standalone replica)`):

1. **Hardcoded `origin=(0, 0, 0)` Ignoring `free_surface` in `AbstractMesh.immersed_part` (`src/capytaine/meshes/abstract_meshes.py:405-429`):**
   ```python
   def immersed_part(self, free_surface=0.0, *, sea_bottom=None, water_depth=None) -> AbstractMesh:
       ...
       if (free_surface - water_depth <= self.z_span[0]
           and self.z_span[1] <= free_surface):  # Already clipped
           return self
       clipped = self.clipped(origin=(0, 0, 0), normal=(0, 0, 1))
       if water_depth < np.inf:
           clipped = clipped.clipped(origin=(0, 0, free_surface-water_depth), normal=(0, 0, -1))
       return clipped
   ```
   Line 426 clips against `z = 0` regardless of `free_surface`, even though line 424 checks `self.z_span[1] <= free_surface` and line 428 uses `free_surface - water_depth`. Evaluating displaced hull drafts or wave-crest immersion by passing `free_surface != 0.0` silently clips at the wrong waterline unless the caller manually translates the mesh first.
2. **Parallel-Axis Origin Error in Metacentric Radii (`src/capytaine/bodies/hydrostatics.py:76-88`):**
   ```python
   def transversal_metacentric_radius(self):
       immersed_mesh = self.mesh.immersed_part()
       inertia_moment = immersed_mesh.waterplane_integral(immersed_mesh.quadrature_points[0][:,:,1]**2)
       return inertia_moment / self.disp_volume
   ```
   Both `transversal_metacentric_radius` (`y**2`, line 79) and `longitudinal_metacentric_radius` (`x**2`, line 86) compute second moments about `(0, 0)` instead of `(x_f, y_f)` (`self.waterplane_center`). By the parallel-axis theorem ($I_{\text{origin}} = I_{\text{centroid}} + A_{wp} y_f^2$), an asymmetric or heeled waterplane with $y_f = 2.0\text{ m}$ on a $100 \times 20 \times 5\text{ m}$ barge overpredicts $BM_T$ by **$+12.0\%$** ($7.4667\text{ m}$ vs. true $6.6667\text{ m}$), and any longitudinally asymmetric ship ($x_f = \mathrm{LCF} \ne 0$) incurs a systematic $+A_{wp} x_f^2/\nabla$ bias in $BM_L$ and $GM_L$. (In contrast, `_rigid_body_hydrostatic_stiffness_coef` at lines 162 and 171 properly subtracts the rotation center `(y - yc)**2` and `(x - xc)**2`.)
3. **Silent Averaging Over Non-Watertight or Flipped Panel Normals (`src/capytaine/meshes/surface_integrals.py:41-88`):**
   `volumes` computes $(V_x, V_y, V_z) = (\iint x n_x\,dS, \iint y n_y\,dS, \iint z n_z\,dS)$, `volume` returns `np.mean(self.volumes)` with **no divergence consistency check**, `waterplane_area` computes $-\iint n_z\,dS$, and `center_of_buoyancy` computes $\frac{1}{2V}\iint x_k^2 n_k\,dS$. If just `2%` of bottom panels on a $100 \times 20 \times 5\text{ m}$ barge have inverted normals, $(V_x, V_y, V_z) = (10000, 10000, 9600)\text{ m}^3$ disagree by $400\text{ m}^3$, yet `volume` silently returns $9866.7\text{ m}^3$ ($-1.33\%$), `waterplane_area` drops $-4.00\%$ to $1920.0\text{ m}^2$, and $\mathrm{CoB}_z$ shifts from $-2.500\text{ m}$ to $-2.432\text{ m}$.

### 2. Free-Surface Ballast Transfer Loss, `2008 IS Code` Envelopes, and SPH Sloshing (`DualSPHysics`)

#### 2.1 Multi-Tank Ballast Transfer Ordering and the *MV Cougar Ace* Mechanism

A partially filled (slack) tank of liquid density $\rho_t$ and free-surface transverse moment of inertia $i_T = \frac{1}{12} l_t b_t^3$ shifts its internal liquid center of gravity horizontally upon heel, reducing effective metacentric height by $\Delta GM_{\text{FS}} = \sum_k \rho_{t,k} i_{T,k} / \Delta$. Because $i_T \propto b_t^3$, dividing a tank into $n$ equal longitudinal compartments reduces its free-surface moment by $n^2$ ($4\times$ for a single centerline baffle). During mid-ocean ballast-water exchange—such as the July 23, 2006 Pure Car/Truck Carrier *MV Cougar Ace* casualty south of the Aleutian Islands (investigated by the Maritime and Port Authority of Singapore), where multiple double-bottom and wing tanks were simultaneously empty or slack while high-deck vehicle cargo kept $KG$ elevated—combined vertical $KG$ rise and stacked $\Delta GM_{\text{FS}}$ drive $GM_{\text{eff}} < 0$, causing sudden flop to an angle of loll ($\sim 60^\circ$ in *MV Cougar Ace*).

Under `IMO Resolution MSC.267(85)` (`2008 IS Code` Part A, §2.2), intact vessels must satisfy *all* five simultaneous criteria: (i) $GM_{\text{eff}} \ge 0.15\text{ m}$, (ii) $e_{0\text{--}30} = \int_0^{30^\circ} GZ\,d\phi \ge 0.055\text{ m}\cdot\text{rad}$, (iii) $e_{0\text{--}40} \ge 0.090\text{ m}\cdot\text{rad}$, (iv) $e_{30\text{--}40} \ge 0.030\text{ m}\cdot\text{rad}$, and (v) $GZ(\phi \ge 30^\circ) \ge 0.20\text{ m}$ with $\phi_{\max} \ge 25^\circ$. Evaluating a top-heavy PCTC variant of the §1.1 hull ($L = 140\text{ m}, \nabla = 40{,}950\text{ m}^3$, solid $GM_0 = 0.65\text{ m}$, four ballast tanks each $l_t = 24\text{ m}, b_t = 13\text{ m}$, $\Delta GM_{\text{unbaffled}} = 0.107\text{ m/tank}$, $\Delta GM_{\text{baffled}} = 0.027\text{ m/tank}$) illustrates why linear $GM_{\text{eff}}$ alone is an unsafe sufficiency gate (`Basis: execution (standalone numerical probe)`):

| Ballast Transfer State (Top-Heavy PCTC, Solid $GM_0 = 0.65\text{ m}$) | $GM_{\text{eff}}$ (m) | $e_{0\text{--}30}$ ($\ge 0.055$) | $e_{0\text{--}40}$ ($\ge 0.090$) | $e_{30\text{--}40}$ ($\ge 0.030$) | $GZ_{\max}$ (m) | Loll Angle | `2008 IS Code` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| 0 slack (intact solid) | +0.650 | +0.1566 | +0.2030 | +0.0464 | 0.614 | 0.0° | **PASS** |
| 1 slack unbaffled (sequential, $+\Delta KG = 0.12\text{ m}$) | +0.423 | +0.1261 | +0.1498 | **+0.0236** | 0.516 | 0.0° | **FAIL** ($e_{30\text{--}40}$) |
| 4 slack baffled (simultaneous, $+\Delta KG = 0.35\text{ m}$) | +0.193 | +0.0953 | +0.0960 | **+0.0006** | 0.418 | 0.0° | **FAIL** ($e_{30\text{--}40}$) |
| 4 slack unbaffled (simultaneous, $+\Delta KG = 0.45\text{ m}$) | **-0.229** | **+0.0388** | **-0.0027** | **-0.0415** | 0.241 | **12.3°** | **FAIL (ALL)** |

Even in the moderate-stability hull ($GM_0 = 1.20\text{ m}$), 4 simultaneous unbaffled slack tanks retain $GM_{\text{eff}} = +0.321\text{ m} > 0.15\text{ m}$ yet fail `2008 IS Code` ($e_{30\text{--}40} = 0.0134 < 0.030\text{ m}\cdot\text{rad}$), while 4 *baffled* tanks pass ($e_{30\text{--}40} = 0.0556$) and sequential 1-tank exchange passes with large margin ($e_{30\text{--}40} = 0.0786$).

#### 2.2 Nonlinear Tank Sloshing Dynamics in `DualSPHysics`

Static free-surface corrections assume quasi-static flat internal waterplanes and vanish near tank-sloshing resonance ($\omega_1 = \sqrt{\frac{\pi g}{b_t}\tanh(\frac{\pi h_f}{b_t})}$), where standing bores, roof impacts, and baffle vortex shedding generate large dynamic phase-lagged overturning moments. Inspecting `DualSPHysics@ef3721a861fda961f0e2f9ec4cd317b19de99086` establishes the exact numerical controls and trade-offs (`Basis: source`):

- **Weakly Compressible Tait EOS in `float32` (`src/source/FunSphEos.h:38-47`, `JSph.cpp:1500`):** Pressure is computed as $P(\rho) = B\left((\rho/\rho_0)^\gamma - 1\right)$ with $\gamma = 7$ and $c_0 = \sqrt{\gamma B / \rho_0}$. To bound compressibility error $|\Delta\rho/\rho_0| \approx M^2 \le 1\%$, users must set $c_0 \ge 10 v_{\max}$ (`CoefSound`), which tightens the explicit acoustic CFL timestep $\Delta t \le \mathrm{CFL} \cdot h / c_0$ (default `CFL = 0.2`, `JSph.cpp:652,961`) during high-velocity liquid-roof impacts.
- **Density Diffusion Terms (`src/source/JSphCpu.cpp:777,923-940`):** Raw WCSPH suffers severe high-frequency acoustic pressure noise during sloshing impacts. `DualSPHysics` implements Molteni & Colagrossi (2009) (`DDT_DDT`, `:924-931`, diffuses raw $\rho_a/\rho_b - 1$) and Fourtakas et al. (2019) (`DDT_DDT2` / `DDT_DDT2Full`, `:933-940`, default `DDTValue = 0.1`, `JSph.cpp:739`), which subtracts the hydrostatic density differential $\Delta \rho_{\text{hyd}} = \rho_0\left((1 + \frac{\rho_0 g \Delta z}{B})^{1/\gamma} - 1\right)$ to prevent artificial free-surface slump. Critically, `JSphCpu.cpp:939` suppresses Fourtakas DDT against boundary particles (`deltap1 = boundp2 ? FLT_MAX : ...`, annotated `//-blocks it makes it boil - bloody DBC`) and `:777` disables DDT on floating particles—making **modified Dynamic Boundary Conditions (`mDBC`, `JSph.cpp:716,897-903`, `JSphCpu.cpp:953-965` with `MDBC2_NoPen` penetration guard)** essential for accurate sloshing tank-wall pressure peaks and baffle damping loads.
- **Verlet vs. Symplectic Integration & Rigid-Body Coupling (`src/source/JSphCpuSingle.cpp:873-960`):** `ComputeStep_Ver` (`:873-888`) executes one neighbor interaction pass per step (cheaper, lower accuracy on resonant tank sloshing), whereas `ComputeStep_Sym` (`:897-932`) executes a 2nd-order symplectic predictor–corrector with two full `MdbcBoundCorrection` + `Interaction_Forces` + `RunCellDivide` passes per timestep and `SymplecticDtPre = min(dt_p, dt_c)`, coupling fluid-to-tank-wall/floating forces via `FtPartsSumAce` / `FtComputeAceVel` / optional Project Chrono (`:946-958`).

### 3. Parametric Roll Mathieu Resonance (`IMO MSC.1/Circ.1627`) and Integrator Artifacts

Container vessels (such as the `S175` hull packaged in `MSS/HYDRO/vessels_capytaine/S175/s175.mat`) and Ro-Ro hulls combine pronounced bow flare with flat wide transom sterns. When a head or following wave of wavelength $\lambda \approx L_{pp}$ passes along the hull, a wave crest amidships submerges the narrow midship parallel body while raising bow flare and transom stern out of the water, collapsing waterplane inertia $I_T$; half a wave period later, a trough amidships submerges the flared ends, spiking $I_T$. The resulting time-varying metacentric height $GM(t) = GM_m + \delta GM \cos(\omega_e t)$ excites unforced roll via a damped nonlinear Mathieu–Duffing equation:

$$\ddot{\phi} + 2\zeta\omega_0 \dot{\phi} + \gamma_d \dot{\phi}|\dot{\phi}| + \omega_0^2\left(1 + \mu\cos(\omega_e t)\right)\phi - c_3 \phi^3 = 0, \qquad \mu = \frac{\delta GM}{GM_m}$$

At principal parametric resonance ($\omega_e \approx 2\omega_0$, i.e., encounter period $T_e \approx T_\phi / 2$), Floquet analysis of the linearized system gives the first Ince–Strutt instability tongue threshold $\mu_{\text{crit}} = 4\zeta$. Under `IMO MSC.1/Circ.1627` (2020), vessels are assessed hierarchically:
- **Level 1 (`PR-L1`):** Deterministic threshold comparing $\delta GM / GM_c$ against a ship-geometry standard $R_{\text{PR}}$ across a steepness-prescribed regular wave.
- **Level 2 (`PR-L2`):** Passes if either $C_1 = \sum_{i=1}^{16} W_i C_i \le 0.06$ (16 scatter-table wave cases checking parametric resonance conditions) **or** $C_2 \le 0.025$ (long-term weighted probability that simulated roll exceeds $25^\circ$ across speeds, headings, and wave states).

#### 3.1 Integrator False-Stability vs. False-Instability Probe

Inspecting `MSS/LIBRARY/numericalMethods/euler2.m:1-17` reveals a classic naming hazard: the file header describes `"Euler's 2nd-order method"`, while line 17 executes 1st-order Forward Euler `xnext = x + h*xdot;`. Meanwhile, `MSS/CRAFT/SIMhydroVessel.m:126` integrates `hydroVessel` using fixed-step `rk4.m`, whereas implicit stiff solvers (e.g., Backward Euler / BDF-1) are frequently employed in coupled co-simulations. Probing all four fixed-step integrators on the nonlinear Mathieu–Duffing equation ($T_0 = 24.0\text{ s}$, $\omega_0 = 0.2618\text{ rad/s}$, $\zeta = 0.06 \implies \mu_{\text{crit}} = 0.24$, $\omega_e = 2\omega_0$, $c_3 = 0.65\omega_0^2$, $\phi(0) = 3.0^\circ$, $T_{\text{end}} = 240\text{ s}$) exposes **opposite-sign stability falsification** (`Basis: execution (standalone numerical probe)`):

| Physical Regime & Reference (`RK4, dt=0.01 s`) | $\Delta t$ (s) | `RK4` max $|\phi|$ | Forward Euler (`MSS euler2.m`) | Backward Euler (`BDF-1`) | Symplectic Velocity-Verlet | Safety Verdict |
| :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| **Sub-Critical ($\mu = 0.20 < 0.24$)** | 0.2 | 3.00° | 5.66° | 3.00° | 3.00° | Forward Euler amplifies stable hull |
| *Physically STABLE (true: 3.00°)* | 0.5 | 3.00° | **35.64°** | 3.00° | 3.00° | **False Parametric Roll** in Forward Euler |
| | 1.0 | 3.00° | **90.00° (capsize)** | 3.00° | 3.00° | Spurious energy $|1 + i\omega\Delta t|^2 > 1$ |
| **Super-Critical ($\mu = 0.38 > 0.24$)** | 0.2 | 17.53° | 41.51° | **3.16°** | 17.71° | **False Stability** in Backward Euler |
| *Physically UNSTABLE (true: 17.53°)* | 0.5 | 17.52° | 49.73° | **3.00°** | 18.18° | Artificial damping suppresses resonance |
| **Severe Super-Critical ($\mu = 0.45 > 0.24$)** | 0.2 | 41.02° | 46.50° | **9.37°** | 41.22° | **Backward Euler falsely passes IMO 25° limit!** |
| *Exceeds IMO 25° C2 limit (true: 41.03°)* | 0.5 | 41.02° | 52.69° | **3.00°** | 41.54° | Complete masking of $41^\circ$ resonance |
| | 1.0 | 41.01° | **90.00° (capsize)** | **3.00°** | 42.82° | `RK4` / Symplectic preserve true threshold |

Even at $\Delta t = 0.2\text{ s}$ ($1/120$ of the natural roll period!), 1st-order Backward Euler masks a $41.0^\circ$ IMO-failing parametric roll into a benign $9.37^\circ$ oscillation because its amplification factor $|1/(1 - i\omega\Delta t)| \approx 1 - \frac{1}{2}\omega^2\Delta t^2$ adds artificial damping $\zeta_{\text{num}} \approx \frac{1}{2}\omega_0 \Delta t$, shifting the effective Mathieu threshold upward by $\Delta\mu_{\text{crit}} \approx 2\omega_0\Delta t$.

### 4. Cryogenic LNG Multi-Component Helmholtz EOS (`CoolProp`) and Stratified Rollover Boil-Off

#### 4.1 GERG-2008 Multi-Fluid Helmholtz Architecture and Cryogenic Flash Failure Modes in `CoolProp`

Custody transfer and rollover density predictions for LNG ($\mathrm{CH}_4\text{--}\mathrm{C}_2\mathrm{H}_6\text{--}\mathrm{C}_3\mathrm{H}_8\text{--}\mathrm{N}_2$ near $105\text{--}120\text{ K}$) require $\pm 0.1\%$ liquid density fidelity (Kunz & Wagner 2012, `ISO 20765-2` GERG-2008), because stratification density differences of only $1\text{--}4\text{ kg/m}^3$ ($\sim 0.2\text{--}0.9\%$ of $\rho \approx 450\text{ kg/m}^3$) govern rollover timing. In `CoolProp@55db41ea9355b5f988f24e30518387a4597f14a8` (`src/Backends/Helmholtz/ReducingFunctions.h:198-231`, `ReducingFunctions.cpp:245-560`), GERG-2008 evaluates reduced Helmholtz energy $\alpha(\delta, \tau, \bar{x}) = \alpha^0 + \sum_i x_i \alpha_i^r(\delta, \tau) + \Delta\alpha^r(\delta, \tau, \bar{x})$ with $\delta = \rho / \rho_r(\bar{x}), \tau = T_r(\bar{x})/T$ via asymmetric binary reducing terms $f_{ij}(x) = x_i x_j \frac{x_i + x_j}{\beta_{ij}^2 x_i + x_j}$.

Direct inspection of `CoolProp`'s Helmholtz mixture VLE/flash solvers (`VLERoutines.cpp` and `ReducingFunctions.cpp`) documents five real cryogenic numerical failure modes that engineers must guard against (`Basis: source`):

1. **Removable $0/0$ Singularity on Zero Trace Components (`ReducingFunctions.cpp:528-555`):** When an LNG composition vector includes absent trace species ($x_i = x_{N-1} = 0$, e.g., weathered or pure-methane heels in a 6-component LNG schema), the denominator $\beta_{ij}^2 x_i + x_j$ vanishes; `CoolProp` intercepts this explicitly with `both_mole_fractions_zero(xk, xN)` (`:538,549`), noting that algebraically equivalent derivative forms still differ by 1 ULP on ~30% of compositions (`:531-534`).
2. **Spurious $dp/d\rho > 0$ Local Newton Roots at Cryogenic LNG Temperatures (`VLERoutines.cpp:2172-2182`):** For a near-pure $n$-pentane stability trial at $110\text{ K}$ under GERG-2008 (far below $n$-pentane's $143.5\text{ K}$ triple point), local Newton can converge onto a non-physical root that *still satisfies mechanical stability* ($dp/d\rho \approx 7.5 \times 10^{13} > 0$) yet produces fugacity coefficients $\phi_i = 0$ or $\infty$, poisoning Michelsen tangent-plane-distance (TPD) trials with `NaN`. `CoolProp` enforces `finite_fugacity_coefficients(phase)` (`:2176-2182`) alongside `mechanically_stable(phase)` (`:2167-2170`) and warm-start branch-jump limits (`max_jump = 2.0`, `:2244,2262`).
3. **Unstable Middle-Branch Density Root ($dp/d\rho < 0$) and Subcooled 80 K LNG Fallback (`VLERoutines.cpp:2211-2238`):** When `calc_rhomolar_max_bound()` underestimates true liquid density, `solver_rho_Tp_global` can land on the mechanically unstable middle spinodal branch ($dp/d\rho < 0$), flipping two-phase feeds to false "stable" single-phase; conversely, at $80\text{ K}, 1\text{ bar}$ on subcooled $\mathrm{N}_2/\mathrm{C}_1/\mathrm{C}_2/\mathrm{C}_3$ LNG (`:2229`), both phase-specified liquid/gas solves can throw, requiring careful fallback to preserve a valid single-phase liquid verdict rather than triggering a speculative two-phase flash.
4. **GDEM Extrapolation Overflow (`VLERoutines.cpp:2291-2303`):** Near $\delta \sim 1$ of GERG-2008 methane/ethane ($162.6\text{ K}, 12.2\text{ MPa}$), spurious roots produce $\ln\phi_i \sim O(10^4)$, causing GDEM acceleration (factor up to 19) to overflow $\exp(d_i - \ln\phi_i)$ into `NaN` unless intercepted by `trial_moles_finite`.
5. **Leaked Imposed-Phase State After Spinodal Exception (`VLERoutines.cpp:2329-2336`):** When pressure falls between spinodal pressures on $\mathrm{N}_2/\mathrm{C}_1/\mathrm{C}_2/n\mathrm{C}_4/n\mathrm{C}_5$ mixtures and `solver_rho_Tp_global` throws, `CoolProp` wraps the SRK-seeded fallback in RAII `ScopedImposedPhase` (`:2334`) so `HEOS.SatL` cannot leak `iphase_gas` onto subsequent flashes.

#### 4.2 Nitrogen Auto-Stratification, Loading Topology, and Rollover Boil-Off Spikes

LNG rollover occurs when two liquid layers form with heavy, warmer (hydrostatically pressurized) cargo beneath a lighter, colder top layer. At the bottom of a $22\text{ m}$ cylindrical `50,000 m^3` storage tank (comparable to the 1971 *La Spezia* Panigaglia terminal incident after *Esso Brega* bottom-filled denser Libyan LNG beneath a lighter heel; Sarsten 1972, Bates & Morrison 1997), hydrostatic head $\Delta P = \rho g H \approx 97\text{ kPa}$ raises local boiling temperature by $\sim 6.5\text{ K}$, suppressing bottom vaporization while ambient floor heat leak superheats the trapped lower cell.

Two distinct thermodynamic regimes govern stratification stability (`Basis: execution (standalone Klosek–McKinley / NBS-1030 cryogenic density & lumped two-layer Bates–Morrison probe; not a compiled CoolProp GERG-2008 run)`):

1. **Nitrogen-Induced Auto-Stratification vs. Hydrocarbon Weathering:** For base LNG (`91% CH4, 6% C2H6, 2% C3H8, 1% N2` at $111.7\text{ K}$), $\rho_0 = 455.86\text{ kg/m}^3$ and thermal expansion $\alpha_T = 2.915 \times 10^{-3}\text{ K}^{-1}$ ($|\partial\rho/\partial T| = 1.33\text{ kg/(m}^3\cdot\text{K)}$). Because nitrogen boils preferentially ($T_b = 77.36\text{ K}$ vs. $\mathrm{CH}_4$ $111.67\text{ K}$) yet has higher effective liquid density ($\sim 604\text{ kg/m}^3$) than methane ($\sim 422\text{ kg/m}^3$), boiling off $0.5\text{ mol}\%\text{ N}_2$ **reduces** surface density by $\mathbf{-1.31\text{ kg/m}^3}$ ($\rho = 454.55\text{ kg/m}^3$)—stabilizing a buoyant light cap (*auto-stratification* even in an initially uniform tank when $x_{\mathrm{N}_2} \gtrsim 1\%$). Conversely, once $\mathrm{N}_2$ is depleted, boiling off $1.0\text{ mol}\%\text{ CH}_4$ enriches $\mathrm{C}_2\mathrm{H}_6/\mathrm{C}_3\mathrm{H}_8$ and **increases** surface density by $\mathbf{+2.89\text{ kg/m}^3}$ ($\rho = 458.75\text{ kg/m}^3$), promoting top-down convective mixing and accelerating density equalization.
2. **Superheat Storage Scaling in Two-Layer Rollover (`50,000 m^3` tank, $D = 49\text{ m}$, $H_{\text{tot}} = 22\text{ m}$):**

| Scenario (Standalone Two-Layer Probe) | Initial $\Delta\rho_0$ ($\text{kg/m}^3$) | Steady Normal BOG (t/h) | Time to Rollover (h) | Bottom Superheat $\Delta T$ (K) | Stored Superheat (GJ) | Flashed Vapor (tonnes) | Mean 2-hr Rollover BOG (t/h) | Spike Multiplier |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Thin heavy bottom ($H_b = 6\text{ m}, Q_b = 130\text{ kW}$) | 2.47 | 1.41 | 83.9 | +3.72 | 65.4 | 128.2 | 65.5 | **46.4×** |
| Moderate stratification ($H_b = 12\text{ m}, Q_b = 110\text{ kW}$) | 3.50 | 1.27 | 252.8 | +3.48 | 122.4 | 240.0 | 121.3 | **95.4×** |
| Strong stratification ($H_b = 12\text{ m}, Q_b = 110\text{ kW}$) | 5.36 | 1.27 | 434.7 | +4.65 | 164.4 | 322.3 | 162.4 | **127.8×** |

**Operational Loading Rule Derived from Density Matching:** Bottom-filling *heavy* cargo beneath a light heel—or top-filling *light* cargo atop a heavy heel—maximizes stratification; conversely, **top-filling denser cargo** (via splash/spray header) and **bottom-filling lighter cargo** (via submerged jet nozzle) uses buoyancy-driven plumes to force immediate mixing and prevent superheat trapping. Because double-diffusive interfacial heat transfer scales as $h_{\text{int}} \propto R_\rho^{-1.8}$ (where stability ratio $R_\rho = \Delta\rho_C / \Delta\rho_T$), stronger stratification looks deceptively quiescent (longer incubation, lower normal surface BOG) right up until $R_\rho \to 1$ triggers violent rollover capable of exceeding pressure-relief valve (PRV) capacity by an order of magnitude (as at *La Spezia* 1971, where PRVs lifted continuously for hours).

### 5. Multi-Level Performance and Resource Footprint (`L1`–`L6`)

Basis: source (exact source-tree measurements of pinned archives) + documentation (Ancellin & Dias 2019, Domínguez et al. 2022, Bell et al. 2014) + derived.

| Level | Metric Dimension | `capytaine` (BEM Hydrostatics & Potential Flow) | `MSS` (6-DoF Vessel Sim) | `DualSPHysics` (WCSPH Sloshing) | `CoolProp` (GERG-2008 Helmholtz EOS) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **L1 (Authoring & Maintenance)** | Domain spec complexity & verification cost | Concise Python API (20–80 LoC per hull); mesh watertightness/normal orientation is major human failure source | MATLAB/Octave `.m` scripts; straightforward prototyping, but manual coupling of external BEM `.mat` + `Gmtrx` assumptions | XML geometry/XML parameters + CaseGen preprocessor; steep tuning burden (`Dp`, `CFL`, `CoefSound`, `DDT`, `mDBC`) | Simple high-level `PropsSI`/AbstractState API; cryogenic VLE tuning and convergence-fallback logic is complex (`VLERoutines.cpp`: 4,390 LoC) |
| **L2 (Toolchain & Build Time)** | Source tree size & compilation footprint | `src/capytaine/`: 64 files (`14,918` LoC, `617.9 KiB`) + Fortran `libDelhommeau` Green-function kernels; `pip`/meson build ~15–60 s | Interpreted MATLAB/Octave: `HYDRO/` (`5,210` LoC), `CRAFT/` (`12,707` LoC), `LIBRARY/` (`5,461` LoC); zero build step | `src/source/`: 338 C++/CUDA files (`123,829` LoC, `5.37 MiB`); CMake + `nvcc` CUDA build takes several minutes | `src/Backends/Helmholtz/`: 26 C++ files (`30,915` LoC, `1.59 MiB`) inside `16 MiB` repo; full C++ build 1–5 min |
| **L3 (Pre-Processing / Flash Latency)** | Matrix assembly / EOS solve latency | Dense BEM matrix assembly $O(N_p^2)$ + direct LU $O(N_p^3)$ per frequency $\omega$; hydrostatic integrals alone are $O(N_p)$ (< 10 ms for $N_p \sim 10^3$) | `Gmtrx` / `computeManeuveringModel` executes in < 10 ms; zero mesh clipping at runtime | Cell-linked list + boundary normal `mDBC` preprocessing seconds–minutes for $10^6\text{--}10^7$ particles | Single-phase $(\rho, T)$ GERG-2008 evaluation ~1–10 µs; cryogenic multi-component TP-flash with Michelsen TPD + spinodal guards ~0.1–5 ms (tail retries on near-critical/80 K feeds) |
| **L4 (Simulation Execution Performance)** | Throughput, scaling, hardware bottleneck | Multi-frequency BEM sweep ($N_p = 10^3\text{--}5\times 10^3$, 50 frequencies): seconds to minutes on multi-core CPU; hierarchical/Toeplitz symmetries reduce cost | Real-time or $100\times$ faster-than-real-time on single CPU core for 12-state `rk4` (`h = 0.05–0.1 s`) | Published single-GPU benchmarks (Domínguez et al. 2022): 1M–8M particles take **1–13 hours** for seconds of physical sloshing; up to ~56M particles on RTX 2080 Ti (~36 h) and ~80M on Tesla V100 (~48 h); Symplectic doubles interaction passes vs. Verlet | Cached `CompositionDerivatives` (`ReducingFunctions.h:160-171`) avoids redundant $O(N^2)$ reducing sums; vectorized/tabular TTSE/bicubic backends accelerate repeated CFD/process calls |
| **L5 (Verification / Stability Check Speed)** | Online invariant / regulatory check latency | Mesh Gauss-volume consistency check $\max |V_i - V_j|/V$ is $O(N_p)$ (< 1 ms) — currently missing | `2008 IS Code` 71-angle $GZ$ check + `MSC.1/Circ.1627` Level 1/2 `C1` runs in < 50 ms; full `C2` time-domain scatter sweep takes minutes | Runtime checks limited to particle-escape & CFL $\Delta t_{\min}$ abort; no formal energy/momentum conservation proof | Online mechanical stability ($dp/d\rho > 0$) + finite-fugacity checks (`VLERoutines.cpp:2167-2182`) run per trial in µs |
| **L6 (RAM, Disk & Binary Footprint)** | Memory, storage, power draw | Dense $N_p \times N_p$ complex128 matrix requires $16 N_p^2$ bytes ($16\text{ MB}$ at $N_p=10^3$, $1.6\text{ GB}$ at $N_p=10^4$); archive `701 KiB` | `12 MiB` repo (dominated by vessel `.mat` datasets); < 200 MB MATLAB/Octave RSS | Bound tightly by GPU VRAM (16–80 GB HBM2/e for 10M–80M particles, 250–400 W TDP); `77 MiB` archive | Compiled shared library ~10–30 MB; < 20 MB RSS per EOS instance; suitable for terminal SCADA/PLC supervisory nodes |

### 6. Human Comprehensibility and Conceptual Simplicity / Model Refinement (`C1`–`C2`)

#### 6.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

- **Linear-$GM_0$ Anchoring Bias Among Maritime Operators:** Stability booklets and bridge displays prominently headline upright $GM_{\text{eff}}$, fostering a mental model that "$GM_{\text{eff}} \ge 0.15\text{ m}$ implies safe reserve stability." As §2.1 proves, flared and top-heavy hulls can pass $GM_{\text{eff}} = +0.32\text{ m}$ while failing `2008 IS Code` $e_{30\text{--}40}$ by $> 50\%$ due to early deck-edge immersion and slack-tank shifts. Similarly, `MSS`'s `euler2.m` mislabeled docstring ("Euler's 2nd-order method" for 1st-order Forward Euler) actively misleads engineers into trusting a step size that fabricates $35.6^\circ$ false parametric roll.
- **Deceptive Quiescence in LNG Rollover Telemetry:** During stratified incubation, low surface BOG rates look *safer* on terminal SCADA trend screens than vigorous normal boil-off, even as hundreds of GJ of superheat accumulate beneath the hydrostatic cap. Operators without vertical liquid temperature/density profiler (LTD) gradients ($\Delta T(z), \Delta\rho(z)$) cannot infer proximity to $R_\rho \to 1$ from vapor-space pressure alone.
- **Hidden Coordinate-Frame & Mesh-Orientation Pitfalls:** Maritime tools split between NED/FSD (`MSS`, $z$ downward) and ENU (`capytaine`, $z$ upward) coordinate systems, origin vs. centroid moments (`hydrostatics.py:79`), and outward vs. inward panel normal conventions. Silent acceptance of flipped normals or ignored `free_surface` arguments creates plausible-looking numerical tables that escape casual visual review.

#### 6.2 Simplicity, Orthogonality & Universal Model Refinement (`C2`)

Across ship stability and cryogenic containment, failure modes stem from **leaky approximations masquerading as universal primitives** (fixed linear `G` matrices reused at large heel, wall-sided formulas extrapolated past deck-edge immersion, origin-referenced moments passed as metacentric radii, raw `dp/drho > 0` accepted without Gibbs/fugacity verification). Two deep, orthogonal abstractions eliminate ad-hoc patches without hiding complexity:

1. **Exact Constant-Displacement Energy-Surface Hydrostatics ($U_{\text{hyd}}(\phi, \theta; \mathbf{f}_{\text{tanks}})$):**
   Instead of splitting upright $GM_0$, `KN` cross-curves, wall-sided formulas, free-surface corrections $\Delta GM_{\text{FS}}$, and wave-crest `MSC.1/Circ.1627` stability variation into five disconnected formulas, represent hydrostatic potential energy directly via exact volume-conserving wetted-hull + internal-tank-fluid polygon/mesh clipping over instantaneous wave surface $\eta(x, y, t)$:
   - Upright $GM_0$ is simply $\frac{1}{\Delta}\frac{\partial^2 U}{\partial\phi^2}\big|_0$;
   - Large-angle $GZ(\phi)$, deck-edge immersion, trim-coupled heel, non-rectangular slack-tank free-surface shift (exact shifted tank centroid, not wall-sided $i_T$), and time-varying wave $GM(t)$ emerge uniformly from **one** geometric clipping primitive, gated by an obligatory Gauss-divergence watertightness precondition ($\max_{i,j}|V_i - V_j|/V < 10^{-4}$ and explicit centroid subtraction $(y - y_f)$).
2. **Conservative Two-Phase Exergy / Density-Stratification Envelope for Cryogenic Tanks:**
   Unify LNG custody EOS (`CoolProp` GERG-2008) with rollover safety via a strictly checked thermodynamic interface returning certified triples `(phase_flag, rho, h_excess)` guarded by mechanical stability ($dp/d\rho > 0$), finite positive fugacity ($\phi_i \in (0, \infty)$), and global Gibbs minimality—feeding a single dimensionless risk invariant $(R_\rho(t), E_{\text{superheat}}(t) / (\dot{m}_{\text{PRV}} h_{fg} \tau_{\text{mix}}))$ that directly compares trapped bottom superheat against installed PRV relief capacity rather than tracking temperature and density in disconnected alarm channels.

### 7. End-to-End Solution & Implementation Validation (`V1`–`V4`)

- **`V1` (Specification Adequacy, Geometric Invariants & Non-Vacuity):**
  - Property-based geometric testing of hydrostatic integrators across randomized closed/open convex and flared hulls: verify translation invariance ($BM_T$ invariant under arbitrary rigid $(x_0, y_0)$ mesh shift—immediately catching `capytaine/bodies/hydrostatics.py:79`), `free_surface` equivariance (`mesh.immersed_part(free_surface=z0)` matches `mesh.translated_z(-z0).immersed_part(0.0)`—immediately catching `abstract_meshes.py:426`), Gauss-divergence volume consistency ($V_x = V_y = V_z$), and non-vacuity via mutant meshes with injected 1% flipped normals.
  - For cryogenic EOS specs, property-test zero-mole-fraction corners ($x_i = x_j = 0$), Gibbs–Duhem thermodynamic consistency $\sum_i x_i d\ln\phi_i = 0$, and phase-imposition exception safety (verifying state invariance after forced spinodal throws).
- **`V2` (Cross-Solver Differential Testing & Integrator Convergence Verification):**
  - Differential comparison of `capytaine` BEM vs. `WAMIT`/`HAMS` Green-function tables (and `MSS` `s175.mat` RAOs), and `DualSPHysics` `DDT_DDT2` + `mDBC` + Symplectic vs. experimental/VOF sloshing benchmarks (checking sensitivity to `Dp`, `CoefSound`, and `DDTValue`).
  - Mandatory **step-halving & symplectic-vs-dissipative cross-checks** on `IMO MSC.1/Circ.1627` Level-2 `C2` time-domain solvers: reject any integrator whose predicted peak roll changes by $> 2^\circ$ or crosses the $25^\circ$ threshold between $\Delta t$ and $\Delta t/2$ (catching both Forward Euler false instability and Backward Euler false stability automatically).
- **`V3` (Fault Injection, Sensor Corruption & Hardware-Layer Validation):**
  - Inject realistic maritime/cryogenic hardware faults: ballast-tank level-gauge bias or stuck-valve sequence inversions (verifying loading computers flag *transient* intermediate transfer steps, not only start/end tank states), roll-inclinometer drift, cryogenic LTD (level-temperature-density) servo-gauge stuck probes, and GPU `float32` precision-loss/overflow checks in `DualSPHysics` high-impact Tait pressure spikes (`pow(rho/rho0, 7)`).
- **`V4` (Plant Falsification, Real-Incident Replay & Operator Mental-Model Testing):**
  - **Incident & Basin Waveform Replay:** Replay historical casualty envelopes (*MV Cougar Ace* multi-tank ballast transfer, `S175` ITTC head-sea parametric roll tank tests, *La Spezia* 1971 LNG rollover trajectory) and run Signal Temporal Logic (STL) falsification over wave-group encounter sequences (searching for worst-case 3–5 wave groups that breach $25^\circ$ roll or deck-edge immersion) and tank-fill schedules (searching for worst-case heel/cargo composition pairs that minimize $R_\rho$ while maximizing $\Delta T_{\text{superheat}}$).
  - **Runtime Model-Validity Shields & Human Litmus Tests:** Deploy `ModelPlex`-style runtime monitors on vessel loading computers (checking live roll period $T_\phi = 2\pi k_{xx}/\sqrt{g\,GM_{\text{eff}}}$ against calculated $GM_{\text{eff}}$ to detect unmodeled slack-tank FSM!) and LNG terminals (cross-checking measured BOG rate against ambient heat-leak predictions to flag anomalous interfacial heat suppression). Conduct empirical behavioral litmus tests with watchkeeping officers and terminal operators on sequential-vs-simultaneous ballast prompts and quiescent-tank rollover warnings.

## Boundaries

- **Compiled Upstream Execution (`not examined`):** `capytaine` (Fortran `libDelhommeau`), `MSS` (MATLAB/Octave), `DualSPHysics` (CUDA/C++ GPU SPH), and `CoolProp` (C++ GERG-2008) were not compiled or executed on this host. All source-level algorithms, guards, and bugs were verified directly against the pinned source files (`Basis: source`); all numerical tables in §§1.1, 2.1, 3.1, and 4.2 derive from standalone Python 3.13 IEEE-754 double-precision probes and are explicitly labeled as such.
- **Klosek–McKinley vs. Full GERG-2008 Cryogenic Accuracy (`known not to apply` outside narrow LNG range):** The standalone LNG probe in §4.2 uses a Klosek–McKinley / NBS-1030 correlation (valid for bubble-point liquid $\mathrm{CH}_4\text{--}\mathrm{C}_2\mathrm{H}_6\text{--}\mathrm{C}_3\mathrm{H}_8\text{--}\mathrm{N}_2$ at $105\text{--}120\text{ K}$, $x_{\mathrm{N}_2} \le 4\%$) plus a lumped two-layer Turner heat-transfer law; it does **not** reproduce full GERG-2008 vapor–liquid equilibrium fugacities, high-pressure supercritical LNG states, or 3D CFD buoyant plume mixing during rollover overturn.
- **3D Trim-Coupled Heel, Wave-Excited Broaching, and Damaged-Compartment Progressive Flooding (`not examined`):** §1.1 models a 2D constant-displacement cross-section without longitudinal trim coupling ($\theta(\phi)$), downflooding openings, or progressive internal flooding dynamics (`SOLAS` probabilistic damage stability `s_i` factors).
- **Coupled Hull–Sloshing Time-Domain Interaction (`not examined`):** Fully two-way coupled ship-roll + internal-tank SPH sloshing (where dynamic sloshing phase lag can either damp or amplify parametric roll depending on $\omega_{\text{slosh}} / \omega_\phi$) was analyzed at the solver-architecture level (`DualSPHysics` `RunFloating` + Chrono) rather than simulated in 3D coupled SPH.
- **Exact `IMO MSC.1/Circ.1627` Direct Stability Assessment (DSA) Statistical Convergence (`unknown`):** Long-term irregular-sea Monte Carlo convergence budgets (thousands of hours of simulated irregular seas needed to bound rare-event $C_2$ capsize tail probabilities with narrow confidence intervals) were not empirically measured.

## Evidence

- **Primary Upstream Source Inspection (`observed_at: 2026-11-19`):**
  - `capytaine/capytaine` @ `b81111ae1a4e4312efbb00023b2dd0837aa312b1`:
    - `src/capytaine/bodies/hydrostatics.py:76-100` (`transversal_metacentric_radius` and `longitudinal_metacentric_radius` origin-referenced `y**2`/`x**2`), `:151-180` (`_rigid_body_hydrostatic_stiffness_coef`), `:253-350` (`compute_hydrostatic_stiffness`).
    - `src/capytaine/meshes/abstract_meshes.py:404-430` (`immersed_part` hardcoding `origin=(0, 0, 0)` at line 426).
    - `src/capytaine/meshes/surface_integrals.py:40-112` (`volumes`, `volume = np.mean(self.volumes)`, `waterplane_integral`, `center_of_buoyancy`, `waterplane_center`).
  - `cybergalactic/MSS` @ `22142414efa679f3926176eac36dae29e2ab93d1`:
    - `LIBRARY/modeling/Gmtrx.m:1-43` (linear $6\times 6$ stiffness about CF transformed via `Hmtrx`).
    - `LIBRARY/modeling/gvect.m:1-30` (submerged nonlinear restoring vector).
    - `LIBRARY/numericalMethods/euler2.m:1-17` (1st-order Forward Euler `xnext = x + h*xdot` mislabeled as 2nd-order).
    - `CRAFT/hydroVessel.m:135-145` (constant linear `- vessel.G * eta`), `CRAFT/SIMhydroVessel.m:126` (`rk4` stepper), `HYDRO/vessels_capytaine/S175/S175.md`, `mssExamples/exShipHydrostatics.m:1-88`.
  - `DualSPHysics/DualSPHysics` @ `ef3721a861fda961f0e2f9ec4cd317b19de99086`:
    - `src/source/FunSphEos.h:38-65` (`float32` Monaghan–Tait EOS `b*(pow(rho/rho0,gamma)-1.0f)`).
    - `src/source/JSph.cpp:650-652, 716-739, 897-961, 1500` (`Gamma`, `CFLnumber`, `DDTValue = 0.1f`, `TMdbc2`, `Cs0 = sqrt(Gamma*CteB/RhopZero)`).
    - `src/source/JSphCpu.cpp:777, 923-940, 953-965` (Molteni `DDT_DDT`, Fourtakas `DDT_DDT2` hydrostatic subtraction & DBC/floating suppression, `MDBC2_NoPen` penetration guard).
    - `src/source/JSphCpuSingle.cpp:873-960` (`ComputeStep_Ver`, `ComputeStep_Sym` 2-pass predictor–corrector, `RunFloating` + Chrono).
  - `CoolProp/CoolProp` @ `55db41ea9355b5f988f24e30518387a4597f14a8`:
    - `src/Backends/Helmholtz/ReducingFunctions.h:156-235` (`CompositionDerivatives` cache, `GERG2008ReducingFunction`), `ReducingFunctions.cpp:245-350, 528-555` (`both_mole_fractions_zero` $0/0$ guard, 1-ULP ordering note).
    - `src/Backends/Helmholtz/VLERoutines.cpp:2167-2395` (`mechanically_stable`, `finite_fugacity_coefficients` at `110 K` GERG-2008 $n$-pentane, `solve_rho_Tp_global_stable` `80 K` $\mathrm{N}_2/\mathrm{C}_1/\mathrm{C}_2/\mathrm{C}_3$ fallback, `trial_moles_finite` GDEM overflow at `162.6 K`, `ScopedImposedPhase` spinodal throw guard).
- **Primary Literature & Regulatory Standards:**
  - T. I. Fossen, *Handbook of Marine Craft Hydrodynamics and Motion Control*, Wiley, 2011 (`DOI: 10.1002/9781119994138`).
  - M. Ancellin & F. Dias, *JOSS* 4(36):1341, 2019 (`DOI: 10.21105/joss.01341`).
  - `IMO Resolution MSC.267(85)` (2008 Intact Stability Code) and `IMO MSC.1/Circ.1627` (2020 Interim Guidelines on Second Generation Intact Stability Criteria: Level 2 $C_1 \le 0.06$ or $C_2 \le 0.025$ against $25^\circ$ roll).
  - S. Bates & D. S. Morrison, *Int. J. Heat Mass Transf.* 40(8):1875–1884, 1997 (`DOI: 10.1016/S0017-9310(96)00218-9`); A. Sarsten (1972) *La Spezia* 1971 LNG rollover study.
  - O. Kunz & W. Wagner, *J. Chem. Eng. Data* 57(11):3032–3091, 2012 (`GERG-2008` / `ISO 20765-2`); I. H. Bell et al., *Ind. Eng. Chem. Res.* 53(6):2498–2508, 2014 (`DOI: 10.1021/ie4033999`).
  - J. M. Domínguez et al. (2021–2022) DualSPHysics GPU scaling benchmarks (RTX 2080 Ti / V100 / A100 multi-million-particle sloshing/dam-break runtimes).
- **Reproducible Execution Probes (`Python 3.13.15`, Linux x86_64, IEEE-754 binary64):**
  - Constant-displacement 2D polygon-clipping $GZ(\phi)$ curve vs. wall-sided/linear models; `capytaine` parallel-axis ($+12.0\%$) and 2%-flipped-normal replicas; sequential vs. simultaneous slack-tank `2008 IS Code` audit; Mathieu–Duffing 4-integrator stability sweep (`RK4`, `Forward Euler`, `Backward Euler`, `Symplectic Velocity-Verlet`); Klosek–McKinley $\mathrm{N}_2$/$\mathrm{CH}_4$ density derivatives and `50,000 m^3` two-layer rollover BOG probe.

## Revalidation

To cheaply verify whether these findings still hold on newer upstream commits or candidate maritime/cryogenic software:

1. **Targeted Upstream Source Diffs (< 10 s):**
   - `capytaine`: Check `src/capytaine/meshes/abstract_meshes.py` (`immersed_part`: whether `origin=(0, 0, 0)` was fixed to `(0, 0, free_surface)`), `bodies/hydrostatics.py` (`transversal_metacentric_radius`: whether `(y - y_f)**2` replaced `y**2`), and `meshes/surface_integrals.py` (`volume`: whether a watertightness/normal-divergence assertion was added).
   - `MSS`: Check `LIBRARY/numericalMethods/euler2.m` (docstring vs. implementation) and `CRAFT/hydroVessel.m` (whether nonlinear $GZ(\phi)$ / wave-modulated $GM(t)$ restoring options were added).
   - `DualSPHysics`: Check `src/source/FunSphEos.h` (float vs. double EOS option) and `JSphCpu.cpp` (Fourtakas `DDT_DDT2` interaction with `mDBC` / floating bodies).
   - `CoolProp`: Check `src/Backends/Helmholtz/VLERoutines.cpp` (`solve_rho_Tp_global_stable`, `finite_fugacity_coefficients`) and `ReducingFunctions.cpp` (`both_mole_fractions_zero`) for regressions on `80–115 K` $\mathrm{N}_2/\mathrm{C}_1/\mathrm{C}_2/\mathrm{C}_3/n\mathrm{C}_5$ GERG-2008 regression tests.
2. **Minimal Standalone Discriminating Probe (< 1 s in Python 3):**
   ```python
   import math
   # 1. Verify Forward Euler false parametric roll & Backward Euler false stability on Mathieu equation
   w0 = 2*math.pi/24.0; zeta = 0.06; we = 2*w0; c3 = 0.65*w0**2
   def run_fe(mu, dt):
       p, v, mp = math.radians(3.0), 0.0, math.radians(3.0)
       for k in range(int(240/dt)):
           a = -2*zeta*w0*v - w0**2*(1 + mu*math.cos(we*k*dt))*p + c3*p**3
           p, v = p + dt*v, v + dt*a; mp = max(mp, abs(p))
       return math.degrees(mp)
   assert run_fe(0.20, 0.5) > 30.0  # sub-critical mu=0.20 < 4*zeta=0.24 falsely rolls >30 deg!
   # 2. Verify cubic width law: single centerline baffle reduces free-surface i_T by exactly 4x
   i_unb = 24.0 * (13.0**3) / 12.0; i_baf = 2 * 24.0 * ((13.0/2.0)**3) / 12.0
   assert abs(i_unb / i_baf - 4.0) < 1e-12
   ```
3. **Full End-to-End Revalidation (when native Python/C++/CUDA stacks are installed):** Run `capytaine` on a shifted + 2%-normal-flipped barge mesh (`free_surface=0.5`), run `CoolProp` `HEOS` GERG-2008 TP-flash at `80 K` and `110 K` on `N2/CH4/C2H6/C3H8/nC5H12` (including two zero trace components), and run a 2D baffled vs. unbaffled `DualSPHysics` tank-sloshing case comparing `DDT_DDT2 + mDBC + Symplectic` against static `FSM` overturning moments.
