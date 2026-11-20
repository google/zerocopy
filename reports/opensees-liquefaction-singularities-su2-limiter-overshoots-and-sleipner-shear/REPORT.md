# Soil-Liquefaction Constitutive Singularities, Unstructured CFD Slope-Limiter Overshoots, Dual FEM Shear Bounds, and Structural Sign-Reversal Envelopes

## Summary

Catastrophic failures in continuum mechanics simulation and structural engineering—spanning seismic soil-liquefaction collapse, compressible CFD vacuum/negative-pressure blowups, distorted finite-element shear underestimation (exemplified by the August 23, 1991 Sleipner A Condeep offshore gravity-base implosion), and load-combination uplift omissions—stem from a single recurring defect: **numerical discretizations and constitutive wrappers fail to preserve the physical admissibility invariants of the governing PDEs under mesh distortion, extreme state transitions, or sign-changing actions**. Direct source inspection of `OpenSees/OpenSees` (`5b9b70511e04e8f1b65710edb98fdffd8ef3add0`), `su2code/SU2` (`6c0e5c5c720936b175c4004e57332884443437f5`), and `OpenFOAM/OpenFOAM-dev` (`af6c9e8f1a7f5872256bb288c3905002a5e435ab`), paired with normative standards (`EN 1990:2002`, `ASCE/SEI 7-22`), forensic engineering reports (`Jakobsen & Rosendahl 1994`; `Selby, Vecchio & Collins 1997`; `NTSB/HAR-19/02`), and standalone numerical micro-probes, establishes four high-value findings:

1. **Zero-Effective-Stress Constitutive Singularity & Inconsistent Tangent in `OpenSees` (`PressureDependMultiYield02` + `SSPquadUP`):** As cyclic excess pore-water pressure ratio $r_u = u_e / \sigma'_{v0} \to 1.0$ drives mean effective confining pressure $p' = -\sigma'_m \to 0$, `PressureDependMultiYield02::getModulusFactor()` (`PressureDependMultiYield02.cpp:1985-1996`) collapses shear and bulk moduli by $100\times$ (to $(0.0001)^{0.5} = 0.01\,G_r$ for cohesionless sand with `residualPress = 0.0001 * pAtm = 0.0101 kPa`, raising the fluid-to-soil stiffness contrast $K_f/G_{\text{soil}}$ from $29.5\times$ to $2933.5\times$). Simultaneously: (i) the outermost failure cone sets plastic modulus `plast_modul = 0` (`line 1770`), making the $6\times 6$ tangent matrix rank-deficient along the deviatoric flow normal at zero dilatancy; (ii) `getTangent()` comments out non-associated volumetric-deviatoric cross-coupling (`lines 659-670, 699-701`) and **explicitly zeroes all 2D plane-strain normal-shear tangent entries** (`lines 711, 715, 717-718`), breaking quadratic Newton–Raphson convergence in `Newmark`; and (iii) floating-point cone-nesting drift near $p' \to 0$ triggers hard process termination `exit(-1)` in `updateActiveSurface()` (`lines 2571-2575`). Moreau–Yosida residual-strength regularization plus HHT-$\alpha$/generalized-$\alpha$ damping eliminates zero-eigenvalue stiffness collapse.
2. **Unclipped Venkatakrishnan Overshoots, Zero-Density Guard Defect, and Positivity Failure in `SU2` & `OpenFOAM`:** Direct inspection of `SU2_CFD/include/limiters/CLimiterDetails.hpp:101-216` reveals three critical behaviors: (i) `venkatFunction` is **never clipped to $\le 1.0$**, attaining a mathematical maximum of $\phi_{\max} = (2+4\sqrt{2})/7 \approx 1.093836$ ($+9.38\%$ gradient over-amplification!) at $r^* = 2+2\sqrt{2} \approx 4.8284$ (a pathology explicitly documented in `OpenFOAM-dev`'s `VenkatakrishnanGradientLimiter.H:48-55`, which clips to `1.0` in `cellLimitedGrad.C:149` at the expense of differentiability); (ii) SU2's `LIMITER::BARTH_JESPERSEN` (`lines 155-178`) calls `venkatFunction(..., eps2 = DBL_EPSILON)` rather than classical piecewise-linear $\min(1, r)$; (iii) `LIMITER::VENKATAKRISHNAN` uses a **dimensional** $\varepsilon^2 = (LK)^3$ (`lines 197-200`) that allows negative face density at low-density local extrema; and (iv) `CEulerSolver.cpp:1967-1985` checks strict `< 0.0` (missing exact `== 0.0`) immediately before dividing by `Primitive_i[Density()]` at `line 1970`, where `NaN < 0.0` evaluates `false` and propagates into `roe.cpp:126,141` (`RoeSoundSpeed2 <= 0` then silently zeros the entire face flux at `roe.cpp:153-167`). Component-wise reconstruction can violate nonlinear equation-of-state pressure positivity $p(\mathbf{U}) > 0$ even when every conservative variable stays inside neighbor bounds; provable invariance requires **Zhang–Shu convex positivity scaling** paired with a positivity-preserving flux under **SSP-RK3**.
3. **Sleipner A Coarse Skewed-Element Shear Underestimation & Prager–Synge Dual Error Bounds:** On August 23, 1991, the Sleipner A concrete gravity-base structure imploded at $65\text{ m}$ submergence ($700\text{M}$ loss, M 3.0 seismic event) after a coarse, skewed `MSC/NASTRAN` tricell finite-element mesh underestimated tricell wall shear demand by **$47\%$**, compounded by short T-headed shear-bar anchorage (`Jakobsen & Rosendahl 1994`; `Selby, Vecchio & Collins 1997`). Because standard primal FEM displacements underestimate energy norms under shear locking and element distortion (dropping to $20.7\%$ of exact tip deflection in a coarse skewed 2D Q4 toy benchmark), only **Prager–Synge / Ainsworth–Oden `H(div)`-equilibrated dual stress reconstruction** ($\|\sigma - \sigma_h\|_{C^{-1}}^2 + \|\sigma - \tau_h\|_{C^{-1}}^2 = \|\tau_h - \sigma_h\|_{C^{-1}}^2$) yields a **strict, distortion-honest computable upper bound** that flags under-resolved shear meshes before design sign-off.
4. **Normative Structural Load-Combination Sign Reversals (`EN 1990` & `ASCE/SEI 7-22`):** Applying only unfavorable gravity load factors (`1.35G` in `EN 1990` Table A1.2(B) STR/GEO Set B, or `1.2D` in `ASCE/SEI 7-22` Section 2.3.1) to stabilizing dead loads masks net uplift tension and overturning collapse. Correct verification enforces per-reaction-mode influence-sign partitioning across **`EN 1990` Table A1.2(A) EQU** ($\gamma_{G,\text{sup}} = 1.10$ unfavorable, $\gamma_{G,\text{inf}} = 0.90$ favorable), **Table A1.2(B) STR/GEO Set B** ($\gamma_{G,\text{sup}} = 1.35$, $\gamma_{G,\text{inf}} = 1.00$), and **`ASCE/SEI 7-22` Combinations 5 & 7** (`0.9D + 1.0W`, `0.9D + 1.0E`), validated end-to-end via `V1–V4` mutant kill, Method of Manufactured Solutions (MMS), MPI reduction reproducibility, and historical collapse replays.

## Applicability

This report synthesizes direct source inspection of three pinned continuum-mechanics codebases, primary numerical-analysis papers, international structural design codes, and forensic collapse investigations observed on `2026-11-19`:

- **Geotechnical liquefaction plasticity & Biot $u$-$p$ coupling (`OpenSees/OpenSees@5b9b70511e04e8f1b65710edb98fdffd8ef3add0`):** Applies to `PressureDependMultiYield02` (`SRC/material/nD/soil/PressureDependMultiYield02.cpp`, `.h`) paired with saturated porous-media elements `SSPquadUP` (`SRC/element/UWelements/SSPquadUP.cpp`) or `FourNodeQuadUP` (`SRC/element/UP-ucsd/FourNodeQuadUP.cpp`) and implicit `Newmark` integration (`SRC/analysis/integrator/Newmark.cpp`). Note that `OpenSees` also includes `PressureDependMultiYield` (v1) and `PressureDependMultiYield03` (v3); exact line citations here apply specifically to `PressureDependMultiYield02.cpp` unless re-verified on v3.
- **Unstructured compressible CFD reconstruction & limiters (`su2code/SU2@6c0e5c5c720936b175c4004e57332884443437f5` and `OpenFOAM/OpenFOAM-dev@af6c9e8f1a7f5872256bb288c3905002a5e435ab`):** Applies to SU2 v8.6.0 `"Harrier"` vertex-centered dual-mesh FVM (`CEulerSolver.cpp`, `CUpwRoe_Flow` in `roe.cpp`, `CLimiterDetails.hpp`, `computeLimiters_impl.hpp`) and OpenFOAM-dev cell-centered FVM (`cellLimitedGrad`, `VenkatakrishnanGradientLimiter`, `correctedSnGrad`, `limitedSnGrad`, `MUSCLLimiter`). The two solvers are compared directly to highlight vertex-centered edge-midpoint vs. cell-centered face-centroid limiting and explicit non-orthogonal skewness damping.
- **Forensic structural concrete shear & dual FEM error bounds (`Jakobsen & Rosendahl 1994`; `Selby, Vecchio & Collins 1997`; `Prager & Synge 1947`; `Ainsworth & Oden 2000`; `NTSB/HAR-19/02`):** Applies to linear and nonlinear elastostatic/elastoplastic finite-element verification of reinforced concrete walls, box-cell junctions, and nodal shear-friction interfaces. The `MSC/NASTRAN` 1991 proprietary binary used in the original Sleipner A design is not publicly inspectable; all quantitative Sleipner A figures ($47\%$ shear underestimation, $65\text{ m}$ submergence, M 3.0 event) derive strictly from the published forensic literature (`Jakobsen & Rosendahl 1994`; `Selby, Vecchio & Collins 1997`).
- **Load-combination sign reversals (`EN 1990:2002`, `ASCE/SEI 7-22`):** Applies to Ultimate Limit State (ULS) equilibrium (`EQU`), structural resistance (`STR`), and LRFD strength combinations for buildings, bridges, foundations, and offshore structures. National Annexes under Eurocode may modify recommended $\gamma_G$ values; exact cited values are the CEN base recommendations in `EN 1990:2002` Tables A1.2(A) and A1.2(B).
- **Toy-model scope separation:** All standalone Python execution numbers (reproduced inline under `## Evidence`) come from pure-Python standard-library toy models implementing the exact inspected C++ formulas and classical 2D plane-stress Q4 elasticity—explicitly distinguished from running compiled `OpenSees`, `SU2`, `OpenFOAM`, or `VecTor` binaries.

## Findings

### 1. Zero-Effective-Stress Constitutive Singularity in Biot $u$-$p$ Seismic Soil Liquefaction

**Basis: normative (Yang, Elgamal & Parra 2003; McGann et al. 2012) + source (`OpenSees/OpenSees@5b9b70511e04e8f1b65710edb98fdffd8ef3add0`) + execution (toy model of `PressureDependMultiYield02.cpp` equations)**

#### 1.1 Effective-Stress Collapse and Multi-Yield-Surface Plasticity Degeneration

In saturated granular soils subjected to undrained cyclic seismic shear, contractive plastic volumetric tendency transfers overburden load from the solid skeleton to interstitial pore water, raising excess pore-water pressure $u_e$ toward initial vertical effective stress $\sigma'_{v0}$ ($r_u = u_e / \sigma'_{v0} \to 1.0$) and driving mean effective confining stress $p' = -\frac{1}{3}\operatorname{tr}(\boldsymbol{\sigma}') \to 0$. In the Yang–Elgamal–Parra multi-yield-surface Drucker–Prager cone model (ASCE *J. Geotech. Geoenviron. Eng.* 2003, DOI `10.1061/(ASCE)1090-0241(2003)129:12(1119)`), implemented in `OpenSees/OpenSees@5b9b70511e04e8f1b65710edb98fdffd8ef3add0` `SRC/material/nD/soil/PressureDependMultiYield02.cpp`, elastic moduli scale nonlinearly with $p'$ (`getModulusFactor`, `lines 1985-1996`):

$$G(p') = G_r \left(\frac{p' + p_{\text{res}}}{p'_r + p_{\text{res}}}\right)^d, \qquad K(p') = K_r \left(\frac{p' + p_{\text{res}}}{p'_r + p_{\text{res}}}\right)^d, \qquad d = \text{pressDependCoeff} \approx 0.5.$$

Direct inspection of `PressureDependMultiYield02.cpp` reveals four interlocking numerical obstructions at liquefaction onset ($r_u \to 1.0$):

1. **$100\times$ Elastic Modulus Collapse and Unchecked Negative Base in `pow` (`lines 54, 1740, 1781, 1985-1996, 2020`):**
   For cohesionless sand (`cohesion = 0`), `setUpSurfaces` enforces `if (residualPress < 0.0001*pAtm) residualPress = 0.0001*pAtm;` (`pAtm = 101.0 kPa`, so $p_{\text{res}} = 0.0101\text{ kPa}$). In `setTrialStress` (`line 2020`), tensile mean effective stress is clamped via `if (volume > 0.) volume = 0.;` (compression is negative in OpenSees, `line 381`). At $p' = 0$, `getModulusFactor` evaluates `scale = (-0.0101 / -101.0101)^0.5 = 0.0100`, collapsing $G$ and $K$ to $1\%$ of reference stiffness. Moreover, line 1993 computes `scale = pow(scale, pressDependCoeff);` **without** first checking `scale <= 0` (unlike `loadStage == 2` at `line 624`), and line 1995 floors the result via `(1.e-10 > scale) ? 1.e-10 : scale`—which passes `NaN` through unchanged if `stress.volume()` ever exceeds `residualPress` because `1.e-10 > NaN` evaluates to `false` in IEEE-754!
2. **Exact Rank-Deficient Tangent on the Outermost Failure Cone (`lines 671-702, 1770`):**
   `setUpSurfaces` explicitly sets `if (ii==numOfSurfaces) plast_modul = 0;` (`line 1770`). Inside `getTangent()` (`lines 679-682`), the elastoplastic tangent denominator is $H_0 + H_p = 9 K n_v^2 + 2 G (\mathbf{n}_{\text{dev}} : \mathbf{n}_{\text{dev}}) + H_p$ with `coeff2 = 4*G*G / (Ho + plastModul)`. On the outermost failure surface ($H_p = 0$) at phase transformation ($n_v = \text{volume} = 0$), $\mathbf{n}_{\text{dev}} : \mathbb{C}_{\text{ep}} : \mathbf{n}_{\text{dev}} = 2G - \frac{4G^2}{2G} = 0$: the $6\times 6$ constitutive tangent matrix acquires an **exact zero eigenvalue** along the active shear flow direction!
3. **Commented-Out Non-Associated Coupling & Zeroed 2D Plane-Strain Shear-Normal Terms (`lines 659-670, 699-727`):**
   In `getTangent()`, the non-symmetric volumetric-deviatoric cross-terms (`coeff3`, `coeff4`, required because dilatancy/contraction flow rule $P'' \neq Q''$ is non-associated) are commented out (`lines 659-670, 699-701`). Worse, in 2D plane strain (`ndm != 3`, used by `SSPquadUP` and `FourNodeQuadUP`), lines 708-726 explicitly zero all normal-shear tangent entries:
   ```cpp
   workM(0,0) = theTangent(0,0);  workM(0,1) = theTangent(0,1);  workM(0,2) = 0.;
   workM(1,0) = theTangent(1,0);  workM(1,1) = theTangent(1,1);  workM(1,2) = 0.;
   workM(2,0) = 0.;               workM(2,1) = 0.;               workM(2,2) = theTangent(3,3);
   ```
   Discarding both non-associated dilatancy terms and symmetric shear-normal coupling destroys the consistency of the Newton–Raphson Jacobian precisely when cyclic pore-pressure buildup couples shear strain increments to volumetric contraction.
4. **Hard Process Crash on Yield-Cone Nesting Drift Near Apex (`lines 2571-2575`):**
   As $p' \to 0$, all nested Drucker–Prager yield cones shrink linearly to radius $\propto |p' + p_{\text{res}}|$ around the apex. If floating-point roundoff causes quadratic intersection coefficients in `updateActiveSurface()` to satisfy `B > 0. || C < 0.`, OpenSees prints `FATAL:PressureDependMultiYield02::updateActiveSurface(): error in surface motion.` and executes `exit(-1)`—terminating the simulation unrecoverably rather than substepping or returning a convergence-failure status to the time integrator.

#### 1.2 Coupled Biot $u$-$p$ Saddle-Point Ill-Conditioning (`SSPquadUP`) and Regularization

In `OpenSees` `SRC/element/UWelements/SSPquadUP.cpp` (McGann, Arduino & Mackenzie-Helnwein, *Acta Geotechnica* 7(4):297–311, 2012, DOI `10.1007/s11440-012-0168-5`), the stabilized single-point 4-node $u$-$p$ element assembles a $12\times 12$ block system (`lines 388-530`):

$$M_{\text{el}} = \begin{bmatrix} M_s & 0 \\ 0 & -S - K_p \end{bmatrix}, \quad C_{\text{el}} = \begin{bmatrix} C_s & -Q \\ -Q^T & -H \end{bmatrix}, \quad K_{\text{el}} = \begin{bmatrix} K_s(\boldsymbol{\sigma}') & 0 \\ 0 & 0 \end{bmatrix},$$

where $S \propto \frac{n}{K_f}$ is pore-fluid compressibility ($K_f \approx 2.2 \times 10^6\text{ kPa}$ for water), $H$ is the Darcy permeability matrix, and $K_p = -4 \alpha J_0 t (\nabla N)(\nabla N)^T$ (`line 505`) provides Huang–Zienkiewicz–Chan Laplacian stabilization to bypass the Ladyzhenskaya–Babuška–Brezzi (LBB) inf-sup failure of equal-order `Q4/Q4` elements in the undrained ($k \to 0$) limit. Notice two subtle implementation interactions: (i) `SSPquadUP::getInitialStiff()` (`line 426`) returns `getTangentStiff()`, and `getDamp()` (`lines 435-444`) applies stiffness-proportional Rayleigh damping `betaK0` to the *current* `mSolidK`; (ii) under Newmark-$\beta$ (`SRC/analysis/integrator/Newmark.cpp`), the effective Jacobian $K_{\text{eff}} = K + c_2 C + c_3 M$ couples a softening solid block $K_s$ ($G \to 750\text{ kPa}$ at $r_u=1.0$, with zero eigenvalues on the failure cone) against an incompressible water bulk modulus $K_f = 2.2\times 10^6\text{ kPa}$ ($K_f / G_{\text{soil}} = 2933.5\times$!).

**Toy-Model Verification (exact `PDMY02` equations, $G_r = 75\text{ MPa}$, $K_r = 200\text{ MPa}$, $p'_r = 101\text{ kPa}$, $\sigma'_{v0} = 100\text{ kPa}$, $K_f = 2.2\text{ GPa}$):**

| Pore Pressure Ratio $r_u$ | $p'_{\text{eff}}$ (kPa) | `PDMY02` Factor $G/G_r$ | $G(p')$ (kPa) | $K_f / G_{\text{soil}}$ Contrast | Unregularized Failure-Cone $\lambda_{\min}$ ($H_p=0, n_v=0$) | Moreau–Yosida Regularized $\lambda_{\min}$ ($p_{\min}=1\text{ kPa}, H_{p,\min}=0.02 G_{\text{reg}}$) |
| :---: | ---: | :---: | ---: | ---: | :---: | ---: |
| $0.0000$ | $100.0000$ | $0.99504$ | $74627.8$ | $29.5\times$ | $0.0\text{ kPa}$ (singular) | $1477.8\text{ kPa}$ |
| $0.5000$ | $50.0000$ | $0.70363$ | $52772.5$ | $41.7\times$ | $0.0\text{ kPa}$ (singular) | $1045.1\text{ kPa}$ |
| $0.9000$ | $10.0000$ | $0.31480$ | $23610.1$ | $93.2\times$ | $0.0\text{ kPa}$ (singular) | $468.7\text{ kPa}$ |
| $0.9900$ | $1.0000$ | $0.10000$ | $7500.0$ | $293.3\times$ | $0.0\text{ kPa}$ (singular) | $176.4\text{ kPa}$ |
| $0.9999$ | $0.0100$ | $0.01411$ | $1058.0$ | $2079.4\times$ | $0.0\text{ kPa}$ (singular) | $148.5\text{ kPa}$ |
| $1.0000$ | $0.0000$ | $0.01000$ | $750.0$ | $2933.5\times$ | $0.0\text{ kPa}$ (singular) | $148.5\text{ kPa}$ |

*(Basis: execution [toy model of `PressureDependMultiYield02.cpp:671-702,1740,1770,1985-1996`]).*

**Regularization & Time-Stepping Remedy:** Replacing the hard $p'=0$ clamp with a $C^1$-smooth hyperbolic effective-stress floor $p'_{\text{reg}} = \sqrt{(p')^2 + (p'_{\min})^2}$ (e.g., $p'_{\min} = 0.5\text{–}1.0\text{ kPa}$) plus Moreau–Yosida Perzyna viscoplastic / residual-strength hardening ($H_{p,\min} > 0$, or viscous drag $\eta_{\text{MY}} \dot{\boldsymbol{\varepsilon}}^p$) keeps the consistent elastoplastic tangent strictly coercive ($\lambda_{\min} \ge 148.5\text{ kPa}$ in the table above), restores non-symmetric consistent tangent assembly in 2D/3D, and pairs with energy-dissipative HHT-$\alpha$ ($\alpha \in [-0.3, 0]$, $\gamma = \frac{1-2\alpha}{2}$, $\beta = \frac{(1-\alpha)^2}{4}$) or numerical-damping Newmark ($\gamma > 0.5$, $\beta = \frac{1}{4}(\gamma+0.5)^2$) to damp spurious high-frequency pore-pressure oscillations during post-liquefaction lateral spreading (as in the 1964 Niigata and 1971 Lower San Fernando Dam seismic failures).

---

### 2. Unstructured Compressible CFD Slope-Limiter Overshoots vs. Zhang–Shu Positivity Preservation

**Basis: normative (Venkatakrishnan 1995; Barth & Jespersen 1989; Zhang & Shu 2010; Zhang, Xia & Shu 2012; Gottlieb, Shu & Tadmor 2001) + source (`su2code/SU2@6c0e5c5c720936b175c4004e57332884443437f5`; `OpenFOAM/OpenFOAM-dev@af6c9e8f1a7f5872256bb288c3905002a5e435ab`) + execution (toy model of SU2/OpenFOAM limiters & Zhang–Shu scaling)**

#### 2.1 Unclipped Venkatakrishnan Overshoot, Dimensional $\varepsilon^2$, and `SU2` vs. `OpenFOAM` Implementation Discrepancies

In second-order unstructured finite-volume Euler/Navier–Stokes solvers, face reconstruction $V_L = V_i + \phi_i (\nabla V_i \cdot \mathbf{r}_{if})$ applies a slope limiter $\phi_i$ computed from neighbor extremes $\Delta_+ = V_{\max/\min} - V_i$ and unlimited edge projections $\Delta_- = \text{proj}_{if}$. Classical Barth–Jespersen (AIAA 89-0366, DOI `10.2514/6.1989-366`) uses the non-differentiable piecewise function $\phi_{\text{BJ}}(r) = \min(1, r)$ ($r = \Delta_+ / \Delta_-$), whose discontinuous derivative causes residual limit-cycling on unstructured meshes. Venkatakrishnan (*J. Comput. Phys.* 118(1):120–130, 1995, DOI `10.1006/jcph.1995.1084`) introduced the smooth rational approximation:

$$\phi_{\text{Venk}}(\Delta_-, \Delta_+, \varepsilon^2) = \frac{\Delta_+^2 + 2\Delta_+\Delta_- + \varepsilon^2}{\Delta_+^2 + \Delta_+\Delta_- + 2\Delta_-^2 + \varepsilon^2} \xrightarrow{\varepsilon \to 0} \frac{r^2 + 2r}{r^2 + r + 2}.$$

Direct inspection of `su2code/SU2@6c0e5c5c720936b175c4004e57332884443437f5` and `OpenFOAM/OpenFOAM-dev@af6c9e8f1a7f5872256bb288c3905002a5e435ab` uncovers four load-bearing defects and behavioral divergences:

1. **Exact $+9.38\%$ Gradient Over-Amplification in `SU2` (`CLimiterDetails.hpp:101-105`, `computeLimiters_impl.hpp:242-248`):**
   Differentiating $f(r) = \frac{r^2+2r}{r^2+r+2}$ gives $f'(r) = \frac{-r^2+4r+4}{(r^2+r+2)^2} = 0 \implies r^* = 2 + 2\sqrt{2} \approx 4.828427$, where $f(r^*) = \frac{2+4\sqrt{2}}{7} \approx 1.0938363$! For every $r > 2$, $\phi_{\text{Venk}}(r) \in (1.0, 1.093836]$. Because `SU2` computes `limiter(iPoint, iVar) = geoFactor * min(limMax, limMin)` (`computeLimiters_impl.hpp:248`) **without clamping to `<= 1.0`**, any vertex whose positive and negative face projections both satisfy $r > 2$ has its gradient *amplified* by up to $+9.38\%$. By contrast, `OpenFOAM-dev` (`cellLimitedGrad.C:149`, `cellLimitedGrad.H:177`) initializes `limiter = 1.0` and takes `min(limiter, Limiter::limiter(r))`, explicitly warning in `VenkatakrishnanGradientLimiter.H:48-55` that the unclipped Venkatakrishnan function exceeds $1$ and causes unboundedness, while clipping breaks differentiability (recommending `cubicGradientLimiter` instead).
2. **`SU2` `BARTH_JESPERSEN` Is Actually Near-Zero-$\varepsilon$ Venkatakrishnan (`CLimiterDetails.hpp:155-178`):**
   `CLimiterDetails<LIMITER::BARTH_JESPERSEN>` sets `eps2 = std::numeric_limits<passivedouble>::epsilon()` (`line 163`) and delegates directly to `LimiterHelpers<>::venkatFunction(proj, delta, eps2)` (`line 176`), inheriting both the $r > 2$ overshoot ($\phi \le 1.0938$) and steeper clipping at $r = 1$ ($\phi(1) = 0.75$ vs. classical Barth–Jespersen $1.0$).
3. **Dimensional $\varepsilon^2 = (LK)^3$ Allows Negative Density at Extrema (`CLimiterDetails.hpp:197-200`):**
   In `LIMITER::VENKATAKRISHNAN`, `eps1 = fabs(L * K)` and `eps2 = max(eps1*eps1*eps1, epsilon)` depend purely on reference mesh length $L$ and user constant $K$, ignoring variable units and magnitude ($\rho \sim 10^{-2}\text{ kg/m}^3$ vs. $p \sim 10^5\text{ Pa}$). At a local minimum ($\Delta_+ = 0$), $\phi = \frac{\varepsilon^2}{\varepsilon^2 + 2\Delta_-^2} > 0$. In our Mach-10 expansion toy probe ($\rho_i = 0.02, \Delta_+ = 0, \text{proj} = -0.05, L = 0.1, K = 5.0 \implies \varepsilon^2 = 0.125$), `SU2`'s `venkatFunction` returns $\phi = 0.961538$, reconstructing **$\rho_{\text{face}} = -0.028077 < 0$**! (`LIMITER::VENKATAKRISHNAN_WANG` at `lines 337-426` scales $\varepsilon^2 = (K \cdot (\max V - \min V))^2$ per variable, reducing dimensional mismatch, and `NISHIKAWA_R3/R4/R5` at `lines 224-330` enforce `if (Dp > 2*Dm) return 1.0` to prevent $>1$ overshoot, but still do not guarantee nonlinear EOS positivity.)
4. **Confirmed Guard Bug on Exact Zero Density & Silent Flux Zeroing in `SU2` (`CEulerSolver.cpp:1967-1985`, `roe.cpp:151-167`):**
   In `CEulerSolver.cpp:1967-1980`:
   ```cpp
   bool neg_pres_or_rho_i = (Primitive_i[prim_idx.Pressure()] < 0.0) || (Primitive_i[prim_idx.Density()] < 0.0);
   bool neg_pres_or_rho_j = (Primitive_j[prim_idx.Pressure()] < 0.0) || (Primitive_j[prim_idx.Density()] < 0.0);
   su2double R = sqrt(fabs(Primitive_j[prim_idx.Density()]/Primitive_i[prim_idx.Density()]));
   ...
   const bool neg_sound_speed = ((Gamma-1)*(RoeEnthalpy-0.5*sq_vel) < 0.0);
   bool bad_recon = neg_sound_speed || neg_pres_or_rho_i || neg_pres_or_rho_j;
   ```
   When `Primitive_i[Density()] == 0.0`, the strict `< 0.0` predicate is `false`, line 1970 divides by `0.0` producing `Inf`/`NaN`, `neg_sound_speed` evaluates `NaN < 0.0` as `false`, and `bad_recon` stays **`false`**, forwarding `Density_i == 0.0` directly into `CUpwRoe_Flow::ComputeResidual` (`roe.cpp:126,141`: `Pressure_i/Density_i` and `Density_j/Density_i`!). Furthermore, when `RoeSoundSpeed2 <= 0.0` does trigger inside `roe.cpp:153-167`, `SU2` **zeros the entire inviscid face flux and Jacobians** (`Flux[iVar] = 0.0`), removing physical acoustic pressure restoring force across vacuum/strong-shock faces.
5. **Non-Orthogonal Skewness Correction in `OpenFOAM-dev` (`correctedSnGrad.C`, `limitedSnGrad.C:100-122`):**
   On skewed boundary-layer tetrahedra/prisms where face normal $\mathbf{S}_f$ deviates from cell-center vector $\mathbf{d}$ by $>70^\circ$, explicit non-orthogonal correction $\mathbf{k}_f \cdot (\nabla \phi)_f$ (`correctedSnGrad.C:52-61`) introduces negative off-diagonal effective coefficients and unbounded oscillations. `limitedSnGrad.C:100-122` bounds the non-orthogonal term by $\psi_f = \min\!\left(\frac{\psi_{\text{coeff}} |\nabla^\perp \phi|}{(1-\psi_{\text{coeff}})|\text{corr}| + \text{small}}, 1.0\right)$ (`limitCoeff = 0.5` bounds non-orthogonal flux $\le$ orthogonal flux, though the default constructor sets `limitCoeff_ = 1.0`, i.e., unlimited!).

#### 2.2 Convex Admissibility Set & Provable Zhang–Shu Positivity Under `SSP-RK3`

Even if a slope limiter strictly bounds each conservative component $\rho_q, (\rho\mathbf{u})_q, E_q$ inside its local neighbor min/max box, **the ideal-gas pressure function is strictly concave in conservative variables $\mathbf{U} = (\rho, \mathbf{m}, E)^T$**:

$$p(\mathbf{U}) = (\gamma - 1)\left(E - \frac{\|\mathbf{m}\|^2}{2\rho}\right), \qquad \mathcal{G} = \left\{\mathbf{U} \in \mathbb{R}^{d+2} : \rho > 0 \;\land\; p(\mathbf{U}) > 0\right\}.$$

Because $p(\mathbf{U})$ is concave on $\{\rho > 0\}$, the admissible set $\mathcal{G}$ is **convex**: for any $\mathbf{U}_1, \mathbf{U}_2 \in \mathcal{G}$ and $\lambda \in [0, 1]$, $(1-\lambda)\mathbf{U}_1 + \lambda\mathbf{U}_2 \in \mathcal{G}$. However, component-wise bounding boxes are *not* contained in $\mathcal{G}$! As demonstrated in the inline toy probe: for cell average $\bar{\mathbf{U}} = (\rho=1.0, m=0.0, E=1.0) \implies \bar{p} = 0.4000$ ($\gamma=1.4$), a reconstructed face point $\mathbf{U}_q = (\rho=0.12, m=0.48, E=0.90)$ (every entry strictly positive and inside plausible neighbor bounds) yields **$p_q = (0.4)(0.90 - \frac{0.48^2}{0.24}) = -0.0240 < 0$** ($\sqrt{\gamma p/\rho} = \text{NaN}$!).

**Zhang–Shu Positivity-Preserving Limiter Theorem** (Zhang & Shu, *J. Comput. Phys.* 2010, DOI `10.1016/j.jcp.2010.08.016`; Zhang, Xia & Shu, *J. Sci. Comput.* 2012, DOI `10.1007/s10915-011-9472-8`):
Given cell average $\bar{\mathbf{U}}_K \in \mathcal{G}$ with $\bar{\rho}_K \ge \varepsilon$ and $p(\bar{\mathbf{U}}_K) \ge \varepsilon$:
1. **Step 1 (Density scaling):** $\hat{\rho}_q = (1 - \theta_1)\bar{\rho}_K + \theta_1 \rho_q$ with $\theta_1 = \min\!\left(1, \frac{\bar{\rho}_K - \varepsilon}{\bar{\rho}_K - \min_q \rho_q}\right) \in [0, 1]$, guaranteeing $\hat{\rho}_q \ge \varepsilon > 0$.
2. **Step 2 (Convex pressure scaling):** For each quadrature/face point $q$ with $p(\hat{\mathbf{U}}_q) < \varepsilon$, find the unique root $t_q \in [0, 1)$ of the quadratic $p((1 - t_q)\bar{\mathbf{U}}_K + t_q \hat{\mathbf{U}}_q) = \varepsilon$, set $\theta_2 = \min_q t_q$, and scale $\tilde{\mathbf{U}}_q = (1 - \theta_2)\bar{\mathbf{U}}_K + \theta_2 \hat{\mathbf{U}}_q$. (In the inline toy probe, this gives $\theta_2 = 0.993038 \implies \rho = 0.1261, E = 0.9007, p = 1.00 \times 10^{-8} \ge \varepsilon_p$, preserving high-order accuracy in smooth regions without clipping extrema to first order!)
3. **Step 3 (`SSP-RK3` time invariance):** With a positivity-preserving numerical flux (Lax–Friedrichs, Rusanov, or HLLC—*not* unfixed Roe!) under the CFL condition $\Delta t \le \hat{\omega}_1 \frac{\text{vol}(K)}{\sum_f |S_f| \lambda_{\max}}$, forward Euler updates remain a convex combination of admissible states in $\mathcal{G}$. Because **Shu–Osher 3-stage SSP-RK3** (Gottlieb, Shu & Tadmor, *SIAM Review* 2001, DOI `10.1137/S003614450036757X`) is a convex combination of forward-Euler stages ($\mathbf{U}^{(1)} = \mathcal{F}(\mathbf{U}^n)$, $\mathbf{U}^{(2)} = \frac{3}{4}\mathbf{U}^n + \frac{1}{4}\mathcal{F}(\mathbf{U}^{(1)})$, $\mathbf{U}^{n+1} = \frac{1}{3}\mathbf{U}^n + \frac{2}{3}\mathcal{F}(\mathbf{U}^{(2)})$), **$\mathbf{U}_K^{n+1} \in \mathcal{G}$ ($\rho > 0, p > 0$) is mathematically invariant for all $n \ge 0$!**

---

### 3. Sleipner A FEM Shear Underestimation, Dual Equilibrated-Flux Bounds, and Structural Load-Combination Sign Reversals

**Basis: normative (`EN 1990:2002`; `ASCE/SEI 7-22`; Prager & Synge 1947; Ainsworth & Oden 2000) + forensic documentation (Jakobsen & Rosendahl 1994; Selby, Vecchio & Collins 1997; `NTSB/HAR-19/02`) + execution (toy 2D Q4 beam & Prager–Synge probe)**

#### 3.1 Forensic Anatomy of the 1991 Sleipner A Implosion and Related Shear/Load-Path Failures

On **August 23, 1991**, during controlled ballasting in Gandsfjorden near Stavanger, Norway, the reinforced-concrete gravity-base structure (GBS) of the **Sleipner A** offshore platform suffered sudden structural failure at **$65\text{ m}$ submergence depth** ($67\text{ m}$ hydrostatic differential across empty drill shafts and flooded triangular **tricell** interstices between circular storage cells), collapsing to the seabed in ~18 minutes with an estimated **$\$700\text{M}$ economic loss** and a magnitude **3.0 seismic event** (`Jakobsen & Rosendahl`, *Structural Engineering International* 4(3):190–193, 1994, DOI `10.2749/101686694780601971`, summarizing SINTEF's 16-report investigation; `Selby, Vecchio & Collins`, *Concrete International* 19(8):28–35, August 1997).

Two coupled engineering defects caused the collapse:
1. **Finite-Element Skewed-Mesh Shear Underestimation ($47\%$ error):** The global linear-elastic `MSC/NASTRAN` model discretized the complex curved tricell wall junction with coarse, heavily skewed 8-node solid/shell elements (severe trapezoidal distortion and poor aspect ratio at the acute tricell corners). Element distortion and incompatible shear-strain modes caused the primal displacement FEM model to **underestimate tricell wall shear forces by approximately $47\%$** relative to refined post-mortem meshes (`Jakobsen & Rosendahl 1994`; `Selby, Vecchio & Collins 1997`).
2. **Inadequate Shear-Reinforcement Detailing & Unverified Interface Capacity:** Relying on the underestimated shear demand, the tricell walls were detailed with short **T-headed shear bars** that terminated outside the critical flexural-tension crack zone without anchorage behind the main longitudinal steel, precipitating brittle diagonal-tension/shear-compression blowout under $65\text{ m}$ hydrostatic water pressure—confirmed independently by Selby, Vecchio & Collins' nonlinear Modified Compression Field Theory (`VecTor`) reanalysis predicting collapse right at the observed submergence depth.

This failure pattern recurs across modern structural disasters: in the **March 15, 2018 Florida International University (FIU) pedestrian bridge collapse** (`NTSB/HAR-19/02`, 6 fatalities), the nodal shear-friction interface at Member 11/12 suffered simultaneous **demand underestimation and monolithic shear-capacity overestimation** across an unroughened cold construction joint during post-tensioning adjustment; and in the **1978 Hartford Civic Center roof collapse**, unverified space-truss member slenderness and unmodeled eccentric joint connections caused progressive buckling under snow load when the computer model assumed idealized concentric pin bracing.

#### 3.2 Prager–Synge Hypercircle Identity and Strict Equilibrated-Flux *A Posteriori* Error Bounds

Primal displacement FEM minimizes potential energy over kinematically admissible displacements $\mathbf{u}_h \in V_h$, producing a stress field $\boldsymbol{\sigma}_h = \mathbb{C}:\boldsymbol{\varepsilon}(\mathbf{u}_h)$ that is **not** locally in static equilibrium ($\nabla \cdot \boldsymbol{\sigma}_h + \mathbf{f} \neq \mathbf{0}$ inside elements and discontinuous tractions across element faces). Under coarse or skewed meshes, shear locking artificially stiffens primal elements, making computed displacements and nodal shear demands appear deceptively small and smooth!

The **Prager–Synge Hypercircle Theorem** (Prager & Synge, *Q. Appl. Math.* 5(3):241–269, 1947, DOI `10.1090/QAM/25902`; Ainsworth & Oden, *A Posteriori Error Estimation in Finite Element Analysis*, Wiley 2000, DOI `10.1002/9781118032824`) constructs an independent **$H(\operatorname{div})$-equilibrated stress field** $\boldsymbol{\tau}_h$ satisfying exact equilibrium $\nabla \cdot \boldsymbol{\tau}_h + \mathbf{f} = \mathbf{0}$ and exact Neumann boundary tractions $\boldsymbol{\tau}_h \mathbf{n} = \bar{\mathbf{t}}$ via local vertex-patch dual solves (requiring zero global matrix factorization!). By orthogonality of kinematic and statically admissible error subspaces in the compliance energy norm $\|\boldsymbol{\sigma}\|_{\mathbb{C}^{-1}}^2 = \int_\Omega \boldsymbol{\sigma} : \mathbb{C}^{-1} : \boldsymbol{\sigma}\,d\Omega$:

$$\|\boldsymbol{\sigma} - \boldsymbol{\sigma}_h\|_{\mathbb{C}^{-1}}^2 + \|\boldsymbol{\sigma} - \boldsymbol{\tau}_h\|_{\mathbb{C}^{-1}}^2 = \|\boldsymbol{\tau}_h - \boldsymbol{\sigma}_h\|_{\mathbb{C}^{-1}}^2 \quad \Longrightarrow \quad \|\boldsymbol{\sigma} - \boldsymbol{\sigma}_h\|_{\mathbb{C}^{-1}} \le \eta_{\text{dual}} \equiv \|\boldsymbol{\tau}_h - \boldsymbol{\sigma}_h\|_{\mathbb{C}^{-1}}.$$

Unlike heuristic Zienkiewicz–Zhu stress-smoothing indicators (which can be fooled by uniformly locked coarse meshes), $\eta_{\text{dual}}$ is a **guaranteed, constant-free, mesh-distortion-honest upper bound** on the true discretization error!

**Toy-Model Verification (2D plane-stress cantilever beam $L=4\text{ m}, H=1\text{ m}, E=30\text{ GPa}, \nu=0.2$, parabolic tip shear $P=1\text{ MN}$, exact equilibrated Airy stress $\boldsymbol{\tau}_{\text{eq}}$, vs. coarse/skewed Q4 primal FEM — toy 2D analogue, not a 3D Sleipner A replay):**

| Q4 Mesh ($n_x \times n_y$) | Trapezoidal Skew Factor | Tip Deflection $v_{\text{tip}}$ (% of Timoshenko Ref $8.917\text{ mm}$) | Peak Gauss Shear $|\tau_{xy,h}|$ (Ref $1.500\text{ MPa}$) | Guaranteed Prager–Synge Relative Bound $\eta_{\text{dual}} / \|\boldsymbol{\tau}_{\text{eq}}\|_{\mathbb{C}^{-1}}$ |
| :---: | :---: | :---: | :---: | :---: |
| $2 \times 1$ | $0.00$ | $3.274\text{ mm}$ ($36.7\%$) | $4.198\text{ MPa}$ | **$79.4\%$** (immediate reject) |
| $2 \times 1$ | $0.35$ | $1.849\text{ mm}$ (**$20.7\%$** — severe locking!) | $4.182\text{ MPa}$ | **$88.8\%$** (immediate reject) |
| $4 \times 2$ | $0.00$ | $6.180\text{ mm}$ ($69.3\%$) | $4.607\text{ MPa}$ | **$55.4\%$** |
| $4 \times 2$ | $0.35$ | $4.343\text{ mm}$ ($48.7\%$) | $5.733\text{ MPa}$ | **$71.6\%$** (skew penalty caught!) |
| $8 \times 4$ | $0.00$ | $8.001\text{ mm}$ ($89.7\%$) | $3.794\text{ MPa}$ | **$32.1\%$** |

Notice that adding a $0.35$ trapezoidal skew on the $4\times 2$ mesh cuts displacement accuracy from $69.3\%$ down to $48.7\%$ (a $51.3\%$ stiffness/flexibility underestimation!), and the computable Prager–Synge dual bound $\eta_{\text{dual}}$ immediately jumps from $55.4\%$ to **$71.6\%$**, catching mesh distortion automatically with zero knowledge of the exact displacement solution.

#### 3.3 Structural Load-Combination Sign Reversals (`EN 1990` & `ASCE/SEI 7-22`)

Structural design software frequently exhibits a catastrophic sign-reversal bug: multiplying permanent dead load $G$ (or $D$) globally by its **unfavorable** load factor ($\gamma_{G,\text{sup}}$) across all load combinations, ignoring that when wind ($W$), seismic ($E$), buoyancy, or cantilever back-span actions oppose gravity, **dead load becomes a favorable (stabilizing) action** whose overestimation is unconservative!

Normative partial factors require explicit distinction across limit states (`EN 1990:2002` Tables A1.2(A) & A1.2(B); `ASCE/SEI 7-22` Section 2.3.1):

| Design Standard & Limit State | Unfavorable Permanent Factor ($\gamma_{G,\text{sup}}$ / $D$) | Favorable Permanent Factor ($\gamma_{G,\text{inf}}$ / $D$) | Governing Uplift / Sign-Reversal Combination | Effect of Omitting Favorable Factor (Inline Probe) |
| :--- | :---: | :---: | :--- | :--- |
| **`EN 1990:2002` Table A1.2(A) (`EQU`)** — Static equilibrium / rigid-body uplift & overturning | **$1.10$** | **$0.90$** | $0.90 G_{k,\text{fav}} + 1.10 G_{k,\text{unfav}} + 1.50 Q_{k,1}$ | With $G_k = -115\text{ kN}$ (down), $Q_k = +100\text{ kN}$ (up): misapplied $1.35G + 1.50Q = -5.25\text{ kN}$ (apparent compression!) vs. `EQU` $0.90G + 1.50Q = +46.50\text{ kN}$ (**net uplift!**). |
| **`EN 1990:2002` Table A1.2(B) (`STR/GEO` Set B)** — Structural resistance | **$1.35$** | **$1.00$** | $1.00 G_{k,\text{fav}} + 1.50 Q_{k,1}$ (Eq. 6.10) | Same load case: `STR` Set B gives $1.00(-115) + 1.50(100) = +35.00\text{ kN}$ (**net uplift!**); using $1.35G$ masks tension anchorage demand completely. |
| **`ASCE/SEI 7-22` Section 2.3.1 (LRFD)** — Strength design | **$1.2$** (Combs 2–4, 6) / **$1.4$** (Comb 1) | **$0.9$** (Combs 5, 7) | Comb 5: $0.9D + 1.0W$; Comb 7: $0.9D + 1.0E$ | With $D = -100\text{ kN}$, $W = +100\text{ kN}$: Comb 4 ($1.2D + 1.0W = -20.0\text{ kN}$, compression!) masks uplift, while Comb 5 ($0.9D + 1.0W = +10.0\text{ kN}$) exposes **net uplift tension**. |

**Required Algorithmic Invariant (Per-Reaction Influence-Sign Splitting):** For every structural response quantity $R_m$ (footing reaction, hold-down bolt tension, top/bottom beam bending moment, wall shear) and every independent load source $k$, evaluate its signed influence $R_m(G_k)$ before assembling combinations: select $\gamma_{G,\text{sup}}$ if $\operatorname{sgn}(R_m(G_k)) = \operatorname{sgn}(R_m^{\text{target}})$ and $\gamma_{G,\text{inf}}$ if opposite (respecting Eurocode's single-source principle for `STR` while applying independent $\gamma_{G,\text{sup}}/\gamma_{G,\text{inf}}$ to destabilizing/stabilizing spans in `EQU`).

---

### 4. Multi-Level Performance and Resource Footprints (`L1–L6`)

**Basis: source + documentation + derived (grounded in `OpenSees`, `SU2`, `OpenFOAM`, and cited literature)**

| Level | Seismic Liquefaction FEM (`OpenSees` `PDMY02` + `SSPquadUP`) | Unstructured Compressible CFD (`SU2` / `OpenFOAM` + Zhang–Shu) | Dual FEM Error Bounds & Load Envelopes (`Prager–Synge` + `EN 1990`) |
| :--- | :--- | :--- | :--- |
| **(L1) Human & Agent Authoring Velocity** | Writing a 2D dam/site model in `OpenSeesPy` takes ~200–600 LoC, but calibrating 15+ `PDMY02` contraction/dilation/liquefaction parameters (`liquefac1/2`, `contract1-3`, `dilate1-3`) and stabilizing `Newmark` convergence through $r_u \to 1$ takes weeks of geotechnical iteration. | Setting up `SU2` / `OpenFOAM` cases takes ~100–400 config lines, but tuning `VENKAT_LIMITER_COEFF`, mesh skewness, and `limitedSnGrad` to survive hypersonic/transonic startup without NaNs is notoriously fragile. Adding Zhang–Shu positivity scaling is ~60–120 LoC inside the flux/reconstruction loop. | Computing `H(div)` patch-equilibrated stress $\boldsymbol{\tau}_h$ adds ~300–800 LoC of element-patch linear algebra once in the solver library; checking `EN 1990`/`ASCE 7-22` dual-sign combinations per reaction mode takes $<50$ LoC and eliminates manual spreadsheet sign errors. |
| **(L2) Framework & Toolchain Build Time** | `OpenSees` C++/Fortran (`LAPACK`/`SuperLU`/`MUMPS`): ~15–35 min on 8 cores, ~4–8 GB RAM. | `SU2` C++/MPI/OpenMP/CoDiPack (`AD` build): ~15–45 min on 8–16 cores, ~8–16 GB RAM (AD expression templates inflate compile memory). `OpenFOAM-dev`: ~30–90 min full build, ~8–12 GB RAM. | Standalone `EN 1990`/`ASCE 7-22` envelope checker + patch-dual post-processor compiles in $<5\text{ s}$ (C99/Rust), $<200\text{ MB}$ RAM. |
| **(L3) Compilation, Elaboration & Synthesis Latency** | Implicit `Newmark` Newton–Raphson step: 2–5 iterations/step pre-liquefaction; degrades to 20–100+ iterations or substep cuts when `PDMY02` drops 2D normal-shear tangent terms and hits $H_p = 0$. | `computeLimiters_impl` (`SU2`) runs $O(|E| \cdot n_{\text{var}})$ OpenMP/MPI per nonlinear iteration ($<3\%$ of step cost); `VENKATAKRISHNAN_WANG` adds 2 global `MPI_Allreduce` calls (`CLimiterDetails.hpp:393-396`). Zhang–Shu positivity scaling adds $O(n_{\text{quad}})$ scalar quadratics per cell ($<5\%$ overhead over SSP-RK3). | Local vertex-patch Prager–Synge flux equilibration solves tiny $O(20\text{–}60)$ SPD systems per vertex independently (**embarrassingly parallel**, $<10\%\text{–}25\%$ of a single global FEM solve time). |
| **(L4) Generated Code Execution Performance** | Full 2D $10^4$-element `SSPquadUP` seismic record ($40\text{ s}$ at $\Delta t = 0.005\text{ s} = 8000$ steps): minutes to hours on 1–8 cores, bottlenecked by sparse direct LU (`SuperLU`/`MUMPS`) factorization when tangent updates trigger every Newton step. | Production $10^7$-cell 3D RANS/Euler `SU2`/`OpenFOAM` runs execute at $10^5\text{–}10^6$ cell-updates/core-s across $10^2\text{–}10^4$ MPI ranks; explicit `SSP-RK3` with Zhang–Shu is CFL-limited (especially on high-aspect-ratio boundary layers, where implicit/dual-time stepping dominates steady runs). | Dual-sign load-combination evaluation across $10^4$ structural members $\times 64$ combinations runs in $<10\text{ ms}$ on a single CPU core. |
| **(L5) Verification & Checker Speed** | Constitutive single-element cyclic-shear driver (`PDMY02` stress-path check): $<100\text{ ms}$. Checking global tangent conditioning $\kappa(K_{\text{eff}})$ via Lanczos/estimate takes $O(1)$ solves. | Pointwise positivity audit ($\forall K,\; \rho_K > 0 \land p_K > 0$) and discrete conservation audit ($\sum_K V_K \mathbf{U}_K^{n+1} = \sum_K V_K \mathbf{U}_K^n - \Delta t \sum_{\partial\Omega} \mathbf{F}_b$): microseconds per step. | Prager–Synge equilibrium residual check $\|\nabla \cdot \boldsymbol{\tau}_h + \mathbf{f}\| < 10^{-12}$ + hypercircle identity verification: seconds per $10^5$-element mesh. |
| **(L6) RAM, Disk & Binary Footprints** | `SSPquadUP` stores 3 DOFs/node + 20–40 nested yield-surface history tensors per Gauss point (~2–5 KB/element); 100k elements $\approx 0.5\text{–}2\text{ GB}$ RAM plus sparse LU fill-in ($2\text{–}16\text{ GB}$). | `SU2` primitive + gradient + limiter + Jacobian block storage: ~1–2 KB/node (3–5 KB/node with CoDiPack AD tapes); $10^7$ cells requires ~15–50 GB distributed MPI RAM. | Equilibrated stress field $\boldsymbol{\tau}_h$ adds ~12–24 doubles/element (~100–200 MB for $10^6$ elements), tiny compared to primal sparse stiffness factorization. |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

**Basis: derived + source (`OpenSees`, `SU2`, `OpenFOAM`) + forensic reports (`Jakobsen & Rosendahl 1994`; `NTSB/HAR-19/02`)**

#### 5.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

Across geotechnical FEM, compressible CFD, and structural design, catastrophic misjudgments arise because solvers **hide physical invariant violations behind opaque numerical heuristics**:

- **Misnamed/aliased algorithms (`SU2`, `OpenSees`):** An aerodynamicist selecting `SLOPE_LIMITER_FLOW = BARTH_JESPERSEN` in `SU2` reasonably expects the classical monotonicity-preserving $\min(1, r) \le 1$ limiter, not an unclipped Venkatakrishnan curve exceeding `1.0` (`CLimiterDetails.hpp:155-178`). Similarly, a geotechnical engineer calling `PDMY02::getTangent()` expects a consistent tangent for Newton–Raphson, not a symmetric approximation with zeroed 2D shear-normal terms (`PressureDependMultiYield02.cpp:708-727`) and an unrecoverable `exit(-1)` inside `updateActiveSurface()` (`line 2574`).
- **False visual confidence in smooth plots (`Sleipner A`, `FIU`):** Primal FEM stress-contour post-processors interpolate and average nodal stresses across distorted elements, visually smoothing away huge inter-element traction jumps ($\llbracket \boldsymbol{\sigma}_h \mathbf{n} \rrbracket \neq \mathbf{0}$). Without a single dimensionless, guaranteed error percentage ($\eta_{\text{dual}} / \|\boldsymbol{\tau}_h\| = 71.6\%$ vs. $5\%$ acceptance threshold), engineers routinely mistake visually smooth coarse-mesh contours for converged physical stresses.
- **Sign-convention cognitive load (`EN 1990` / `ASCE 7-22`):** Mixing compression-negative (`OpenSees` soil mechanics: `refPressurex = -refPress`) with tension-positive or downward-positive gravity conventions makes manual load-combination tables error-prone; engineers routinely overlook sign-flipping uplift modes when checking only peak gravity combinations.

#### 5.2 Simplicity, Orthogonality & Universal Model Refinement (`C2`)

Applying Felleisen macro-expressibility and Ousterhout deep-module criteria unifies all four seemingly disparate domains under **Invariant-Preserving Admissible-State Operators**:

1. **Convex Admissible-State Barrier (Replaces Ad-Hoc Clamps & `exit(-1)` Crashes):**
   - In **compressible CFD**, replace separate primitive-variable `< 0.0` checks (`CEulerSolver.cpp:1967`), zero-flux emergency aborts (`roe.cpp:153`), and dimensional $(LK)^3$ limiter knobs with one convex-set invariant $\mathbf{U} \in \mathcal{G}_\varepsilon = \{\rho \ge \varepsilon,\; p(\mathbf{U}) \ge \varepsilon\}$ enforced by Zhang–Shu convex scaling + positivity-preserving flux + `SSP-RK3`.
   - In **liquefaction soil plasticity**, replace hard `volume > 0 ? 0` clamps, `1.e-10` post-`pow` guards, and `exit(-1)` surface-nesting aborts with a single $C^1$ Moreau–Yosida regularized free-energy potential $\psi_\varepsilon(\boldsymbol{\varepsilon}^e, p'_{\text{reg}})$ guaranteeing $\mathbb{C}_{\text{ep}} \succ 0$ everywhere and returning structured substep-request status codes to the integrator.
2. **Guaranteed Dual Certificate Interface (Replaces Mesh-Convergence Guesswork):**
   - Make `H(div)` stress-equilibration residual $\eta_{\text{dual}}$ a mandatory output alongside primal FEM stress tensors (a deep module hiding patch assembly behind one scalar certificate `guaranteed_energy_error_upper_bound`), so coarse/skewed tricell meshes like Sleipner A are rejected automatically at solver exit rather than relying on expert visual inspection.
3. **Reaction-Mode Influence-Sign Combinator (Replaces Hardcoded Combination Tables):**
   - Represent load combinations as a single declarative policy mapping `(limit_state ∈ {EQU, STR, LRFD}, action_class, favorable: bool) -> gamma`, where `favorable` is computed automatically per reaction DOF from $\operatorname{sgn}(R_m(G_k)) \cdot \operatorname{sgn}(R_m^{\text{env}})$—making sign-reversal uplift checks an ordinary, unavoidable case with zero manual sign bookkeeping.

---

### 6. End-to-End Solution and Implementation Validation (`V1–V4`)

**Basis: normative + source + derived**

- **`V1` (Specification Adequacy, Mutation & Non-Vacuity Validation):**
  - *Skewed-tricell & dead-load sign-flip mutant-kill suite:* Inject (i) trapezoidal element skew ($0.35$) into benchmark walls/beams and verify the dual error gate rejects every distorted mesh with $\eta_{\text{dual}} > 5\%$; (ii) favorable/unfavorable dead-load sign-flip mutants (e.g., substituting `1.35G` for `0.90G` in `EQU`, or omitting `0.9D + 1.0W` in `ASCE 7-22`) and verify $100\%$ mutant kill; and (iii) exact zero-density `Primitive_i[Density()] == 0.0` edge mutants (which immediately exposes `SU2`'s `CEulerSolver.cpp:1967-1970` bug!).
- **`V2` (Discretization Accuracy, MMS & Independent Solver Cross-Validation):**
  - *Method of Manufactured Solutions (MMS) exact PDE convergence audit:* Drive analytical smooth fields $(\rho, \mathbf{u}, p)(x, y, t)$ and Biot $u$-$p$ fields $(\mathbf{u}, p_w)(x, y, t)$ with exact symbolic source terms across successively refined skewed unstructured meshes ($h, h/2, h/4$) and assert observed $L_2$/$H^1$ convergence rate $p_{\text{obs}} = \log_2(e_h / e_{h/2}) \ge 1.95$ (exposing silent first-order degradation from over-aggressive `limitCoeff` or accidental `bad_recon` fallback!).
  - *Prandtl–Meyer expansion & exact Riemann shock-tube differential checks:* Compare `SU2` / `OpenFOAM` flux schemes against exact analytical Sod/Lax/LeBlanc/Prandtl–Meyer vacuum-near-expansion solutions, verifying zero negative density/pressure events and monotone entropy production.
- **`V3` (Parallel Determinism, Floating-Point Reproducibility & Crash Safety):**
  - *MPI rank-invariant reproducible reductions:* In distributed `SU2`/`OpenFOAM`/`OpenSees` runs (`MPI_Allreduce` in `CLimiterDetails.hpp:393-396` and Krylov dot products), floating-point non-associativity across varying rank counts $P \in \{1, 4, 16, 64\}$ can trigger divergent bifurcation paths right at liquefaction onset or shock-induced transition. Validate with reproducible binned/Kulisch/ExBLAS fixed-order summations (`|res(P=1) - res(P=64)| == 0`) and assert zero unrecovered `exit(-1)` / `SIGFPE` crashes under randomized near-apex liquefaction perturbations.
- **`V4` (Historical Collapse, Centrifuge & Strong-Shock Replays + `SMoL` Comprehension Audits):**
  - *Historical disaster & physical benchmark replays:*
    1. **Sleipner A $65\text{ m}$ submergence benchmark** (`Selby, Vecchio & Collins 1997`, `VecTor` nonlinear concrete benchmark): verify that both the equilibrated-flux linear error bound flags the original coarse NASTRAN tricell mesh ($\eta_{\text{dual}} \gg 10\%$) and refined nonlinear concrete analysis predicts brittle tricell shear failure within $\pm 5\%$ of $65\text{ m}$ hydrostatic head.
    2. **VELACS centrifuge seismic liquefaction benchmark** (Arulanandan & Scott 1993, Model No. 1 / Model No. 2 level and sloping saturated sand beds): replay measured centrifuge base accelerations through Biot $u$-$p$ solvers (`SSPquadUP` + regularized `PDMY02`), validating excess pore-pressure ratio $r_u(t)$ rise to $1.0$, cyclic mobility dilation spikes, and post-liquefaction lateral displacement without Newton–Raphson stall.
    3. **Woodward–Colella Mach 10 Double-Mach Reflection** (*J. Comput. Phys.* 54(1):115–173, 1984, DOI `10.1016/0021-9991(84)90142-6`) and high-Mach astrophysical jet ($\text{Ma} = 80\text{–}2000$): verify zero negative density/pressure blowups under Zhang–Shu + `SSP-RK3` on skewed unstructured triangles.
  - *Human mental-model (`SMoL`) diagnostic litmus tests:* Empirically test structural/CFD engineers on error diagnostics covering `EN 1990` `EQU` (`0.90G`) vs. `STR` (`1.35G` / `1.00G`), `ASCE 7-22` `0.9D + 1.0W`, and Prager–Synge dual error percentages to ensure $>98\%$ accurate root-cause identification without silent overrides.

## Boundaries

- **Live execution of compiled `OpenSees`, `SU2`, `OpenFOAM`, and `VecTor` binaries (`not examined`):** Neither `OpenSees`, `SU2`, `OpenFOAM-dev`, nor `VecTor` was compiled or executed on full 3D seismic dam, Mach 10 reflection, or Sleipner A tricell meshes in this environment. All quantitative tables in Sections 1.2, 2.1, 2.2, 3.2, and 3.3 are produced by pure-Python standard-library toy models reproducing exact equations inspected in the pinned C++ source files and classical 2D Q4 elasticity, and are labeled explicitly as toy models.
- **Original 1991 `MSC/NASTRAN` Sleipner A input deck (`not examined` / proprietary):** The proprietary 1991 Norwegian Contractors `MSC/NASTRAN` finite-element input file and SINTEF's 16 internal client reports are not publicly hosted; the $47\%$ shear underestimation figure, $65\text{ m}$ collapse depth, and T-headed bar detailing conclusions rely strictly on the peer-reviewed forensic publications (`Jakobsen & Rosendahl 1994`, DOI `10.2749/101686694780601971`; `Selby, Vecchio & Collins 1997`, *Concrete International* 19(8):28–35).
- **`OpenSees` `PressureDependMultiYield03` and alternative constitutive models (`not examined`):** Whether `PressureDependMultiYield03.cpp` (present alongside `PressureDependMultiYield02.cpp` at `5b9b70511e04e8f1b65710edb98fdffd8ef3add0`), `PM4Sand`, or `SANISAND` retain the zeroed 2D plane-strain normal-shear tangent entries (`lines 711-718`) or the `exit(-1)` crash in `updateActiveSurface()` was **not examined** in this report.
- **Interaction of `SU2` `OutlierMitigation` and `CEulerSolver.cpp` flux schemes beyond `CUpwRoe_Flow` (`not examined`):** While `CEulerSolver.cpp:1967-1985` applies to all MUSCL convective fluxes in `CEulerSolver` (including `HLLC`, `AUSM`, `JST`), flux-level behavior under `RoeSoundSpeed2 <= 0` was examined specifically in `SU2_CFD/src/numerics/flow/convection/roe.cpp:151-167` (`CUpwRoe_Flow`); `ausm_slau.cpp` and `hllc.cpp` were **not examined**.
- **Conflating `EN 1990` Set B (`1.35G`) with `EQU` (`0.90G`) (`known not to apply`):** A common informal shorthand pairs `1.35G` and `0.90G` inside a single Eurocode combination; normatively, `EN 1990:2002` Table A1.2(B) (`STR/GEO` Set B) uses $\gamma_{G,\text{sup}}=1.35$ and $\gamma_{G,\text{inf}}=1.00$, whereas Table A1.2(A) (`EQU`) uses $\gamma_{G,\text{sup}}=1.10$ and $\gamma_{G,\text{inf}}=0.90$ (subject to National Annex overrides).
- **Nonlinear concrete Prager–Synge extension (`unknown` / requires dual plasticity formulation):** The exact quadratic hypercircle identity $\|\sigma - \sigma_h\|_{C^{-1}}^2 + \|\sigma - \tau_h\|_{C^{-1}}^2 = \|\tau_h - \sigma_h\|_{C^{-1}}^2$ holds strictly for linear elasticity (such as the linear-elastic `MSC/NASTRAN` model that caused the Sleipner A error); extending guaranteed constant-free upper bounds to cracking/softening reinforced concrete with tension stiffening requires convex dual dissipation formulations and remains more restricted than in linear elastostatics.
- **Unsupported upstream features (`unsupported`):** `OpenSees` `PressureDependMultiYield02` does not support an active non-symmetric 2D/3D consistent tangent (the code blocks at `lines 659-670, 699-701, 721-725` are commented out in upstream source); `SU2` (`6c0e5c5c720936b175c4004e57332884443437f5`) does not implement Zhang–Shu convex conservative-variable EOS positivity limiting inside `computeLimiters_impl.hpp`.

## Evidence

All source inspections, paper/standard verifications, and standalone micro-probes were conducted on `2026-11-19` (`2026-11-20T02:06Z` UTC).

### Pinned Primary Source Citations

1. **`OpenSees/OpenSees` @ `5b9b70511e04e8f1b65710edb98fdffd8ef3add0`**:
   - `SRC/material/nD/soil/PressureDependMultiYield02.cpp:54,381,597-729,1738-1782,1985-2022,2505-2580` — `pAtm = 101.0`, compression-negative `refPressurex`, `residualPress >= 0.0001*pAtm`, `if (ii==numOfSurfaces) plast_modul = 0` (`line 1770`), `getModulusFactor` (`lines 1985-1996`, `pow` without pre-check + IEEE-754 `1.e-10 > NaN` pass-through), `setTrialStress` clamp `if (volume > 0.) volume = 0.` (`line 2020`), `getTangent()` commented-out non-symmetric tangent (`lines 659-670, 699-701`) and zeroed 2D plane-strain normal-shear terms (`lines 708-727`), and `updateActiveSurface()` hard `exit(-1)` crash (`lines 2571-2575`).
   - `SRC/element/UWelements/SSPquadUP.cpp:142-216,388-530` — Biot $u$-$p$ coupled `mTangentStiffness`, `mDamp` (`C`, `-Q`, `-H` with `betaK0` applied to current `mSolidK`), `mMass` (`M`, `-S - Kp` with Laplacian stabilization `Kp = -4.0*mAlpha*J0*mThickness*dN*dNp` at `line 505`), `getInitialStiff()` delegating to `getTangentStiff()` (`line 426`).
   - `SRC/analysis/integrator/Newmark.cpp:105-160` — `Newmark(gamma, beta)` transient integrator.
2. **`su2code/SU2` @ `6c0e5c5c720936b175c4004e57332884443437f5`**:
   - `SU2_CFD/include/limiters/CLimiterDetails.hpp:101-105,155-216,224-330,337-426` — unclipped `venkatFunction(proj, delta, eps2)`, `LIMITER::BARTH_JESPERSEN` delegating to `venkatFunction` with `DBL_EPSILON`, dimensional `eps2 = (L*K)^3` in `LIMITER::VENKATAKRISHNAN`, `NISHIKAWA_R3/R4/R5` (`if (Dp > 2.0*Dm) return 1.0`), and global-range `VENKATAKRISHNAN_WANG` (`MPI_Allreduce`).
   - `SU2_CFD/include/limiters/computeLimiters_impl.hpp:206-254` — edge-midpoint projection `dist_ij = 0.5*(coord_j - coord_i)` and `limiter(iPoint, iVar) = geoFactor * min(limMax, limMin)` without clamping to `1.0`.
   - `SU2_CFD/src/solvers/CEulerSolver.cpp:1927-1987` — MUSCL primitive reconstruction, `OutlierMitigation`, strict `< 0.0` density/pressure check (`lines 1967-1968`) followed by unguarded division by `Primitive_i[Density()]` (`line 1970`), and first-order edge fallback (`lines 1984-1985`).
   - `SU2_CFD/src/numerics/flow/convection/roe.cpp:123-170` — `CUpwRoe_Flow::ComputeResidual` division by `Density_i`, `RoeSoundSpeed2 = (Gamma-1)*(RoeEnthalpy - 0.5*sq_vel)`, and silent zeroing of all face fluxes and Jacobians when `RoeSoundSpeed2 <= 0.0` (`lines 153-167`).
3. **`OpenFOAM/OpenFOAM-dev` @ `af6c9e8f1a7f5872256bb288c3905002a5e435ab`**:
   - `src/finiteVolume/finiteVolume/gradSchemes/limitedGradSchemes/cellLimitedGrad/gradientLimiters/VenkatakrishnanGradientLimiter.H:48-55,94-97` — `(sqr(r) + 2*r)/(sqr(r) + r + 2)` and explicit warning regarding $> 1.0$ unboundedness and clipping non-differentiability.
   - `src/finiteVolume/finiteVolume/gradSchemes/limitedGradSchemes/cellLimitedGrad/cellLimitedGrad.C:147-173` & `cellLimitedGrad.H:154-178` — initialization `limiter = 1.0` and `limiter = min(limiter, Limiter::limiter(r))`.
   - `src/finiteVolume/finiteVolume/snGradSchemes/correctedSnGrad/correctedSnGrad.C:43-65` & `limitedSnGrad/limitedSnGrad.C:43-48,89-123` — explicit non-orthogonal correction and `limitedSnGrad` blending (`limitCoeff_` default `1.0`).
   - `src/finiteVolume/interpolation/surfaceInterpolation/limitedSchemes/MUSCL/MUSCL.H:63-80` — `max(min(min(2*r, 0.5*r + 0.5), 2), 0)`.

### Reproducible Toy-Model Probe Command (Pure Python 3 Stdlib)

The core numerical findings in Sections 1.2, 2.1, 2.2, and 3.3 are reproduced deterministically via pure Python 3 (`python3 - <<'EOF' ... EOF`):

```python
import math

# 1. Exact OpenSees PDMY02 modulus collapse at liquefaction (PressureDependMultiYield02.cpp:1740,1985-1996)
pAtm, refPress, G_ref, d_exp, Kf = 101.0, 101.0, 75000.0, 0.5, 2.2e6
resP = 0.0001 * pAtm
for ru in [0.0, 0.9, 0.99, 1.0]:
    p_eff = max(0.0, (1.0 - ru) * 100.0)
    fac = ((-p_eff - resP) / (-refPress - resP)) ** d_exp
    print(f"PDMY02 ru={ru:.2f}: p'={p_eff:6.2f}kPa, G/Gr={fac:.5f}, Kf/G={Kf/(fac*G_ref):7.1f}x")

# 2. Exact SU2 venkatFunction unclipped peak & dimensional eps2 negative-density failure (CLimiterDetails.hpp:101-200)
venk = lambda proj, delta, eps2: (delta*(delta+proj)+eps2+delta*proj) / (delta*(delta+proj)+eps2+2*proj*proj)
r_star = 2.0 + 2.0 * math.sqrt(2.0)
print(f"SU2 Venkat unclipped peak at r*={r_star:.6f}: phi={venk(1.0, r_star, 2.22e-16):.7f}")
eps2 = (0.1 * 5.0) ** 3
phi_ext = venk(-0.05, 0.0, eps2)
print(f"SU2 extremum (rho=0.02, delta=0, proj=-0.05, eps2={eps2}): phi={phi_ext:.6f} -> rho_face={0.02 + phi_ext*(-0.05):+.6f}")

# 3. Zhang-Shu convex pressure scaling rescuing negative EOS pressure (gamma=1.4)
gamma, rb, mb, Eb, rq, mq, Eq, eps_p = 1.4, 1.0, 0.0, 1.0, 0.12, 0.48, 0.90, 1e-8
pq = (gamma - 1.0) * (Eq - 0.5 * mq * mq / rq)
lo, hi = 0.0, 1.0
for _ in range(60):
    mid = 0.5 * (lo + hi)
    r, m, E = (1-mid)*rb + mid*rq, (1-mid)*mb + mid*mq, (1-mid)*Eb + mid*Eq
    if (gamma - 1.0) * (E - 0.5 * m * m / r) >= eps_p: lo = mid
    else: hi = mid
print(f"EOS p_q={pq:+.4f} -> Zhang-Shu theta={lo:.6f} restores p={eps_p:.1e} > 0")

# 4. EN 1990 / ASCE 7-22 sign-reversal check
print(f"ASCE 7-22 (D=-100, W=+100): 1.2D+1.0W={1.2*(-100)+100:+.1f} vs 0.9D+1.0W={0.9*(-100)+100:+.1f} kN")
print(f"EN 1990 (G=-115, Q=+100): misapplied 1.35G+1.5Q={1.35*(-115)+150:+.2f} vs EQU 0.9G+1.5Q={0.9*(-115)+150:+.2f} kN")
```

## Revalidation

To cheaply determine whether these findings remain valid on newer upstream revisions:

1. **`OpenSees` `PDMY02` tangent, `pow` guard, and `exit(-1)` audit:** Diff `SRC/material/nD/soil/PressureDependMultiYield02.cpp` at `getTangent()` (check if 2D `workM(0,2)..workM(2,1)` are still hardcoded `0.` and non-symmetric coupling stays commented out), `getModulusFactor()` (check whether `scale <= 0` is guarded before `pow`), and `updateActiveSurface()` (check whether `exit(-1)` remains). Check `SSPquadUP.cpp` `getInitialStiff()` and `getDamp()`.
2. **`SU2` limiter clipping & zero-density guard check:** Diff `SU2_CFD/include/limiters/CLimiterDetails.hpp` (`venkatFunction`, `LIMITER::BARTH_JESPERSEN`, `LIMITER::VENKATAKRISHNAN`), `computeLimiters_impl.hpp` (check whether `limiter` is clamped to `<= 1.0`), `CEulerSolver.cpp` around `neg_pres_or_rho_i` (check whether `< 0.0` changed to `<= 0.0` before dividing by `Density()`), and `roe.cpp` around `RoeSoundSpeed2 <= 0.0`.
3. **`OpenFOAM-dev` gradient and non-orthogonal limiters:** Diff `VenkatakrishnanGradientLimiter.H`, `cellLimitedGrad.C` (`limiter` initialization/clipping), and `limitedSnGrad.C` (`limitCoeff_` default and blending formula).
4. **Standards & full-scale verification (when no cheap diff suffices):** Adoption of Second-Generation Eurocode `EN 1990:2023` or future `ASCE 7` editions requires re-checking partial factor tables (`A1.2(A)/(B)` and Section 2.3.1); verifying quantitative seismic liquefaction displacements or Mach 10 shock stability requires running full compiled `OpenSees` (VELACS) and `SU2`/`OpenFOAM` (Woodward–Colella / MMS) test harnesses rather than isolated unit formulas.
