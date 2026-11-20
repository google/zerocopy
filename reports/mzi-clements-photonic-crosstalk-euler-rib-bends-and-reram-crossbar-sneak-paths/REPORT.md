# Programmable Photonic MZI Meshes, Euler Bend Integer-Grid DRC, and Analog ReRAM/PCM Crossbar Parasitics

## Summary

Analog physical linear-algebra accelerators—spanning programmable silicon-photonic Mach–Zehnder interferometer (MZI) unitary meshes and resistive-memory (ReRAM/PCM) crossbar arrays—fail when software compilation treats hardware primitives as ideal orthogonal/linear operators. Direct source inspection across `gdsfactory` (`7407836dd5d872c704fc06f38562a2ffc88049dc`), `photontorch` (`57296d4972e4f8cc92ce45b20fea9aced7dc4f29`), `meep` (`84cbc56a2e94b90acfa05dee78247b565b68d04c`), `cross-sim` (`b1f4755188ea7b38a71f61075cff7045ab6b589f`), and `aihwkit` (`86681d9dbf47413eb083f1f6414667931a31b3b2`), paired with exact mathematical derivations and standalone numerical probes, establishes four load-bearing engineering findings:

1. **Photonic $U(N)$ Decomposition & Parasitic Coupling:** Clements rectangular meshes halve maximum optical depth from $2N-3$ (Reck triangular) to $N$ and equalize per-path insertion loss (improving fidelity at $N=16$, $0.2\text{ dB}$/MZI from $0.9698$ in Reck to $0.9985$ in a toy Clements/Reck probe), yet remain vulnerable to two distinct defects: (i) uniform directional-coupler split error $\kappa = 0.5 + \delta$ creates an unreachable bar-port null floor $|T_{00}|^2_{\min} = (2\kappa - 1)^2$ ($27.96\text{ dB}$ extinction-ratio ceiling at 52:48, $20.00\text{ dB}$ at 55:45), which `photontorch`'s monolithic `Mzi` omits by construction; and (ii) uncompensated mutual thermo-optic crosstalk $\Delta\Phi = C_{\text{th}} P$ collapses mesh fidelity below $0.03$ for $N \ge 8$ under unit-pitch thermal decay, requiring nonnegative-power inversion $P = C_{\text{th}}^{-1}(\Delta\Phi + 2\pi k) \ge 0$ with monotonic phase-unwrapping margins (e.g., $[\pi, 3\pi]$ operating bias) to avoid $2\pi$ DAC thermal flyback glitches.
2. **Euler Bend Minimum-Radius Guard Bypass & 1 nm DBU Port-Snapping Gaps:** Clothoid partial-Euler bends eliminate the step-curvature discontinuity $\Delta\kappa = 1/R$ of circular arcs at $s=0$, but scaling an Euler bend to match a circular arc's floorplan (`with_arc_floorplan=True`, the default in `gdsfactory`) reduces its minimum radius of curvature $R_{\min}$ to $0.7061\,R_{\text{eff}}$ at $p=0.5$ and $0.5347\,R_{\text{eff}}$ at $p=1.0$ ($90^\circ$ bend). Direct source audit of `gdsfactory/component_functions/bends/bend_euler.py:122,131-132` reveals a concrete defect: `_bend_euler` computes `min_bend_radius = path.info["Rmin"]` yet passes the *effective* `radius` (`Reff`) to `validate_radius(x, radius)`, silently admitting bends whose physical $R_{\min}$ violates `CrossSection.radius_min` by up to $46.5\%$. Separately, extruding non-Manhattan ports onto a $1\text{ nm}$ integer GDSII/OASIS database unit (DBU) grid introduces facet angle errors of $0.057^\circ\text{–}0.094^\circ$ on a $500\text{ nm}$ strip waveguide—exceeding `gdsfactory/get_netlist.py`'s `SmartPortMatcher` default `angle_tolerance = 0.01` degrees by $5.7\times\text{–}9.4\times$.
3. **Crossbar Wire IR-Drop, Input-Dependent 1T1R Nonlinearity & Upstream Noise-Model Defects:** In resistive crossbars with per-cell wire resistance $R_w > 0$ and device resistance $R_{\min}$, the dimensionless severity parameter $\gamma_{\text{IR}} \propto N^2 R_w / R_{\min}$ drives worst-column current droop to $41.1\%$ on a $64\times 64$ array at $R_{\min}=1\text{ k}\Omega, R_w=0.35\,\Omega$ (toy CrossSim SUR probe) and breaks linear superposition in 1T1R / PWM-gated arrays (where inactive rows disconnect access transistors, making the Kirchhoff conductance graph $A(x)$ explicitly input-dependent; up to $15.8\%$ superposition error at $128\times 128$). Direct source inspection of `IBM/aihwkit` reveals (i) `src/aihwkit/inference/noise/reram.py:82-107` writes `self.prog_coeff_g_max_reference = 40.0` instead of `self.coeff_g_max_reference`, causing default Wan-2022 ReRAM noise scaling to silently evaluate `g_max / g_max = 1.0` when `g_max != 40.0 uS`; (ii) `IOParametersIRDropT` disables IR-drop automatically during hardware-aware (HWA) training; and (iii) `rpu_forward_backward_pass.cpp:406-432` replaces Kirchhoff inversion with a single-pass cubic parabolic approximation (`c_i = a*(a*(0.05*a - 0.2) + 0.5)`) whose docstring in `io.py:168` misstates `5e-6` S ($5\,\mu\text{S}$) as `5mS`.
4. **End-to-End Verification Envelopes (`V1–V4`):** Verifying analog photonic and memristive pipelines requires moving beyond idealized algebraic models to certified error envelopes combining `V1` reachability/mutant-kill suites, `V2` 3D FDTD (`Meep`) and SPICE/Kirchhoff cross-checks, `V3` thermal-gradient and power-law conductance drift ($G(t) = G_0 (t/t_0)^{-\nu}$, losing $33.7\%\text{–}39.5\%$ conductance within 24 hours in `aihwkit`'s PCM model) injection, and `V4` KLayout DRC/LVS signoff plus hardware optical-dither calibration replay.

## Applicability

This report characterizes the intersection of five pinned upstream codebases and nine primary peer-reviewed references observed on `2026-11-19`:

- **Photonic layout, routing, and DRC (`gdsfactory/gdsfactory@7407836dd5d872c704fc06f38562a2ffc88049dc`):** Applies to KLayout/kfactory-backed `gdsfactory` layouts using `bend_euler`, `mzi`, `path.euler`, `path.extrude`, `cross_section.utils.validate_radius`, and `get_netlist.SmartPortMatcher`. Findings on `validate_radius` apply specifically when `with_arc_floorplan=True` (the default) and `allow_min_radius_violation=False`. Port snapping calculations assume standard silicon-on-insulator (SOI) foundry DBU $= 1\text{ nm}$ ($0.001\,\mu\text{m}$) and $500\text{ nm}$ strip waveguides.
- **Photonic unitary mesh simulation (`flaport/photontorch@57296d4972e4f8cc92ce45b20fea9aced7dc4f29`):** Applies to `ClementsNxN`, `ReckNxN`, `Mzi`, `DirectionalCoupler`, and `RealisticDirectionalCoupler` in frequency- and time-domain PyTorch scattering-matrix simulations. `photontorch` was last committed in 2022 (`57296d4972e4f8cc92ce45b20fea9aced7dc4f29`), so its behavioral findings characterize that frozen revision and equivalent compact S-matrix simulators.
- **Electromagnetic field and adjoint verification (`NanoComp/meep@84cbc56a2e94b90acfa05dee78247b565b68d04c`):** Applies to 2D/3D FDTD eigenmode S-parameter extraction (`get_eigenmode_coefficients`), Courant-limited time stepping (`Courant = 0.5`), subpixel dielectric averaging (`eps_averaging`, `allow_3d_subpixel`), and `python/adjoint/optimization_problem.py` topology/shape optimization for bends and couplers.
- **Resistive crossbar parasitic & ADC simulation (`sandialabs/cross-sim@b1f4755188ea7b38a71f61075cff7045ab6b589f` and `IBM/aihwkit@86681d9dbf47413eb083f1f6414667931a31b3b2`):** `CrossSim` and `AIHWKIT` are compared as complementary points on the accuracy-vs-throughput Pareto frontier: `CrossSim` solves row/column Kirchhoff IR-drop via successive under-relaxation (`IArray.iterative_solve`) and explicit bit-sliced cores (`BitslicedCore`) with circuit-level ADC models (`SarADC`, `RampADC`, `PipelineADC`, `CyclicADC`), whereas `AIHWKIT` targets GPU-accelerated hardware-aware neural network training (`rpu_forward_backward_pass.cpp`) with empirical PCM (`PCMLikeNoiseModel`, Nandakumar et al. 2019) and ReRAM (`ReRamWan2022NoiseModel`, `ReRamCMONoiseModel`) inference noise/drift models.
- **Scope separation:** Analytical derivations and source citations apply directly to the exact pinned revisions. Standalone pure-Python micro-probes (reproduced inline under `## Evidence`) test the exact equations extracted from those codebases and papers in isolated toy models without invoking compiled GPU kernels (`rpucuda`), `klayout`, or MPI `Meep` binaries; every probe measurement is explicitly labeled as a toy-model execution result.

## Findings

### 1. Clements vs. Reck Unitary MZI Meshes: Splitter Holes, Thermal Crosstalk, and $2\pi$ Flyback

**Basis: normative (Clements et al. 2016; Reck et al. 1994; Bandyopadhyay et al. 2021; Milanizadeh et al. 2019) + source (`flaport/photontorch@57296d4972e4f8cc92ce45b20fea9aced7dc4f29`) + execution (toy model of MZI meshes)**

#### 1.1 Ideal vs. Imperfect $2\times 2$ MZI Transfer Matrix and Unreachable Unitary Holes

An integrated photonic $2\times 2$ Mach–Zehnder interferometer consists of two nominal 50:50 directional couplers (or $2\times 2$ MMIs), an internal arm phase shifter $\theta$, and an external input phase shifter $\phi$. Modeling each coupler with power coupling $\kappa_k = \sin^2(\alpha_k)$ where $\alpha_k = \pi/4 + \epsilon_k$ ($k \in \{1, 2\}$):

$$B(\alpha_k) = \begin{pmatrix} \cos\alpha_k & i\sin\alpha_k \\ i\sin\alpha_k & \cos\alpha_k \end{pmatrix}, \qquad T_{\text{MZI}}(\theta,\phi;\epsilon_1,\epsilon_2) = B(\alpha_2)\begin{pmatrix} e^{i\theta} & 0 \\ 0 & 1 \end{pmatrix}B(\alpha_1)\begin{pmatrix} e^{i\phi} & 0 \\ 0 & 1 \end{pmatrix}.$$

Expanding the bar-port amplitude $T_{00}$ and cross-port amplitude $T_{10}$ (ignoring global phase $e^{i\phi}$):

$$|T_{00}(\theta)|^2 = \cos^2(\alpha_1)\cos^2(\alpha_2) + \sin^2(\alpha_1)\sin^2(\alpha_2) - 2\cos\alpha_1\sin\alpha_1\cos\alpha_2\sin\alpha_2\cos\theta$$
$$|T_{10}(\theta)|^2 = \cos^2(\alpha_1)\sin^2(\alpha_2) + \sin^2(\alpha_1)\cos^2(\alpha_2) + 2\cos\alpha_1\sin\alpha_1\cos\alpha_2\sin\alpha_2\cos\theta.$$

Evaluating the extrema over $\theta \in [0, 2\pi)$ yields exact closed-form reachability bounds (Bandyopadhyay, Hamerly & Englund, *Optica* 2021, DOI `10.1364/OPTICA.424052`):

- **Bar-port minimum transmission:** $\min_\theta |T_{00}|^2 = \cos^2(\alpha_1 + \alpha_2) = \sin^2(\epsilon_1 + \epsilon_2)$.
- **Cross-port minimum transmission:** $\min_\theta |T_{10}|^2 = \sin^2(\alpha_1 - \alpha_2) = \sin^2(\epsilon_1 - \epsilon_2)$.

Crucially, **correlated wafer-scale fabrication bias** (e.g., uniform silicon rib-etch undercut or waveguide-gap shrinkage shifting both directional couplers identically by $\epsilon_1 = \epsilon_2 = \epsilon$) cancels out of the cross-port null ($\min |T_{10}|^2 = 0$), **but adds constructively in the bar-port null**:

$$\min_\theta |T_{00}|^2 = \sin^2(2\epsilon) = (2\kappa - 1)^2, \qquad \text{ER}_{\max} = 10\log_{10}\left(\frac{1}{(2\kappa - 1)^2}\right)\text{ dB}.$$

Every matrix element in $U(N)$ whose Clements/Reck decomposition demands an MZI splitting ratio inside the forbidden disk $|T_{00}|^2 < \sin^2(\epsilon_1 + \epsilon_2)$ or $|T_{10}|^2 < \sin^2(\epsilon_1 - \epsilon_2)$ lies inside an **unreachable unitary hole** near the bar/cross states. Because Haar-random $U(N)$ matrices concentrate their Clements internal angles near high reflectivity (small $\theta$) in the center of the mesh as $N$ grows, fabrication error accumulates with $N$.

In `flaport/photontorch@57296d4972e4f8cc92ce45b20fea9aced7dc4f29`, direct source inspection reveals an important modeling gap:
- `photontorch/components/mzis.py:85-113` (`Mzi.set_S`) hardcodes ideal 50:50 couplers directly into the trigonometric elements (`S[0,:,0,1] = cos_phi1 * cos_theta`, `S[0,:,0,2] = cos_phi1 * sin_theta`, `S[0,:,1,3] = -cos_phi0 * sin_theta`, `S[0,:,2,3] = cos_phi0 * cos_theta`) and assumes zero differential arm delay (`lines 37-38`). It exposes **no** splitter imbalance parameters $\epsilon_1, \epsilon_2$.
- Modeling realistic splitter holes in `photontorch` therefore requires bypassing `Mzi` and composing `DirectionalCoupler(coupling=0.5 + delta)` (`photontorch/components/directionalcouplers.py:61-71`, where `t = (1 - coupling)**0.5`, `k = coupling**0.5`) or `RealisticDirectionalCoupler` (`lines 176-253`, which models quadratic wavelength dispersion of supermode index splitting $\Delta n(\lambda) = n_0 + n_1 \Delta\lambda + \frac{1}{2} n_2 \Delta\lambda^2$ and bend coupling $\kappa_0(\lambda)$ with $\tau = \cos(\kappa_0 + \frac{\pi\Delta n}{\lambda}L)$ and $\kappa = -\sin(\kappa_0 + \frac{\pi\Delta n}{\lambda}L)$).
- **Topology comparison in `photontorch`:** `photontorch/networks/clements.py:182-255` (`ClementsNxN`) instantiates `capacity // 2` pairs of `_Capacity2ClementsNxN` (each containing `N - 1` MZIs) plus a final `_PhaseArray` (or `_MixingPhaseArrayClements` for odd `capacity`), giving $N(N-1)/2$ MZIs at default `capacity = N` with **uniform optical depth $N$**. Conversely, `photontorch/networks/reck.py:74-142` (`ReckNxN`) cascades `N - 1` shrinking `_ReckNxN(N - m)` diagonals, giving the same $N(N-1)/2$ MZI count but **non-uniform optical depth ranging from $1$ to $2N - 3$**. Under uniform per-MZI insertion loss $\alpha_{\text{MZI}}$, Reck's unequal path attenuation distorts the realized transformation away from unitarity (non-proportional scaling of matrix rows/columns), whereas Clements' uniform path depth factors uniform loss out as a global scalar attenuation $10^{-N \alpha_{\text{MZI}}/20} U$, preserving unitary fidelity!

#### 1.2 Mutual Thermo-Optic Crosstalk Matrix $C_{\text{th}}$, Nonnegative Power Inversion, and $2\pi$ DAC Flyback

Thermo-optic silicon micro-heaters ($\text{TiN}$ or doped-Si resistors exploiting silicon's thermo-optic coefficient $dn/dT \approx 1.86 \times 10^{-4}\text{ K}^{-1}$ at $\lambda = 1550\text{ nm}$, requiring $P_\pi \approx 15\text{–}30\text{ mW}$ per $\pi$ phase shift without undercut trenches, or $1\text{–}3\text{ mW}$ with suspended trenches; Bogaerts et al. *Nature* 2020, DOI `10.1038/s41586-020-2764-0`) dissipate heat laterally through the buried oxide (BOX) and silicon substrate. Consequently, the actual vector of phase shifts $\Delta\Phi \in \mathbb{R}^M$ ($M = N(N-1)$ phase shifters) is coupled to the electrical heater power vector $P \in \mathbb{R}_{\ge 0}^M$ through a dense, nonnegative, symmetric (or near-symmetric) thermal conductance coupling matrix $C_{\text{th}}$ (Milanizadeh et al., *J. Lightwave Technol.* 2019, DOI `10.1109/JLT.2019.2892512`):

$$\Delta\Phi = C_{\text{th}} P + \Phi_0, \qquad (C_{\text{th}})_{ii} = \frac{\pi}{P_{\pi,i}}, \qquad (C_{\text{th}})_{ij} > 0 \;\;(i \neq j).$$

Because resistive heaters are **strictly unipolar** ($P_i = V_i^2 / R_i \ge 0$; they cannot actively cool), naive linear inversion $P_{\text{naive}} = C_{\text{th}}^{-1}(\Delta\Phi_{\text{target}} \bmod 2\pi)$ frequently produces negative entries $P_i < 0$ whenever hot neighbors induce more parasitic phase on waveguide $i$ than its wrapped target $\Delta\Phi_i \in [0, 2\pi)$. Two failure modes result:
1. **Uncompensated programming or clamping $P_i \leftarrow \max(0, P_i)$:** Leaves residual crosstalk error $\delta\Phi_i > 0$ on every clamped node. In dense meshes ($N \ge 8$), accumulated phase errors rapidly orthogonalize the actual unitary matrix against the target (fidelity collapsing to $0.026$ at $N=8$ and $0.003$ at $N=16$ in our toy probe below).
2. **$2\pi$ DAC wraparound flyback glitches:** If a continuous phase trajectory crosses $0 \leftrightarrow 2\pi$ and wraps instantaneously by $2\pi$, heater $i$ undergoes a full $2 P_\pi$ power step whose thermal time constant ($\tau_{\text{th}} \approx 5\text{–}50\,\mu\text{s}$ in SOI) is finite and coupled through $C_{\text{th}}$ to neighboring arms, creating a multi-microsecond transient matrix corruption across the entire optical mesh.

**Constrained Nonnegative Thermal Inversion & Operating-Window Invariant:**
Because optical phases are invariant modulo $2\pi$, exact thermal cancellation with strictly positive powers is restored by solving for integer wrap offsets $k \in \mathbb{Z}_{\ge 0}^M$ (minimizing total dissipated power $\mathbf{1}^T P$):

$$\min_{k \in \mathbb{Z}_{\ge 0}^M} \mathbf{1}^T C_{\text{th}}^{-1}(\Delta\Phi_{\text{target}} + 2\pi k) \quad \text{subject to} \quad P_{\min} \le C_{\text{th}}^{-1}(\Delta\Phi_{\text{target}} + 2\pi k) \le P_{\max}.$$

When $C_{\text{th}}$ is strictly diagonally dominant (an $M$-matrix inverse property holds when off-diagonal coupling sum $\sum_{j\neq i} (C_{\text{th}})_{ij} < (C_{\text{th}})_{ii}$), $(C_{\text{th}}^{-1} \mathbf{1})_i > 0$ for all $i$, so a uniform bias shift into the window $[\pi, 3\pi]$ (or integer $k \ge 1$) guarantees $P_i > 0$ everywhere **and** provides a $\pm\pi$ continuous tracking margin without crossing the $0/2\pi$ wrap boundary (at the cost of $+P_\pi$ static bias power per phase shifter). For Bandyopadhyay–Hamerly–Englund (2021) hardware error correction of imperfect splitters ($\epsilon_1, \epsilon_2 \neq 0$), local closed-form adjustment of $\theta_k$ and surrounding external phases $\phi_k$ eliminates first- and second-order splitter error across the entire reachable subset of $U(N)$ without global non-convex gradient descent, provided each MZI's target splitting lies outside the forbidden hole $\sin^2(|\epsilon_1 \pm \epsilon_2|)$.

#### 1.3 Toy-Model Quantitative Verification

**Basis: execution (toy model of MZI meshes, not `photontorch` itself)** — Executed via the standalone pure-Python Clements/Reck toy model (5 random circuits per $N$, normalized Hilbert–Schmidt fidelity $\mathcal{F} = |\operatorname{Tr}(U_{\text{ideal}}^\dagger U_{\text{pert}})|^2 / (N \|U_{\text{pert}}\|_F^2)$):

| Directional Coupler Split | $\epsilon$ (deg) | $\min_\theta |T_{00}|^2$ (Numeric / Analytic) | Max Extinction Ratio (dB) | $\min_\theta |T_{10}|^2$ (Uniform Bias) |
| :--- | ---: | :---: | ---: | ---: |
| 50.5 : 49.5 ($\kappa=0.505$) | $0.29^\circ$ | $0.000100$ / $0.000100$ | $40.00\text{ dB}$ | $3.75 \times 10^{-33}$ |
| 51.0 : 49.0 ($\kappa=0.510$) | $0.57^\circ$ | $0.000400$ / $0.000400$ | $33.98\text{ dB}$ | $3.75 \times 10^{-33}$ |
| 52.0 : 48.0 ($\kappa=0.520$) | $1.15^\circ$ | $0.001600$ / $0.001600$ | $27.96\text{ dB}$ | $3.74 \times 10^{-33}$ |
| 55.0 : 45.0 ($\kappa=0.550$) | $2.87^\circ$ | $0.010000$ / $0.010000$ | $20.00\text{ dB}$ | $3.71 \times 10^{-33}$ |

| Mesh Size $N$ ($M$ MZIs) | Clements 52:48 DC Fidelity (Uncorrected) | Uncompensated Thermal Fidelity ($\ell_{\text{th}}=0.8$) | $C_{\text{th}}^{-1}$ Compensated Fidelity (Shift $k$) | Loss $0.2\text{ dB}$/MZI: Clements Fidelity | Loss $0.2\text{ dB}$/MZI: Reck Fidelity |
| :---: | :---: | :---: | :---: | :---: | :---: |
| $N=4$ ($6$) | $0.9973$ | $0.6805$ | $1.000000$ ($k=1$) | $0.999738$ | $0.999360$ |
| $N=8$ ($28$) | $0.9938$ | $0.0263$ | $1.000000$ ($k=1$) | $0.999166$ | $0.994444$ |
| $N=12$ ($66$) | $0.9911$ | $0.0113$ | $1.000000$ ($k=1$) | $0.998661$ | $0.984942$ |
| $N=16$ ($120$) | $0.9863$ | $0.0032$ | $1.000000$ ($k=1$) | $0.998541$ | $0.969791$ |

---

### 2. Curvature-Continuous Euler Bends, `gdsfactory` Minimum-Radius Guard Bypass, and 1 nm Integer-DBU Port Snapping

**Basis: normative (Vogelbacher et al. 2019) + source (`gdsfactory/gdsfactory@7407836dd5d872c704fc06f38562a2ffc88049dc`; `NanoComp/meep@84cbc56a2e94b90acfa05dee78247b565b68d04c`) + execution (toy model of `gdsfactory` Fresnel math & DBU snapping)**

#### 2.1 Step-Curvature Mode Mismatch vs. Partial-Euler Clothoid Geometry

At the junction between a straight waveguide ($\kappa(s)=0$) and a circular bend of radius $R$ ($\kappa(s)=1/R$), the local eigenmode shifts radially outward toward the outer cladding wall by $\Delta r \propto \frac{n_{\text{eff}}^2 w^4}{\lambda^2 R}$. A step discontinuity $\Delta\kappa = 1/R$ excites higher-order slab/waveguide modes and radiation modes, producing transition insertion loss and inter-modal crosstalk (especially severe in multimode/wide rib waveguides used for low propagation loss).

A symmetric **partial-Euler bend** (Vogelbacher et al., *Optics Express* 27(22):31394–31406, 2019, DOI `10.1364/OE.27.031394`) ramps curvature linearly along arc length $s$ over fraction $p \in (0, 1]$ of the bend angle $\alpha$, holds constant maximum curvature $\kappa_{\max} = 1/R_{\min}$ over the middle $(1-p)\alpha$ circular arc, and ramps linearly back to $\kappa = 0$:

$$\kappa(s) = \begin{cases} s / R_0^2, & 0 \le s \le s_p = R_0\sqrt{p\alpha}, \\ 1 / R_p = \sqrt{p\alpha}/R_0, & s_p \le s \le s_0/2, \end{cases} \qquad \theta(s) = \int_0^s \kappa(\tau)\,d\tau = \frac{s^2}{2 R_0^2}\;\;(s \le s_p).$$

In `gdsfactory/path.py:1668-1842` (`euler()`), the Fresnel clothoid coordinates $(x(s), y(s))$ are computed on normalized scale $R_0 = 1$, mirrored and rotated by $\text{angle} - 180^\circ$ (`lines 1804-1810`), and then rescaled by `scale = radius / Reff if use_eff else radius / Rmin` (`line 1828`), where `Reff = points[-1][1] - tan(end_angle - 90°) * points[-1][0]` (`lines 1822-1823`, with `Reff = points[-1][1] / 2` at `angle == 180°`, `lines 1826-1827`).

#### 2.2 Confirmed Upstream Defect: `gdsfactory` `bend_euler` Checks `Reff` Instead of `Rmin` Against `CrossSection.radius_min`

Direct source inspection of `gdsfactory/gdsfactory@7407836dd5d872c704fc06f38562a2ffc88049dc` exposes a silent DRC/physics-guard bypass:

- In `gdsfactory/components/bends/bend_euler.py:74-85` and `gdsfactory/component_functions/bends/bend_euler.py:50-62`, the default parameters are `p: float = 0.5`, `with_arc_floorplan: bool = True`, and `allow_min_radius_violation: bool = False`.
- Inside `_bend_euler` (`gdsfactory/component_functions/bends/bend_euler.py:113-133`):
  ```python
  path = euler(
      radius=radius,
      angle=angle,
      p=p,
      use_eff=with_arc_floorplan,
      npoints=npoints,
      angular_step=angular_step,
  )
  c = path.extrude(x, all_angle=all_angle)
  min_bend_radius = float(np.round(path.info["Rmin"], 3))
  ...
  if not allow_min_radius_violation:
      validate_radius(x, radius)
  ```
- In `gdsfactory/cross_section/utils.py:427-438`, `validate_radius(xs, radius)` checks `if minimum is not None and radius < minimum:` and formats the error string `f"min_bend_radius {radius} < CrossSection.radius_min {minimum}."`.

**Consequence:** `_bend_euler` explicitly computes `min_bend_radius = float(np.round(path.info["Rmin"], 3))` on line 122, stores it in `c.info["min_bend_radius"]` (line 127), **and then passes the unscaled `radius` (`Reff`) instead of `min_bend_radius` to `validate_radius` on line 132**. Because $R_{\min} < R_{\text{eff}}$ whenever $p > 0$ and `with_arc_floorplan=True`, any caller setting `radius = xs.radius_min` (e.g., $5.0\,\mu\text{m}$ for a standard $220\text{ nm}$ SOI strip waveguide) silently passes `validate_radius` while fabricating a bend apex whose true curvature radius drops far below `radius_min`, causing exponential bend radiation loss $\alpha_{\text{rad}} \propto e^{-c R_{\min}}$:

| $90^\circ$ Partial-Euler Fraction $p$ | Exact Ratio $R_{\min}/R_{\text{eff}}$ | Peak Curvature Ratio $\kappa_{\max}/\kappa_{\text{circ}}$ | Physical $R_{\min}$ when `radius=5.0 um` (`with_arc_floorplan=True`) | `validate_radius(x, radius)` (`radius_min=5.0 um`) |
| :---: | :---: | :---: | :---: | :---: |
| $p = 0.00$ (circular arc) | $1.0000$ | $1.000\times$ | $5.000\,\mu\text{m}$ | Pass (exact) |
| $p = 0.25$ | $0.8316$ | $1.203\times$ | $4.158\,\mu\text{m}$ | **Silent violation** ($-16.8\%$) |
| $p = 0.50$ (`gdsfactory` default) | $0.7061$ | $1.416\times$ | $3.530\,\mu\text{m}$ | **Silent violation** ($-29.4\%$) |
| $p = 0.75$ | $0.6100$ | $1.639\times$ | $3.050\,\mu\text{m}$ | **Silent violation** ($-39.0\%$) |
| $p = 1.00$ (full clothoid) | $0.5347$ | $1.870\times$ | $2.674\,\mu\text{m}$ | **Silent violation** ($-46.5\%$) |

*(Basis: derived + execution [toy model of `gdsfactory/path.py:1668-1842` Fresnel integrals] + source [`bend_euler.py:113-133`, `utils.py:427-438`]).*

#### 2.3 1 nm Integer GDSII/OASIS Grid Snapping, Non-Manhattan Port Gaps, and Connectivity Tolerance Mismatch

GDSII and OASIS mask formats represent polygon vertices as signed 32-bit integers scaled by the database unit (`kcl.dbu = 0.001` $\mu\text{m} = 1\text{ nm}$ in standard silicon photonics PDKs). Inspecting `gdsfactory/path.py:1102-1254` (`extrude`), `gdsfactory/cross_section/utils.py:131-138,401-424`, and `gdsfactory/get_netlist.py:195-314` exposes three grid-discretization invariants:

1. **Integer DBU polygon rounding vs. floating-point port frames:** In `path.extrude()` (`path.py:1180-1201`), upper and lower strip edges are computed in floating point (`points1`, `points2`) and added to `Component` via `c.add_polygon(..., layer=section.layer)`, which snaps every vertex to integer DBU coordinates (`round(x / 0.001)`) when `all_angle=False`. Meanwhile, `bend_euler` explicitly warns if `abs(angle) not in {90, 180}` (`component_functions/bends/bend_euler.py:238-243`), advising `bend_euler_all_angle` (`ComponentAllAngle`, which defers polygon snapping until virtual-cell flattening/GDS export).
2. **Non-Manhattan facet angle & width quantization (inline toy model of $1\text{ nm}$ DBU rounding on $W=500\text{ nm}$ waveguide):**
   - At $0^\circ$ (Manhattan): snapped width $= 500.000\text{ nm}$ ($+0.000\text{ nm}$), facet angle error $= 0.0000^\circ$.
   - At $45^\circ$ (octagonal): snapped width $= 500.632\text{ nm}$ ($+0.632\text{ nm}$), facet angle error $= 0.0000^\circ$ (exact diagonal grid symmetry!).
   - At $15.0^\circ$: snapped width $= 499.223\text{ nm}$ ($-0.777\text{ nm}$), **facet angle error $= 0.0941^\circ$**.
   - At $22.5^\circ$: snapped width $= 500.308\text{ nm}$ ($+0.308\text{ nm}$), **facet angle error $= 0.0670^\circ$**.
   - At $30.0^\circ$: snapped width $= 500.855\text{ nm}$ ($+0.855\text{ nm}$), **facet angle error $= 0.0565^\circ$**.
3. **Connectivity checker & foundry DRC/scattering mismatch:** In `gdsfactory/get_netlist.py:210-254`, `SmartPortMatcher` uses `position_tolerance_dbu = 2` (i.e., strict `< 2 nm` per axis), `width_tolerance = 0.001` $\mu\text{m}$ ($1\text{ nm}$), and `angle_tolerance = 0.01` degrees. When two non-Manhattan polygons meet after independent integer snapping, opposing facet vertices can separate by $1\text{–}2\text{ nm}$ triangular air-sliver gaps or acute-angle notches (failing foundry minimum-gap/minimum-notch DRC, or scattering optical power via high-index-contrast $\text{Si}/\text{SiO}_2$ facet reflections if unmerged). Enforcing **exact Manhattan ($0^\circ, 90^\circ, 180^\circ, 270^\circ$) or octagonal ($45^\circ$ multiples with matched even-DBU centerlines) port-frame closure**—or overlapping extruded segments by $\ge 2\text{ DBU}$ followed by boolean union prior to tape-out—eliminates inter-cell snapping slits. Notably, `gdsfactory/cross_section/utils.py:401-424` (`section_cross_section`) already uses exact integer parity (`strip.width % 2`) to prevent off-grid half-DBU offsets on odd-width strips.

#### 2.4 3D FDTD Verification & Adjoint Bend Optimization in `Meep`

In `NanoComp/meep@84cbc56a2e94b90acfa05dee78247b565b68d04c`:
- `python/simulation.py:1319-1326,1458-1505` enforces Yee-grid stability via `Courant: float = 0.5` ($\Delta t = S \Delta x / c$, requiring $S \le 1/\sqrt{d}$ in $d$ dimensions, or $S \le \min[0.5, 1/(|m|+0.5)]$ in cylindrical coordinates with azimuthal order $m$) and anisotropic subpixel permittivity averaging (`eps_averaging=True`, `subpixel_tol=1e-4`, `subpixel_maxeval=100000`, `allow_3d_subpixel=True`), preventing $O(\Delta x)$ staircasing errors on curved Euler bend sidewalls.
- `python/adjoint/optimization_problem.py:12-244` (`OptimizationProblem`) computes exact electromagnetic sensitivity $\partial f / \partial \rho$ across all $N_{\text{design}}$ pixels using **exactly 2 FDTD runs** (1 forward run + 1 adjoint run with DFT-monitored reverse sources, `states = INIT -> FWD -> ADJ`, `decay_by = 1e-11`), enabling direct 3D Maxwell validation and shape optimization of compact Euler bends and directional couplers for exact 50:50 split across C-band wavelengths ($1530\text{–}1565\text{ nm}$).

---

### 3. ReRAM/PCM Crossbar Wire IR-Drop, Input-Dependent 1T1R Nonlinearity, Drift, and ADC Headroom

**Basis: normative (Sebastian et al. 2020; Nandakumar et al. 2019; Wan et al. 2022) + source (`sandialabs/cross-sim@b1f4755188ea7b38a71f61075cff7045ab6b589f`; `IBM/aihwkit@86681d9dbf47413eb083f1f6414667931a31b3b2`) + execution (toy model of CrossSim SUR & AIHWKIT PCM drift)**

#### 3.1 Block-Tridiagonal Kirchhoff Nodal System vs. Ideal MVM

An $M \times N$ resistive crossbar with conductance matrix $G \in \mathbb{R}_{\ge 0}^{M\times N}$, row interconnect segment resistance $R_{w,\text{row}}$, and column segment resistance $R_{w,\text{col}}$ satisfies Kirchhoff's Current Law (KCL) at every row node $V^r_{i,j}$ and column node $V^c_{i,j}$:

$$\frac{V^r_{i,j} - V^r_{i,j-1}}{R_{w,\text{row}}} + \frac{V^r_{i,j} - V^r_{i,j+1}}{R_{w,\text{row}}} + I_{\text{cell}}(G_{i,j}, V^r_{i,j} - V^c_{i,j}) = 0,$$
$$\frac{V^c_{i,j} - V^c_{i-1,j}}{R_{w,\text{col}}} + \frac{V^c_{i,j} - V^c_{i+1,j}}{R_{w,\text{col}}} - I_{\text{cell}}(G_{i,j}, V^r_{i,j} - V^c_{i,j}) = 0,$$

with boundary conditions $V^r_{i,0} = V_{\text{in},i}$ (or via terminal resistance $R_{p,\text{row,term}}$) and column ADC virtual ground $V^c_{M,j} = 0$ (via $R_{p,\text{col,term}}$). Ordering unknowns by rows/columns yields a symmetric positive-definite (SPD) **block-tridiagonal** $2MN \times 2MN$ nodal conductance system $A(G, V_{\text{in}}) \mathbf{v} = \mathbf{b}(V_{\text{in}})$.

**Critical Distinction — Linear Spatial Distortion vs. True Input-Dependent Nonlinearity:**
- **Purely Ohmic `0T1R` array with grounded inactive rows:** $A$ is independent of $V_{\text{in}}$, so $I_{\text{out}} = G_{\text{eff}}(G, R_w) V_{\text{in}}$ remains linear in $V_{\text{in}}$, **but** $G_{\text{eff}} \neq G$ suffers severe row/column-position-dependent attenuation scaling quadratically with array dimension ($\Delta V / V \sim \frac{1}{2} M N \bar{G} R_w$ in the worst far corner) and **passive sneak-path currents** whenever unselected wordlines/bitlines float or sit at half-select bias ($V/2$ or $V/3$).
- **1T1R access-transistor / PWM-gated / bit-sliced arrays AND nonlinear $I\text{–}V$ devices:** When inactive rows ($x_i = 0$) turn off their 1T1R MOSFET gates ($G_{ij}^{\text{active}}(x_i) = \mathbb{1}[x_i \neq 0] G_{ij}$), or when memristor conduction is nonlinear ($I_{\text{cell}}(G, V)$ in `CrossSim` `IArray._cell_currents`), the nodal matrix $A(G, x)$ **explicitly depends on the input vector $x$**! Consequently, **linear superposition fails**: $I_{\text{out}}(x^{(a)} + x^{(b)}) \neq I_{\text{out}}(x^{(a)}) + I_{\text{out}}(x^{(b)})$, because activating additional rows raises total column wire current $I_{\text{col}}$, increasing column IR drop $V^c_{i,j}$ and attenuating currents contributed by *other* already-active rows!

#### 3.2 Solver Architecture Comparison: `CrossSim` Exact SUR vs. `AIHWKIT` Closed-Form Parabolic IR-Drop

Direct source comparison of `sandialabs/cross-sim@b1f4755188ea7b38a71f61075cff7045ab6b589f` and `IBM/aihwkit@86681d9dbf47413eb083f1f6414667931a31b3b2` reveals sharply different fidelity-vs-speed trade-offs and concrete upstream defects:

| Dimension | `sandialabs/cross-sim` (`b1f47551...`) | `IBM/aihwkit` (`86681d9d...`) |
| :--- | :--- | :--- |
| **IR-Drop Formulation** | Exact iterative Kirchhoff solver via successive under-relaxation (SUR): `NonInterleaved_InputSource.py:75-108` & `Interleaved_InputSource.py:99-139` compute exact row/col cumulative wire drops via `xp.cumsum`, updating `dV += gamma * (dV0 - Vpar - dV)`. | **Fast 1-pass parabolic surrogate** (`src/rpucuda/rpu_forward_backward_pass.cpp:399-433`): $a_i = \frac{n}{G_w/G_{\max}} \sum_j |w_{ij}||x_j|$, $c_i = a_i(a_i(0.05 a_i - 0.2) + 0.5)$, $x'_j = x_j(1 - (1 - j/n)^2)$, $y_i \leftarrow y_i - \text{ir\_drop}\cdot c_i (W x')_i$. Separate time-sliced segmented Thevenin model in `IOParametersIRDropT` (`io.py:259-370`, default `ir_drop_segments=8`). |
| **Convergence / Failure Mode** | `iarray.py:98-120`: if `Verr > Verr_th` after `Niters_max`, raises `RuntimeError`, decays `self.gamma *= 0.98`; fails with `ValueError("Parasitic MVM solver failed to converge")` if `gamma <= 1e-2` (or `RuntimeError("Nans...")` at line 260). | Never diverges iteratively, **but** under-models coupled 2D row+column IR-drop redistribution and is **automatically disabled during HWA training** in `IOParametersIRDropT` (`io.py:287-288`), creating a train/test mismatch unless modeled separately. |
| **Interleaved Differential Cancellation** | `Interleaved_InputSource.py:16-63`: positive and negative weight cells share the summation column with opposite voltage polarities ($\pm V_0$), canceling column currents *locally* before wire IR-drop accumulates. | Differential pair mapped via `SinglePairConductanceConverter` (`pcm.py:76`) or implicit reference offset `v_offset_w_min = -1.0` (`io.py:204`). |
| **Bit-Slicing & ADC Headroom** | `BitslicedCore` (`bitsliced_core.py:19-180`) splits $W_{\text{bits}}$ across `num_slices` sub-arrays (`W_slices[0..Nslices-1]`) with per-slice `ADC` (`ADCRangeLimits.{CALIBRATED, MAX, GRANULAR}`, `xbar_parameters.py:17-31`) and circuit-level `SarADC`, `RampADC`, `PipelineADC`, `CyclicADC` (with op-amp `gain_db`, `sigma_capacitor`, `sigma_comparator`). | Fixed `IOParameters` (`io.py:56,74,105`): default 7-bit DAC (`inp_res = 1/(2^7-2)`), 9-bit ADC (`out_res = 1/(2^9-2)`), `out_bound = 12.0`, iterative `BoundManagementType.ITERATIVE` (`max_bm_factor = 1000`, `max_bm_res = 0.25`) + `NoiseManagementType.ABS_MAX`. |
| **Conductance Drift & Noise** | Configurable `WeightErrorParameters` & `DriftErrorParameters` (`xbar_parameters.py:448-487`), optional `lumped` read-noise approximation (documented as invalid under strong parasitics/nonlinear I-V, `lines 481-483`). | Empirical `PCMLikeNoiseModel` (`pcm.py:89-158`, Nandakumar et al. 2019): $G(t)=G_{\text{prog}}((t+t_0)/t_0)^{-\nu}$, $t_0=20\text{ s}$, $\mu_\nu = \text{clip}(-0.0155\ln(g/g_{\max})+0.0244, 0.049, 0.1)$, plus $1/f$ noise. Also `ReRamWan2022NoiseModel` (4th-order poly at $1\text{ s}, 1\text{ d}, 2\text{ d}$) & `ReRamCMONoiseModel` (`reram.py:26-317`). |

#### 3.3 Confirmed Upstream Defects in `IBM/aihwkit@86681d9dbf47413eb083f1f6414667931a31b3b2`

1. **Silent Reference-Conductance Scaling Bug (`src/aihwkit/inference/noise/reram.py:82-107`):**
   In `ReRamWan2022NoiseModel.__init__`, line 83 sets `self.coeff_g_max_reference = self.g_max` when `coeff_g_max_reference is None`. When `coeff_dic is None` (default Wan et al. 2022 empirical coefficients fitted at $40.0\,\mu\text{S}$), line 94 executes:
   ```python
   self.prog_coeff_g_max_reference = 40.0
   ```
   instead of updating `self.coeff_g_max_reference`. In `_apply_poly` (`line 107`), noise scaling computes:
   ```python
   sig_prog *= self.g_max / self.coeff_g_max_reference
   ```
   which evaluates to `self.g_max / self.g_max == 1.0` for *every* user-chosen `g_max` instead of `g_max / 40.0`! For example, configuring a low-power ReRAM cell with `g_max = 10.0 uS` over-injects programming/drift noise by **$4\times$** unless `coeff_g_max_reference=40.0` is passed explicitly.
2. **Unit-Scale Documentation Error (`src/aihwkit/simulator/parameters/io.py:164-170`):**
   `ir_drop_g_ratio: float = 1.0 / 0.35 / 5e-6` corresponds to $R_w = 0.35\,\Omega$ and $G_{\max} = 5\,\mu\text{S}$ ($R_{\min} = 200\text{ k}\Omega$), yielding $G_w/G_{\max} \approx 5.714 \times 10^5$, yet the docstring on line 168 states *"5mS maximal conductance set state"* (off by $10^3\times$). Engineers reading the docstring rather than the code underestimate wire IR drop severity by three orders of magnitude for low-resistance $1\text{–}10\text{ k}\Omega$ ReRAM filaments.

#### 3.4 Toy-Model Quantitative Verification of Crossbar IR-Drop, 1T1R Superposition Failure, and PCM Drift

**Basis: execution (toy model implementing CrossSim `NonInterleaved_InputSource.py` SUR algorithm and exact `aihwkit/inference/noise/pcm.py:126-154` equations)** — Random normalized conductances $G_{ij} \sim \mathcal{U}[0.1, 1.0]$, comparing $R_{\min}=1\text{ k}\Omega$ (`CrossSim` default `xbar_parameters.py:96`) and $R_{\min}=10\text{ k}\Omega$, with 1T1R active-row gating ($V_{\text{dense}} = \mathbf{1}$ vs. $V_{\text{sparse}} + V_{\text{comp}} = V_{\text{dense}}$, $12.5\%$ vs. $87.5\%$ active rows):

| Array Size & $R_{\min}$ | Wire $R_w$ ($\Omega$/cell) | $R_{p,\text{norm}} = R_w / R_{\min}$ | Relative $L_2$ MVM Error | Worst-Column Current Droop | 1T1R Superposition Error | SUR $\gamma$ / Iterations |
| :--- | ---: | ---: | ---: | ---: | ---: | :---: |
| $32\times 32$, $R_{\min}=1\text{ k}\Omega$ | $0.35\,\Omega$ | $3.5\times 10^{-4}$ | $12.49\%$ | $15.49\%$ | $1.71\%$ | $0.5000$ / $16$ |
| $32\times 32$, $R_{\min}=1\text{ k}\Omega$ | $1.00\,\Omega$ | $1.0\times 10^{-3}$ | $28.60\%$ | $34.65\%$ | $4.09\%$ | $0.5000$ / $15$ |
| $64\times 64$, $R_{\min}=1\text{ k}\Omega$ | $0.35\,\Omega$ | $3.5\times 10^{-4}$ | $34.59\%$ | $41.12\%$ | $5.17\%$ | $0.5000$ / $15$ |
| $64\times 64$, $R_{\min}=1\text{ k}\Omega$ | $2.50\,\Omega$ | $2.5\times 10^{-3}$ | $77.23\%$ | $84.85\%$ | $13.53\%$ | $0.2500$ / $36$ |
| $128\times 128$, $R_{\min}=1\text{ k}\Omega$ | $0.35\,\Omega$ | $3.5\times 10^{-4}$ | $66.24\%$ | $76.05\%$ | $11.08\%$ | $0.5000$ / $72$ |
| $128\times 128$, $R_{\min}=1\text{ k}\Omega$ | $2.50\,\Omega$ | $2.5\times 10^{-3}$ | $92.14\%$ | $96.53\%$ | $15.78\%$ | $0.0625$ / $155$ |
| $32\times 32$, $R_{\min}=10\text{ k}\Omega$ | $0.35\,\Omega$ | $3.5\times 10^{-5}$ | $1.40\%$ | $1.73\%$ | $0.20\%$ | $0.5000$ / $16$ |
| $64\times 64$, $R_{\min}=10\text{ k}\Omega$ | $1.00\,\Omega$ | $1.0\times 10^{-4}$ | $13.40\%$ | $16.61\%$ | $1.86\%$ | $0.5000$ / $16$ |
| $128\times 128$, $R_{\min}=10\text{ k}\Omega$ | $0.35\,\Omega$ | $3.5\times 10^{-5}$ | $17.64\%$ | $21.82\%$ | $2.53\%$ | $0.5000$ / $16$ |
| $128\times 128$, $R_{\min}=10\text{ k}\Omega$ | $2.50\,\Omega$ | $2.5\times 10^{-4}$ | $58.78\%$ | $67.68\%$ | $9.47\%$ | $0.5000$ / $19$ |

Notice the dramatic architectural lever revealed by the table: **raising minimum cell resistance by $10\times$ ($1\text{ k}\Omega \to 10\text{ k}\Omega$) or partitioning a $128\times 128$ tile into four $64\times 64$ bit-sliced sub-arrays** cuts $L_2$ IR-drop distortion by $4\times\text{–}9\times$, restores SUR convergence without $\gamma$ damping, and proportionally reduces peak column current—eliminating ADC clipping headroom collapse (`Icol_max`, `out_bound`)!

Evaluating `aihwkit`'s empirical PCM power-law drift equation (`pcm.py:126-144`, $t_0 = 20\text{ s}$) shows conductance decay $G(t)/G_{\text{prog}}$ across operational retention horizons:

| Relative Conductance $g/g_{\max}$ | Mean Drift Exponent $\mu_\nu$ | $t = 60\text{ s}$ | $t = 1\text{ hr}$ | $t = 1\text{ day}$ | $t = 1\text{ yr}$ |
| :---: | :---: | :---: | :---: | :---: | :---: |
| $0.10$ | $0.0601$ | $0.9201$ ($-8.0\%$) | $0.7317$ ($-26.8\%$) | $0.6047$ ($-39.5\%$) | $0.4242$ ($-57.6\%$) |
| $0.25\text{–}1.00$ (clamped floor) | $0.0490$ | $0.9343$ ($-6.6\%$) | $0.7751$ ($-22.5\%$) | $0.6635$ ($-33.7\%$) | $0.4969$ ($-50.3\%$) |

Because $\mu_\nu$ is **state-dependent** (higher for low-conductance amorphous states than high-conductance crystalline states, `pcm.py:126`), a single scalar global drift-compensation factor (multiplying column output by $\alpha(t)$) cannot remove differential inter-weight drift distortion between small and large weights.

---

### 4. Multi-Level Performance and Resource Footprints (`L1–L6`)

**Basis: source + documentation + derived (order-of-magnitude bounds grounded in cited tools and papers)**

| Level | Silicon Photonics MZI Mesh Stack (`gdsfactory` + `photontorch` + `Meep`) | Analog ReRAM/PCM Crossbar Stack (`CrossSim` + `AIHWKIT`) |
| :--- | :--- | :--- |
| **(L1) Human & Agent Authoring Velocity** | Parametric PDK cells (`gdsfactory`) cut manual mask drawing from weeks to ~50–300 LoC Python per $N\times N$ mesh, but tape-out DRC/LVS debug, thermal-crosstalk calibration scripts, and FDTD component qualification add $3\times\text{–}8\times$ verification code overhead. Port-angle/DBU mismatch errors require manual geometry inspection when `all_angle` cells flatten. | High-level PyTorch drop-in replacement (`aihwkit` `AnalogLinear`) enables model conversion in $<100$ LoC; however, circuit-faithful `CrossSim` co-design (ADC calibration ranges, bit-slicing, parasitic parameter extraction from metal stack) requires $5\text{–}20\times$ more sweep/calibration engineering effort and SPICE correlation. |
| **(L2) Framework & Toolchain Build Time** | `gdsfactory` + `kfactory` + `photontorch`: pure Python/PyTorch wheels install in $<30\text{ s}$ (KLayout C++ build from source: ~5–15 min, ~2–4 GB RAM). `Meep` C++/MPI + Harminv/MPB/HDF5 source build: ~10–25 min on 8 cores, ~4 GB RAM. | `CrossSim`: pure Python/NumPy/CuPy install ($<15\text{ s}$). `AIHWKIT` C++/CUDA `rpucuda` extension build (`src/rpucuda/cuda/*.cu`): ~4–12 min with `nvcc` and PyTorch headers, ~4–8 GB peak compile RAM. |
| **(L3) Compilation, Elaboration & Synthesis Latency** | Clements $U(N)$ algebraic decomposition: $O(N^3)$ flops ($<5\text{ ms}$ for $N=64$). `gdsfactory` GDSII generation for $N=16$ MZI mesh: ~0.5–3 s. `Meep` 3D FDTD single $90^\circ$ SOI bend at $25\text{–}40\text{ px}/\mu\text{m}$: minutes on 8–32 CPU cores; `OptimizationProblem` adjoint step = $2\times$ forward FDTD runtime per iteration (typically 50–150 iterations = hours). | `AIHWKIT` parabolic IR-drop forward pass adds $1$ extra `gemv` (`rpu_forward_backward_pass.cpp:422-425`) per tile ($<10\%$ overhead over GPU GEMM). `CrossSim` SUR parasitic solver adds $15\text{–}155$ full-array `cumsum` iterations per MVM ($15\times\text{–}150\times$ slower than ideal matmul, stalling when $R_w N^2 / R_{\min} \gtrsim 1$ triggers $\gamma$ backoff). |
| **(L4) Generated Code / Hardware Execution Performance** | Optical propagation latency through an $N=32$ Clements mesh ($L \approx 10\text{ mm}$, $n_g \approx 4.2$): $\tau_{\text{opt}} \approx 140\text{ ps}$; modulation bandwidth $10\text{–}50\text{ GHz}$ (electro-optic) vs. **thermal reconfiguration bottleneck** $\tau_{\text{th}} \approx 5\text{–}50\,\mu\text{s}$ ($20\text{–}200\text{ kHz}$ weight refresh; Bogaerts et al. 2020). | Analog crossbar MVM pulse latency: $10\text{–}100\text{ ns}$/tile (Wan et al. 2022, DOI `10.1038/s41586-022-04992-8`, achieves up to tens of TOPS/W on 130 nm CMOS+RRAM), dominated by ADC conversion cycles (SAR: $B$ clock cycles per group; bit-slicing multiplies cycles by `input_bits / slice_size`) and `BoundManagement` re-reads on overflow. |
| **(L5) Verification & Checker Speed** | `gdsfactory` `get_netlist` (`SmartPortMatcher`): milliseconds for $10^2\text{–}10^3$ ports. KLayout DRC/LVS on $1\text{ cm}^2$ photonic reticle: seconds to minutes (polygon count dominated by finely discretized Euler bends: `npoints` vs. `simplify` tolerance). `photontorch` S-matrix check for $N=16$: milliseconds on CPU/GPU. | Analytical Kirchhoff residual check $\|A\mathbf{v} - \mathbf{b}\|_\infty < 10^{-6}$ takes $<1\text{ ms}$ per $128\times 128$ tile; full transistor-level SPICE (`Xyce`/`Ngspice`) netlist verification of one $64\times 64$ crossbar + SAR ADC takes minutes to hours ($10^4\times\text{–}10^6\times$ slower than `CrossSim` SUR). |
| **(L6) RAM, Disk, Area & Power Footprints** | 3D `Meep` FDTD at $30\text{ px}/\mu\text{m}$ over a $20\times 20\times 4\,\mu\text{m}^3$ bend volume ($\sim 4.3\times 10^7$ Yee voxels $\times 6$ field components $\times 8\text{ B}$): ~2–8 GB RAM per run. Silicon die footprint: one thermo-optic MZI is ~$150\text{–}300\,\mu\text{m} \times 50\text{–}100\,\mu\text{m}$ ($N=64$ mesh needs $2016$ MZIs $\approx 1\text{–}3\text{ cm}^2$ reticle limit!) and dissipates $2016 \times 2 \times 20\text{ mW} \approx 80\text{ W}$ static heater power without thermal trenches! | Crossbar tile ($256\times 256$ at $10\text{–}40\,F^2$): $<0.05\text{ mm}^2$ core area, but peripheral ADCs/DACs/drivers consume $60\%\text{–}85\%$ of tile area and energy (Sebastian et al. 2020). `CrossSim` 4D `fast_matmul` batch tensor `(#out, #in, #MVMs, batch)` (`iarray.py:143`) explodes GPU VRAM as $O(M N \cdot W_{\text{out}} H_{\text{out}} \cdot B)$, easily exceeding $16\text{–}40\text{ GB}$ on convolutional layers unless tiled. |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

**Basis: derived + source (`gdsfactory`, `photontorch`, `cross-sim`, `aihwkit`)**

#### 5.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

Across all five repositories, the dominant comprehension hazard is **silent semantic aliasing between idealized mathematical parameters and realization-layer physical quantities**:

- **Parameter-name collisions (`gdsfactory`):** Naming `bend_euler`'s first argument `radius` while flipping its physical meaning between `Rmin` (`with_arc_floorplan=False`) and `Reff` (`with_arc_floorplan=True`, default) directly caused the upstream `validate_radius(x, radius)` bug (`bend_euler.py:132`): even the library's own authors conflated `radius` with `min_bend_radius`! Humans reading `bend_euler(radius=5.0)` assume the bend never curves tighter than $5.0\,\mu\text{m}$.
- **Hidden non-idealities in compact models (`photontorch`, `aihwkit`):** A human or LLM agent instantiating `photontorch.ClementsNxN(N=16)` sees clean unitary convergence because `Mzi` silently enforces exact 50:50 couplers and zero thermal coupling; similarly, an engineer training with `aihwkit`'s `IOParametersIRDropT` can miss the docstring note (`io.py:287-288`) that `ir_drop` is silently disabled during HWA training and active only during evaluation. Diagnostic legibility is also asymmetric: when `CrossSim`'s SUR solver prints `Reduced MVM convergence parameter to: 0.01...` and throws `ValueError("Parasitic MVM solver failed to converge")`, it reports an *algorithmic* relaxation failure rather than the physical root cause ($\gamma_{\text{IR}} = N^2 R_w / R_{\min}$ exceeded the physical voltage-divider regime).
- **Nonlocal reasoning burden:** Both domains break modular local reasoning. Moving one thermo-optic heater by $20\,\mu\text{m}$ perturbs every entry of $C_{\text{th}}^{-1}$; activating one more row in a 1T1R ReRAM crossbar alters the effective weight of every other row in the column. Humans can audit 1D local specifications ($R_{\min} \ge 5\,\mu\text{m}$, $\text{ER} \ge 30\text{ dB}$, $R_w / R_{\min} \le 10^{-4}$), whereas checking coupled $N\times N$ global matrices requires machine-computed certified bounds.

#### 5.2 Simplicity, Orthogonality & Universal Model Refinement (`C2`)

Applying Felleisen macro-expressibility and Ousterhout deep-module tests reveals that photonic meshes, integer-grid layouts, and resistive crossbars share **one unified semantic abstraction**: a **Perturbed Linear Operator with Certified Physical Envelope**:

$$\tilde{\mathcal{L}}(\theta, x) = \mathcal{Q}_{\text{ADC}}\!\left(\mathcal{L}_{\text{phys}}\!\left(\mathcal{P}_{\text{fab}}(\theta), \mathcal{Q}_{\text{DAC}}(x)\right)\right), \qquad \|\tilde{\mathcal{L}}(\theta, x) - \mathcal{L}_{\text{ideal}}(W, x)\| \le \varepsilon_{\text{env}}(N, \delta_{\text{fab}}, C_{\text{th}}, \gamma_{\text{IR}}, t).$$

Rather than bolting ad-hoc special cases onto unrelated scripts (e.g., separate `bend_euler` vs. `bend_euler_all_angle` radius checks, separate `Mzi` vs. `DirectionalCoupler` noise hooks, or separate `IOParameters` vs. `IOParametersIRDropT` training/eval toggles):
1. **Separate geometric floorplan (`Reff`) from curvature invariant (`Rmin`) in the type signature:** Make `BendSpec` explicitly discriminate `FloorplanRadius(Reff)` vs. `MinCurvatureRadius(Rmin)` and enforce `validate_radius(xs, path.info["Rmin"])` unconditionally on the post-construction `Path` invariant—zero consumer boilerplate, zero bypass.
2. **Typed integer-DBU port frames:** Represent layout ports as exact `(x_dbu: int, y_dbu: int, angle_deg: ExactAngle | AllAngle)` so Manhattan/octagonal closure is checked statically at port connection time, while non-Manhattan routes explicitly require an overlap-and-boolean-merge or `ComponentAllAngle` flattening boundary instead of silently generating sub-nanometer facet slits.
3. **Unify crossbar parasitic & noise compilation behind one dimensionless severity invariant:** Expose $\gamma_{\text{IR}} = M N R_w / R_{\min}$ and per-column current bound $I_{\text{col,max}}$ as first-class tile invariants that simultaneously govern (i) automatic sub-array tiling / bit-slicing, (ii) ADC clipping headroom allocation, and (iii) whether a fast surrogate (`aihwkit` parabolic IR-drop) stays within a certified error tolerance $\varepsilon_{\text{surr}}$ of the exact Kirchhoff solve (`CrossSim` SUR / direct sparse LU).

---

### 6. End-to-End Solution and Implementation Validation (`V1–V4`)

**Basis: normative + source + derived**

Formal algebraic proofs of $U(N)$ unitarity or ideal MVM accuracy fail across unmodeled physical reality gaps (wafer etch bias, 3D radiation modes, GDSII grid snapping, metal-line IR drop, conductance relaxation). End-to-end validation requires all four validation tiers:

- **`V1` (Specification Adequacy, Mutation & Non-Vacuity Validation):**
  - *Haar-random $U(N)$ reachability & splitter-hole mutant kill:* Inject systematic $\pm 2\%\text{–}5\%$ directional-coupler split mutants ($\kappa \in [0.45, 0.55]$) and verify that the mesh compiler (i) detects unreachable target unitaries lying inside $|T_{00}|^2 < \sin^2(\epsilon_1 + \epsilon_2)$ rather than silently converging to an erroneous phase vector, and (ii) achieves $<10^{-4}$ infidelity across reachable Haar-random $U(N)$ under Bandyopadhyay–Hamerly–Englund phase correction.
  - *Layout DRC & radius-guard mutant kill:* Mutate `bend_euler` inputs (`radius = xs.radius_min`, `p = 0.5, 1.0`, `with_arc_floorplan=True`) and inject $0.05^\circ$ / $1\text{ nm}$ off-grid port perturbations; verify that the DRC/netlist gate kills $100\%$ of both mutants (which `gdsfactory@7407836dd5d872c704fc06f38562a2ffc88049dc` currently fails on the `bend_euler` `Rmin` mutant!).
  - *Crossbar noise-scaling mutant kill:* Mutate `g_max` away from reference values ($10\,\mu\text{S}, 25\,\mu\text{S}, 40\,\mu\text{S}, 100\,\mu\text{S}$) and verify proportional noise scaling $\sigma(g_{\max}) / g_{\max} = \text{const}$ (which immediately catches `aihwkit`'s `reram.py:94` `prog_coeff_g_max_reference` bug!).
- **`V2` (Lowering, Electromagnetic & Circuit-Solver Cross-Validation):**
  - *3D Maxwell FDTD cross-validation (`Meep`):* Export GDSII polygons of partial-Euler bends, directional couplers, and port junctions into 3D `Meep` (`Courant <= 0.5`, `eps_averaging=True`, grid refinement $20 \to 30 \to 40\text{ px}/\mu\text{m}$) and extract complex S-parameters via `get_eigenmode_coefficients` to confirm $<0.02\text{ dB}$ excess bend loss, $<-40\text{ dB}$ back-reflection at port junctions, and C-band split dispersion against compact `photontorch` S-matrix models.
  - *Transistor-level SPICE (`Xyce`/`Ngspice`) cross-validation:* Compare `CrossSim` SUR and `aihwkit` parabolic/Thevenin IR-drop outputs against extracted parasitic RC+1T1R SPICE netlists across sparse ($10\%$) and dense ($100\%$) input patterns, quantifying worst-case surrogate approximation error vs. exact Kirchhoff currents and SAR/Ramp ADC DNL/INL.
- **`V3` (Thermal Gradient, Drift & Physical Leakage / Reliability Injection):**
  - *Thermo-optic die gradient & $2\pi$ flyback stress:* Inject $+15^\circ\text{C}$ spatial substrate temperature gradients across the $C_{\text{th}}$ model and verify nonnegative power headroom ($P_{\min} \le P_i \le P_{\max}$) and zero transient $2\pi$ flyback spikes during continuous weight updates.
  - *Memristive retention drift & $1/f$ noise injection:* Evaluate inference accuracy across logarithmic time horizons $t \in [1\text{ s}, 1\text{ yr}]$ using empirical `PCMLikeNoiseModel` ($G(t) = G_0((t+t_0)/t_0)^{-\nu}$ with conductance-dependent $\nu(g)$) and `ReRamWan2022NoiseModel` / `ReRamCMONoiseModel` (with `coeff_g_max_reference` fixed), plus ADC clipping/bound-management saturation stress tests under adversarial heavy-tailed activations.
- **`V4` (Foundry Signoff, Hardware-in-the-Loop Calibration Replay & Human Comprehension Audits):**
  - *Foundry DRC/LVS signoff (`KLayout`):* Run rule-deck polygon checks (minimum width, spacing, acute angle, off-grid vertex, notch/sliver) and full layout-versus-schematic netlist equivalence on flattened GDSII/OASIS after all `ComponentAllAngle` transformations.
  - *Hardware optical-dither & crossbar calibration replay:* Replay real chip calibration loops—e.g., low-frequency heater dither/lock-in tracking for $C_{\text{th}}$ identification (Milanizadeh et al. 2019) and periodic PCM reference-column drift recalibration (Sebastian et al. 2020)—against recorded hardware telemetry, paired with `SMoL`-style diagnostic comprehension tests verifying engineers accurately distinguish `Reff` vs. `Rmin`, `5 uS` vs. `5 mS`, and train-vs-eval `IR`-drop toggles.

## Boundaries

- **Direct execution of upstream compiled toolchains (`not examined`):** Neither `klayout`/`gdsfactory`, `Meep` 3D FDTD MPI binaries, `CrossSim` CuPy kernels, nor `AIHWKIT` CUDA (`rpucuda`) kernels were compiled or executed in this environment (which lacks `numpy`, `scipy`, `torch`, and GPU hardware). All numerical tables in Sections 1.3, 2.2, 2.3, and 3.4 are produced by pure-Python standard-library toy models reproducing the exact equations from the pinned upstream files and papers, and are explicitly labeled as such; absolute FDTD bend radiation loss (dB) and full ResNet/Transformer inference accuracy degradation under hardware-aware training were **not examined** via live execution here.
- **Exact foundry back-reflection (-15 dB) from $0.05^\circ$ non-Manhattan facet gaps (`unknown`):** While our 1 nm DBU geometric probe confirms that $15^\circ\text{–}30^\circ$ non-Manhattan $500\text{ nm}$ waveguide facets incur $0.057^\circ\text{–}0.094^\circ$ angular quantization error and sub-nanometer width jumps (exceeding `SmartPortMatcher`'s $0.01^\circ$ tolerance), the exact optical back-reflection power in dB depends strongly on foundry lithography optical proximity correction (OPC), corner rounding radius ($\sim 30\text{–}60\text{ nm}$ in 193 nm DUV), and waveguide confinement; any single universal dB figure is **unknown** without a foundry-calibrated 3D FDTD + lithography-model simulation.
- **Exact fidelity threshold ("below 40% for $N \ge 16$") under thermal crosstalk (`known not to apply` universally without specifying thermal pitch/isolation):** Uncompensated thermal crosstalk fidelity depends exponentially on the ratio of heater pitch to thermal decay length $\ell_{\text{th}}$ and on whether undercut isolation trenches are fabricated. In our toy exponential model with $\ell_{\text{th}} = 0.8$ pitch units, fidelity fell to $0.0263$ already at $N=8$ and $0.0032$ at $N=16$, whereas well-isolated deep-trench meshes ($\ell_{\text{th}} \ll 0.2$) retain far higher fidelity without compensation.
- **Linear superposition failure in purely Ohmic `0T1R` crossbars (`known not to apply` to fixed-conductance grounded-inactive Ohmic grids):** For fixed linear resistances with ideal grounded inactive wordlines, Kirchhoff's equations remain linear in $V_{\text{in}}$ (distorting $G_{\text{eff}} \neq G$ globally, but satisfying $I(x^{(a)}+x^{(b)}) = I(x^{(a)}) + I(x^{(b)})$). Input-dependent nonlinearity specifically arises from 1T1R access-transistor switching ($A(x)$ depends on active row support), nonlinear device/selector $I\text{–}V$ characteristics, or peripheral ADC/driver saturation.
- **Photonic active/nonlinear elements & cryogenic/quantum single-photon loss (`not examined`):** Electro-optic lithium niobate / PN-depletion carrier-plasma MZI phase shifters, silicon-nitride piezo-optomechanical actuators, optical-to-electrical shot/RIN noise budgets, and Hong–Ou–Mandel multi-photon distinguishability were **not examined**.
- **Unsupported upstream features (`unsupported`):** `photontorch`'s monolithic `Mzi` (`mzis.py:85-113`) does not support directional-coupler split errors or arm-length delay dispersion; `aihwkit`'s `ReRamWan2022NoiseModel.apply_drift_noise_to_conductance` (`reram.py:160-161`) explicitly raises `ArgumentError` for any `t_inference` not in `{1.0, 86400.0, 172800.0}` unless custom `coeff_dic` keys are supplied; `aihwkit`'s `IOParametersIRDropT` (`io.py:287-288`) does not support IR-drop during HWA training.

## Evidence

All repository source inspections, paper verifications, and standalone micro-probes were conducted on `2026-11-19` (`2026-11-20T02:06Z` UTC).

### Pinned Primary Source Citations

1. **`gdsfactory/gdsfactory` @ `7407836dd5d872c704fc06f38562a2ffc88049dc`**:
   - `gdsfactory/components/bends/bend_euler.py:73-156` — public wrappers `bend_euler`, `bend_euler_s`, `bend_euler_all_angle`, `bend_euler180` (`p=0.5`, `with_arc_floorplan=True`, `allow_min_radius_violation=False`).
   - `gdsfactory/component_functions/bends/bend_euler.py:50-145,212-258` — `_bend_euler` computes `min_bend_radius = float(np.round(path.info["Rmin"], 3))` (`line 122`), passes effective `radius` to `validate_radius(x, radius)` (`line 132`), and warns when `abs(angle) not in {90, 180}` (`lines 238-243`).
   - `gdsfactory/cross_section/utils.py:131-138,401-438` — integer DBU rounding (`kcl.to_dbu`), odd-DBU parity handling (`section_cross_section`), and `validate_radius` (`lines 427-438`).
   - `gdsfactory/path.py:1102-1254,1668-1842` — `extrude` (`all_angle` polygon extrusion) and `euler()` Fresnel clothoid synthesis (`Rp`, `Reff`, `Rmin`, `scale = radius / Reff if use_eff else radius / Rmin`).
   - `gdsfactory/components/mzis/mzi.py:26-178` — MZI factory (`mzi`, `mzi2x2_2x2`, `mzi_coupler`, `mzi_phase_shifter`).
   - `gdsfactory/get_netlist.py:195-314` — `PortCenterMatcher`, `SmartPortMatcher` (`position_tolerance_dbu=2`, `width_tolerance=0.001`, `angle_tolerance=0.01`), and `FlexiblePortMatcher`.
   - `gdsfactory/routing/validation.py:35-114` — `is_invalid_bundle_topology` crossing/facing check (`angle_tolerance = 1e-10`).
2. **`flaport/photontorch` @ `57296d4972e4f8cc92ce45b20fea9aced7dc4f29`**:
   - `photontorch/networks/clements.py:115-272` — `_Capacity2ClementsNxN` and `ClementsNxN` (rectangular $N$-layer mesh).
   - `photontorch/networks/reck.py:31-159` — `_ReckNxN` and `ReckNxN` (triangular $2N-3$ depth mesh).
   - `photontorch/components/mzis.py:23-113` — `Mzi.set_S` (ideal 50:50 trigonometric S-matrix, zero differential arm delay).
   - `photontorch/components/directionalcouplers.py:25-72,176-253` — `DirectionalCoupler` and `RealisticDirectionalCoupler` (quadratic wavelength dispersion).
3. **`NanoComp/meep` @ `84cbc56a2e94b90acfa05dee78247b565b68d04c`**:
   - `python/simulation.py:233,1319-1326,1419-1505,2124-2149` — `Courant = 0.5`, `eps_averaging`, `subpixel_tol = 1e-4`, `allow_3d_subpixel`, `get_eigenmode_coefficients`.
   - `python/adjoint/optimization_problem.py:12-250` — `OptimizationProblem` forward+adjoint 2-simulation gradient state machine (`decay_by = 1e-11`).
4. **`sandialabs/cross-sim` @ `b1f4755188ea7b38a71f61075cff7045ab6b589f`**:
   - `simulator/circuits/array/iarray.py:18-128,163-261` — `IArray`, `iterative_solve` adaptive SUR relaxation (`self.gamma *= 0.98`, fail threshold `1e-2`), NaN guard.
   - `simulator/circuits/array/NonInterleaved_InputSource.py:16-117` & `Interleaved_InputSource.py:16-145` — exact cumulative row/column wire IR-drop SUR solvers and interleaved differential current cancellation.
   - `simulator/cores/bitsliced_core.py:19-180` — `BitslicedCore` weight bit-slicing across sub-arrays with per-slice ADCs.
   - `simulator/parameters/xbar_parameters.py:17-154,271-401,489-549` — `ADCRangeLimits`, `DeviceParameters` (`Rmin=1000`, `Rmax=10000`), `ArrayParameters` (`Icol_max`), `SarADCParameters`/`RampADCParameters`/`PipelineADCParameters`, `ParasiticParameters` (`Rp_row_norm = Rp_row / Rmin`).
   - `simulator/circuits/adc/adc.py:19-149` — `ADC` dispatch to `QuantizerADC`, `RampADC`, `SarADC`, `PipelineADC`, `CyclicADC`.
5. **`IBM/aihwkit` @ `86681d9dbf47413eb083f1f6414667931a31b3b2`**:
   - `src/aihwkit/inference/noise/pcm.py:27-159` — `PCMLikeNoiseModel` (`prog_coeff = [0.26348, 1.9650, -1.1731]` at `25.0 uS`, `t_0 = 20.0`, `t_read = 250e-9`, `mu_drift`, `sig_drift`, `1/f` read noise).
   - `src/aihwkit/inference/noise/reram.py:26-166,168-317` — `ReRamWan2022NoiseModel` (including `self.prog_coeff_g_max_reference = 40.0` attribute-name bug at line 94 vs. `self.coeff_g_max_reference` at lines 83, 107) and `ReRamCMONoiseModel`.
   - `src/aihwkit/simulator/parameters/io.py:19-370` — `IOParameters` (`inp_res = 1/(2^7-2)`, `out_res = 1/(2^9-2)`, `out_bound = 12.0`, `ir_drop_g_ratio = 1.0 / 0.35 / 5e-6` with `"5mS"` docstring typo at line 168) and `IOParametersIRDropT` (`ir_drop_rs = 0.15`, `ir_drop_segments = 8`, IR-drop disabled in HWA training at lines 287-288).
   - `src/rpucuda/rpu_forward_backward_pass.cpp:399-433` — single-pass cubic parabolic IR-drop approximation (`c_i = a*(a*(0.05*a - 0.2) + 0.5)`).

### Reproducible Toy-Model Probe Command (Pure Python 3 Stdlib)

The numerical results in Sections 1.3, 2.2, 2.3, and 3.4 are reproduced deterministically by running the following self-contained pure-Python probe (`python3 - <<'EOF' ... EOF`):

```python
import cmath, math, random

# 1. Exact 2x2 MZI bar-port extinction ratio under uniform DC split error kappa = 0.5 + delta
for kappa in [0.505, 0.51, 0.52, 0.55]:
    eps = 0.5 * math.asin(2 * (kappa - 0.5))
    a = math.pi / 4 + eps
    # B(a) diag(e^{i theta}, 1) B(a): min |T00|^2 = cos^2(2a) = sin^2(2 eps) = (2*kappa - 1)^2
    min_bar = math.sin(2 * eps) ** 2
    print(f"DC {kappa*100:.1f}:{(1-kappa)*100:.1f} -> min|T00|^2={min_bar:.6f}, ER={-10*math.log10(min_bar):.2f} dB")

# 2. Exact 90-deg partial Euler Rmin/Reff (gdsfactory/path.py:1668-1842)
def fresnel_cs(u, steps=4000):
    h = u / steps
    cs = 1.0 + math.cos(0.5 * math.pi * u * u)
    ss = math.sin(0.5 * math.pi * u * u)
    for k in range(1, steps):
        t, w = k * h, 4.0 if k % 2 else 2.0
        cs += w * math.cos(0.5 * math.pi * t * t)
        ss += w * math.sin(0.5 * math.pi * t * t)
    return (h / 3.0) * cs, (h / 3.0) * ss

for p in [0.25, 0.5, 0.75, 1.0]:
    alpha = math.pi / 2.0
    sp, Rp = math.sqrt(p * alpha), 1.0 / math.sqrt(p * alpha)
    C, S = fresnel_cs(sp / math.sqrt(math.pi))
    xp, yp = math.sqrt(math.pi) * C, math.sqrt(math.pi) * S
    xh = Rp * math.sin(alpha / 2) + xp - Rp * math.sin(p * alpha / 2)
    yh = Rp * (1 - math.cos(alpha / 2)) + yp - Rp * (1 - math.cos(p * alpha / 2))
    Reff = yh + xh  # exact for symmetric 90-deg bend: end_pt = (xh+yh, yh+xh)
    print(f"Euler 90deg p={p:.2f}: Rmin/Reff={Rp/Reff:.4f} (Reff=5.0um -> Rmin={5*Rp/Reff:.3f}um)")

# 3. 1 nm DBU facet angle error on 500 nm strip waveguide
for deg in [15.0, 22.5, 30.0, 45.0]:
    th = math.radians(deg)
    nx, ny = -math.sin(th), math.cos(th)
    s = lambda x, y: (round(x / 0.001) * 0.001, round(y / 0.001) * 0.001)
    st, sb = s(10 + 0.25 * nx, 5 + 0.25 * ny), s(10 - 0.25 * nx, 5 - 0.25 * ny)
    vx, vy = st[0] - sb[0], st[1] - sb[1]
    print(f"Angle {deg:4.1f}deg -> width={math.hypot(vx,vy)*1000:.3f}nm, angle_err={abs(math.degrees(math.atan2(-vx,vy))-deg):.4f}deg")
```

## Revalidation

To cheaply verify whether these findings still hold against newer revisions of the five upstream repositories:

1. **`gdsfactory` `bend_euler` `Rmin` guard check:** Inspect `gdsfactory/component_functions/bends/bend_euler.py` around `validate_radius(...)`. The bypass persists if and only if `_bend_euler` still passes `radius` rather than `min_bend_radius` (or `path.info["Rmin"]`) when `with_arc_floorplan=True`. With `gdsfactory` installed, run a one-line check: `gf.components.bend_euler(radius=5.0, p=0.5, with_arc_floorplan=True, cross_section=gf.cross_section.strip(radius_min=5.0))` — if it succeeds without raising `ValueError`, the bypass remains live.
2. **`gdsfactory` port matcher tolerances:** Diff `SmartPortMatcher.__init__` in `gdsfactory/get_netlist.py` for changes to `position_tolerance_dbu`, `width_tolerance`, or `angle_tolerance`.
3. **`aihwkit` ReRAM scaling bug & IR-drop training toggle:** Grep `prog_coeff_g_max_reference` vs. `coeff_g_max_reference` in `src/aihwkit/inference/noise/reram.py` (fixed when line 94 assigns `self.coeff_g_max_reference = 40.0`) and inspect `IOParametersIRDropT` in `src/aihwkit/simulator/parameters/io.py` and `applyIRDrop` in `src/rpucuda/rpu_forward_backward_pass.cpp`.
4. **`CrossSim` SUR solver & bit-slicing:** Diff `simulator/circuits/array/iarray.py` (`iterative_solve`) and `NonInterleaved_InputSource.py` / `Interleaved_InputSource.py` for replacement of fixed-point SUR by direct sparse/Krylov Kirchhoff solvers.
5. **Full physical revalidation (when no cheap check suffices):** Changes to silicon foundry processes (e.g., $\text{SiN}$ vs. $220\text{ nm}$ SOI, thermal undercut trenches) or new ReRAM material stacks require re-running 3D `Meep` FDTD bend/coupler sweeps and empirical device drift characterization rather than relying on the SOI/PCM constants reported here.
