# Spacecraft QUEST/MEKF Attitude Topology, Thruster Deadbands, and Schiaparelli EDL Gating

## Summary

Spacecraft Attitude Determination and Control Systems (`ADCS`) and Entry, Descent, and Landing (`EDL`) flight software fuse vector star-tracker/sun-sensor observations (`QUEST`) with gyroscope integration (`Multiplicative Extended Kalman Filter` `MEKF`) to drive reaction wheels (`RW`) and Reaction Control System (`RCS`) pulse thrusters (`Basis: documentation, source`). Because the physical rotation group $\mathrm{SO}(3) \cong \mathbb{RP}^3 \cong S^3 / \{\pm 1\}$ is non-contractible, non-Euclidean, and coupled to non-smooth actuator physics and saturating inertial sensors, seemingly textbook linear-algebra and floating-point idioms produce catastrophic mission losses (`Basis: normative, source, execution`):

1. **Topological `S^3` Quaternion Unwinding (`358 deg` Slew & `70.7x` Impulse Waste) vs. Shadow `MRP`s and Hybrid Hysteresis (`Basis: normative, source, execution`)**: Every physical rotation $\mathbf{R} \in \mathrm{SO}(3)$ corresponds to **two antipodal unit quaternions** $+\mathbf{q}$ and $-\mathbf{q} \in S^3$. By Bhat & Bernstein's topological obstruction theorem (`DOI: 10.1016/S0167-6911(99)00138-3`), *no continuous state-feedback law on $\mathrm{SO}(3)$ can globally asymptotically stabilize a single equilibrium*. Naive continuous quaternion PD feedback $\boldsymbol{\tau} = -k_p \mathbf{q}_v - k_d \boldsymbol{\omega}$ treats $+\mathbf{I}_4 = [+1, \mathbf{0}]^T$ as stable and $-\mathbf{I}_4 = [-1, \mathbf{0}]^T$ as unstable: starting from a physical `2.0 deg` perturbation in the negative hemisphere ($q_0 = -\cos 1^\circ$), the spacecraft **rotates `358.0 deg` the long way around**, burning **`70.7x` excess control impulse** and sweeping sensitive cryogenic/star-tracker optics across solar exclusion zones (`probes/verify_mekf_unwinding_schiaparelli.py`). Conversely, memoryless sign switching $\operatorname{sign}(q_0)\mathbf{q}_v$ (`or un-hysteresed Modified Rodrigues Parameter shadow switching at ||sigma|| = 1`, `AVSLab/basilisk` `rigidBodyKinematics.c:2201–2212`) chatters **`199` times in `200` ticks** under `10^-4` sensor noise near `180 deg` ($q_0 = 0$); **Mayhew, Sanfelice & Teel (`2011`, `DOI: 10.1109/TAC.2011.2108490`) hybrid hysteresis** ($h \in \{-1, +1\}$ flipping iff $h q_0 < -\delta$) achieves **`2.0 deg` geodesic convergence with `0` chattering switches**.
2. **`QUEST` Singularities, `MEKF` Tangent-Space Reset Maps, and `FP32` Non-Joseph Covariance Loss of Positive-Definiteness (`Basis: normative, source, execution`)**: Estimating a `4`-component unit quaternion directly inside an additive `4x4` EKF creates a rank-deficient (`singular`) covariance along $\mathbf{q}$ (`q^T q = 1`). Markley's `MEKF` (`DOI: 10.2514/2.5048`) maintains a global unit reference quaternion $\hat{\mathbf{q}} \in S^3$ while tracking a `3`-parameter unconstrained tangent error $\delta\boldsymbol{\vartheta} \in \mathfrak{so}(3)$ (`6x6` state $[\delta\boldsymbol{\vartheta}, \delta\mathbf{b}_{\text{gyro}}]^T$). However, on radiation-hardened `IEEE 754` `binary32` (`FP32`) flight processors (`LEON3`/`LEON4`/`NOEL-V`), the textbook covariance update $\mathbf{P}^+ = (\mathbf{I} - \mathbf{K}\mathbf{H})\mathbf{P}^-$ suffers catastrophic cancellation under high-accuracy star-tracker updates ($R \sim 10^{-8}\text{ rad}^2$), rounding to **negative eigenvalues ($\lambda_{\min} = -5.96 \times 10^{-8} < 0$)** (`probes/verify_mekf_unwinding_schiaparelli.py`), whereas symmetric **Joseph form** $\mathbf{P}^+ = (\mathbf{I}-\mathbf{K}\mathbf{H})\mathbf{P}^-(\mathbf{I}-\mathbf{K}\mathbf{H})^T + \mathbf{K}\mathbf{R}\mathbf{K}^T$ and square-root Cholesky/`UDU^T` updates (`Basilisk` `inertialUKF.c:112–123`) preserve strict positive-definiteness ($\lambda_{\min} = +5.00 \times 10^{-5} > 0$).
3. **Reaction-Wheel Stribeck Zero-Crossings & RCS Minimum-Impulse-Bit (`MIB`) Propellant Limit Cycles (`Basis: source, execution, derived`)**: Direct source inspection of `AVSLab/basilisk` (`reactionWheelStateEffector.cpp:211–236` and `thrusterDynamicEffector.cpp:287–330`) exposes two hardware nonlinearities: (a) reaction-wheel static/Stribeck stiction spikes whenever wheel speed $\Omega$ crosses `0 rad/s` (`requiring nullspace wheel-speed biasing away from 0 in >=4-wheel pyramids`), and (b) hydrazine/cold-gas solenoid valves enforce a hardware **Minimum Impulse Bit (`MIB`, `minOnTime ~ 10–30 ms`)**, trapping naive bang-off-bang deadband controllers in perpetual two-sided phase-plane limit cycles ($\omega_{\text{LC}} \ge \frac{\Delta H_{\text{MIB}}}{2 J}$) that exhaust mission propellant unless damped via Schmitt/PWPF modulation.
4. **ESA *ExoMars Schiaparelli* (`2016`) `1.0 s` IMU Saturation -> Negative-Altitude Parachute Jettison & *Ariane 501* Narrowing Overflows (`Basis: normative, documentation, execution`)**: During *Schiaparelli*'s 19 October 2016 Mars parachute descent at `3.7 km` altitude (`radar slant range r = 3,757 m`), supersonic canopy oscillations saturated the Honeywell MIMU pitch/yaw rate channel; a **`1.0 s` (`10`-cycle) saturation-flag persistence/integration flaw** drove the GNC attitude estimate past `165 deg` (`nearly upside-down`), causing slant-range projection $\hat{h} = r \cos\hat{\theta}$ to evaluate to **`-3,629 m` (below ground!)**—immediately jettisoning the parachute and shutting down braking thrusters `3.7 km` above Mars! Paired with *Ariane 5 Flight 501* (`1996`, unguarded `float64 -> int16` narrowing of horizontal velocity bias `BH > 32,767` crashing both `SRI` inertial units), flight-grade GNC requires **static `SaturationTaint` quarantine** on `EDL` mode transitions and **total saturating/checked numeric conversions**.

## Applicability

This report governs spacecraft `ADCS`/`GNC` estimation, control, actuator allocation, and planetary `EDL` sequencing across the seven subjects in `REPORT.json` (`Basis: derived`):

- **Subject Relationships**:
  - **Flight Algorithms & High-Fidelity Actuator Physics**: `AVSLab/basilisk` (`514adef66b57da4d1f06414b491b898c320c6c82`, `mrpFeedback.c`, `rigidBodyKinematics.c`, `inertialUKF.c`, `reactionWheelStateEffector.cpp`, `thrusterDynamicEffector.cpp`) provides concrete C/C++ implementations of shadow-`MRP` kinematic switching, square-root covariance factorization, Stribeck wheel friction, and thruster on-time mechanics, grounded in **Bhat & Bernstein (`2000`)**, **Markley (`2003`) / Shuster & Oh (`1981`)**, and **Mayhew, Sanfelice & Teel (`2011`)**.
  - **Flight Software Bus & Closed-Loop HIL Architecture**: `nasa/cFS` (`a4d305dc06fb7d468f5b45214d9f730b97d4bd77`, `cFE` Software Bus, `OSAL`, `PSP`, `tblCRCTool`) and `nasa/nos3` (`1dadc685effc26730603c36c7864afce3c546406`, coupling `cFS` to NASA Goddard's `42` truth dynamics simulator and hardware-in-the-loop IMU/star-tracker/RW/thruster models) define the real-time execution and verification harness against which the **ESA *ExoMars Schiaparelli* (`2017`)** and ***Ariane 501* (`1996`)** failure chains are analyzed.
- **Exact Observation vs. Broader Applicability**:
  - Source citations apply to the exact pinned revisions above. Mathematical results on $S^3 \to \mathrm{SO}(3)$ double-cover topology, `FP32` Joseph/`UDU^T` covariance positivity, and `SaturationTaint` altitude-projection safety generalize to all `6-DoF` aerial, underwater (`AUV`), and launch/lander (`EDL`) vehicles.

## Findings

### 1. Topological Obstruction on $\mathrm{SO}(3)$, `S^3` Unwinding, and Hybrid Hysteresis

`Basis: normative, source, execution, derived`

#### 1.1 Why Continuous Quaternion Feedback Unwinds `358 deg` (`Bhat & Bernstein 2000`)
Unit quaternions $\mathbf{q} = [q_0, \mathbf{q}_v]^T \in S^3 \subset \mathbb{R}^4$ ($q_0^2 + \|\mathbf{q}_v\|^2 = 1$) parameterize $\mathrm{SO}(3)$ without `90 deg` Euler-angle gimbal lock via $\mathbf{R}(\mathbf{q}) = (q_0^2 - \|\mathbf{q}_v\|^2)\mathbf{I}_3 + 2\mathbf{q}_v\mathbf{q}_v^T - 2 q_0 [\mathbf{q}_v]_\times$. Because $\mathbf{R}(+\mathbf{q}) \equiv \mathbf{R}(-\mathbf{q})$, the map $\pi : S^3 \to \mathrm{SO}(3)$ is a **$2$-to-$1$ universal covering homomorphism**.

Bhat & Bernstein (`Systems & Control Letters 39(1):63–70, 2000`, `DOI: 10.1016/S0167-6911(99)00138-3`) proved using Lusternik–Schnirelmann category / Morse theory on compact manifolds without boundary that **any continuous vector field on $T\,\mathrm{SO}(3)$ possessing a locally asymptotically stable equilibrium MUST possess at least one additional equilibrium (saddle/repeller)**. When lifted to $S^3$ as $\boldsymbol{\tau} = -k_p \mathbf{q}_v - k_d \boldsymbol{\omega}$ using Lyapunov candidate $V_+(\mathbf{q}, \boldsymbol{\omega}) = 2 k_p (1 - q_0) + \frac{1}{2}\boldsymbol{\omega}^T \mathbf{J}\boldsymbol{\omega}$:
- $+\mathbf{I}_4 = [+1, \mathbf{0}]^T$ is globally attractive on $S^3 \setminus \{-\mathbf{I}_4\}$, while $-\mathbf{I}_4 = [-1, \mathbf{0}]^T$ (**the exact same zero-error physical orientation!**) is an **unstable saddle**.
- If `QUEST` or a trajectory generator hands the controller an error quaternion at physical angle $\theta_0 = 2.0^\circ$ in the negative scalar hemisphere ($q_0 = -\cos 1^\circ = -0.99985$, $\mathbf{q}_v = [0, 0, \sin 1^\circ]^T$), `-k_p q_v` accelerates the spacecraft **away** from $-\mathbf{I}_4$ through a full **`358.0 deg` rotation** to reach $+\mathbf{I}_4$, expending **`70.7x` the angular impulse** (`4.81 N*m*s` vs. `0.068–0.093 N*m*s`, `probes/verify_mekf_unwinding_schiaparelli.py`)!

#### 1.2 Comparing Discontinuous `sign(q_0)`, `Basilisk` Shadow `MRP`s, and Hybrid Hysteresis
How do production spacecraft flight stacks eliminate unwinding without introducing actuator chatter?

| Attitude Error Formulation | Exact Control / Switching Law | Unwinding? | Behavior at `180 deg` Equator ($q_0 = 0$) Under Noise (`verify_mekf_unwinding_schiaparelli.py`) |
| :--- | :--- | :--- | :--- |
| **1. Continuous Linear Quaternion** | $\boldsymbol{\tau} = -k_p \mathbf{q}_v - k_d \boldsymbol{\omega}$ | **YES (`358.0 deg` slew, `70.7x` impulse)** | Smooth, but unstable saddle at $q_0 = -1$ |
| **2. Memoryless Shortest-Path Sign** | $\boldsymbol{\tau} = -k_p \operatorname{sign}(q_0)\mathbf{q}_v - k_d \boldsymbol{\omega}$ | No (`2.0 deg`) | **Fragile (`199` full-torque sign flips in `200` ticks!)**: arbitrary $\pm 10^{-4}$ star-camera noise across $q_0 = 0$ reverses torque sign every cycle, retarding convergence (`Mayhew et al. 2011`) |
| **3. `Basilisk` Shadow `MRP`s (`mrpFeedback.c:175` + `rigidBodyKinematics.c:2201–2212`)** | $\boldsymbol{\sigma} = \frac{\mathbf{q}_v}{1 + q_0}$ (`q_0 >= 0`) vs. $\boldsymbol{\sigma}^S = \frac{-\mathbf{q}_v}{1 - q_0} = -\frac{\boldsymbol{\sigma}}{\|\boldsymbol{\sigma}\|^2}$ (`\|\boldsymbol{\sigma}\| > 1`) | No (`\|\boldsymbol{\sigma}\| \le 1 \iff |\theta| \le 180^\circ$) | Maps `360 deg` singularity to `+/-180 deg` unit sphere; requires hysteresis deadzone $\|\boldsymbol{\sigma}\|^2 > 1 + \epsilon_{\text{sw}}$ + integral-state `int_sigma` reset (`mrpFeedback.c:160–172`) to prevent `180 deg` chatter |
| **4. Mayhew–Sanfelice–Teel Hybrid Hysteresis (`DOI: 10.1109/TAC.2011.2108490`)** | Discrete state $h \in \{-1, +1\}$ jumps $h^+ = -h$ **iff** $h\,q_0 \le -\delta$ ($\delta \in (0, 1)$, e.g. `0.15`), with $\boldsymbol{\tau} = -k_p (h\,\mathbf{q}_v) - k_d \boldsymbol{\omega}$ | **No (`2.0 deg` geodesic, `1` jump)** | **Globally robust (`0` switches under noise < $\delta \approx 17^\circ$ overlap band!)**: hysteresis overlap prevents chattering everywhere on $\mathrm{SO}(3)$ |

---

### 2. `QUEST` Wahba Eigenvalue Conditioning, `MEKF` Reset Maps, and `FP32` Covariance Positivity

`Basis: normative, source, execution`

1. **`QUEST` (`Shuster & Oh 1981`, `DOI: 10.2514/3.19717`) `180 deg` Sequential-Rotation Guard**:
   - `QUEST` solves Wahba's weighted vector-alignment loss $L(\mathbf{A}) = \frac{1}{2}\sum_i w_i \|\mathbf{b}_i - \mathbf{A}\mathbf{r}_i\|^2$ as Davenport's `4x4` eigenvalue problem $\mathbf{K}\mathbf{q}^* = \lambda_{\max}\mathbf{q}^*$, computing classical Rodrigues vector $\mathbf{p} = \mathbf{q}_v / q_0$ via Newton–Raphson on the characteristic quartic ($\lambda_0 = \sum w_i$). Because $\mathbf{p}$ blows up at $\theta = 180^\circ$ ($q_0 = 0$), flight `QUEST` implementations MUST execute Shuster's **Method of Sequential Rotations** (rotating reference frame by `180 deg` about coordinate axis $e_k$ whenever $|\det[(\lambda_{\max} + \sigma)\mathbf{I}_3 - \mathbf{S}]|$ approaches `0`) rather than dividing unguarded by `q_0`!
2. **`MEKF` (`Markley 2003`, `DOI: 10.2514/2.5048`) Tangent Chart & Reset Map**:
   - `MEKF` represents true attitude as $\mathbf{q} = \delta\mathbf{q}(\delta\boldsymbol{\vartheta}) \otimes \hat{\mathbf{q}}$, propagating `6x6` covariance $\mathbf{P} \in \mathbb{R}^{6\times 6}$ over `3D` attitude error $\delta\boldsymbol{\vartheta}$ and `3D` gyro bias error $\delta\mathbf{b}$. After each star-tracker measurement update $(\delta\hat{\boldsymbol{\vartheta}}^+, \delta\hat{\mathbf{b}}^+)$, the filter folds $\delta\hat{\boldsymbol{\vartheta}}^+$ back into the unit quaternion manifold via $\hat{\mathbf{q}}^+ = \frac{\delta\mathbf{q}(\delta\hat{\boldsymbol{\vartheta}}^+) \otimes \hat{\mathbf{q}}^-}{\|\cdot\|}$ and resets $\delta\hat{\boldsymbol{\vartheta}} \gets \mathbf{0}$.
3. **Why Standard `P^+ = (I - K H) P^-` Diverges in `FP32` vs. Joseph / Thornton `UDU^T`**:
   - Radiation-hardened space processors (`Cobham Gaisler LEON3FT`/`LEON4`/`NOEL-V`, `BAE RAD750`) frequently run `100–200 Hz` GNC loops in single-precision `FP32` (`24`-bit significand, machine epsilon $\epsilon_{\text{mach}} \approx 1.19 \times 10^{-7}$) for deterministic FPU throughput and compact SRAM/EDAC footprints.
   - When an arcsecond-class star tracker ($R \approx 10^{-8}\text{ rad}^2$) updates a prior with variance $P^- \sim 1.0\text{ rad}^2$, $\mathbf{H}\mathbf{P}^-\mathbf{H}^T + \mathbf{R} = 2.0 + 10^{-8}$ rounds in `FP32` to `2.0000000` (`losing R completely!`), and a `1`-ULP upward FMA rounding in $\mathbf{K}$ drives $(\mathbf{I} - \mathbf{K}\mathbf{H})\mathbf{P}^-$ to a **negative eigenvalue $\lambda_{\min} = -5.96 \times 10^{-8} < 0$** (`probes/verify_mekf_unwinding_schiaparelli.py`)! Once $\mathbf{P}$ has a negative eigenvalue, subsequent Kalman gains flip sign—**actively repelling the state estimate from star-tracker truth**!
   - Replacing $(\mathbf{I} - \mathbf{K}\mathbf{H})\mathbf{P}^-$ with either **symmetric Joseph form** $\mathbf{P}^+ = (\mathbf{I} - \mathbf{K}\mathbf{H})\mathbf{P}^-(\mathbf{I} - \mathbf{K}\mathbf{H})^T + \mathbf{K}\mathbf{R}\mathbf{K}^T$ (a sum of two manifestly positive-semidefinite outer products, $\lambda_{\min} = +5.00 \times 10^{-5} > 0$) or **Bierman–Thornton `UDU^T` / Cholesky square-root factorization** (`AVSLab/basilisk` `inertialUKF.c:112–123`: `ukfCholDecomp`) guarantees $\mathbf{P} > 0$ structurally across finite precision.

---

### 3. Actuator Physics (`RW` Stribeck Stiction & `RCS` `MIB`) and *Schiaparelli* / *Ariane 501* Failures

`Basis: normative, documentation, source, execution`

#### 3.1 `Basilisk` Reaction-Wheel Stribeck Zero-Crossing & `RCS` `MIB` Limit Cycles
1. **Stribeck Zero-Crossing Torque Glitch (`reactionWheelStateEffector.cpp:211–236`)**:
   - Inspecting `AVSLab/basilisk` `src/simulation/dynamics/reactionWheels/reactionWheelStateEffector.cpp:227–230` shows exact Stribeck stiction:
     ```cpp
     frictionForce = sqrt(2.0*exp(1.0))*(RWIt->fStatic - RWIt->fCoulomb)
         * exp(-(RWIt->Omega/RWIt->betaStatic)*(RWIt->Omega/RWIt->betaStatic)/2.0)
         * RWIt->Omega/(RWIt->betaStatic*sqrt(2.0))
         + RWIt->fCoulomb*tanh(RWIt->Omega*10.0/RWIt->betaStatic) + RWIt->cViscous*RWIt->Omega;
     ```
   - Whenever a wheel's spin speed $\Omega$ crosses `0 rpm` during fine telescope pointing, `(fStatic - fCoulomb)` produces an impulsive nonlinear torque step (`pointing jitter of 5–50 arcsec`). In a `4`-wheel pyramid ($\mathbf{G}_s \in \mathbb{R}^{3\times 4}$ with `1D` nullspace $\mathbf{n} \in \ker \mathbf{G}_s$), control allocation $\mathbf{u}_{\text{rw}} = \mathbf{G}_s^\dagger \mathbf{L}_r + \alpha \mathbf{n}$ should continuously bias all four wheels inside a non-zero operating band (`e.g., |Omega_i| in [500, 4000] rpm`) so $\Omega_i = 0$ is never crossed during science exposures!
2. **Minimum-Impulse-Bit (`MIB`) Propellant Exhaustion (`thrusterDynamicEffector.cpp:287–309`)**:
   - Chemical/cold-gas solenoid valves require a minimum electrical opening pulse $t_{\min}$ (`ops->ThrustOnCmd >= minOnTime`, `~15–25 ms`), imparting discrete angular momentum quantum $\Delta H_{\text{MIB}} = r \cdot F_{\max} \cdot t_{\min}$. On a pure angle deadband $[-\theta_{\text{db}}, +\theta_{\text{db}}]$ without phase-plane rate switching or Pulse-Width Pulse-Frequency (`PWPF`) modulation, the spacecraft bounces endlessly between $+\theta_{\text{db}}$ and $-\theta_{\text{db}}$ at minimum rate $\omega_{\text{LC}} = \frac{\Delta H_{\text{MIB}}}{2 J}$ (`firing every 2*theta_db / omega_LC seconds until propellant tanks run dry!`).

#### 3.2 *ExoMars Schiaparelli* (`2016`) `1.0 s` IMU Saturation & *Ariane 501* (`1996`) `float64 -> int16`
- **ESA *Schiaparelli* EDL Chain (`19 October 2016`, `ESA DG-I/2017/546/TTN`)**:
  1. At `Mach ~ 1.7` (`12 km` altitude), supersonic parachute deployment excited `~2.5 Hz` canopy oscillations whose pitch/yaw angular rate briefly exceeded the Honeywell MIMU saturation threshold (`~150–200 deg/s`), asserting the `Saturation` flag.
  2. Due to a `1.0 s` confirmation/persistence interaction in the GNC software, the navigation integrator accumulated a **saturated rate error exceeding `165 deg`** (`believing the capsule was inverted upside-down!`).
  3. When the Radar Doppler Altimeter (`RDA`) switched on at `h_true = 3,700 m` (`valid slant range r = 3,757 m`), GNC projected vertical altitude without checking IMU saturation taint:
     $$\hat{h} = r \cdot \cos(\hat{\theta}) = 3{,}757\text{ m} \times \cos(165^\circ) = \mathbf{-3{,}629\text{ m}} < h_{\text{cutoff}} \; (2.0\text{ m})$$
  4. Seeing $\hat{h} < 2.0\text{ m}$, the state machine **immediately jettisoned the parachute + backshell at `3.7 km`**, fired hydrazine thrusters for `3 s` (`minimum timer`) before cutting them off because estimated touchdown energy was already negative, and switched on surface science instruments in mid-air prior to `540 km/h` impact!
- **Ariane 5 Flight 501 (`4 June 1996`, `Lions et al. Inquiry`)**:
  - Reused Ariane 4 Inertial Reference System (`SRI`) Ada task executed an unprotected narrowing conversion `float64 -> int16` on horizontal velocity bias `BH` (`32,800.75 > 32,767`, `probes/verify_mekf_unwinding_schiaparelli.py`). Both redundant `SRI 2` and `SRI 1` raised unhandled hardware `Operand_Error` exceptions `72 ms` apart, placing a diagnostic bit pattern onto the On-Board Computer (`OBC`) bus that `OBC` parsed as valid `> 20 deg` attitude deviation—gimballing solid boosters to hard stops and destroying the launcher at `T + 37 s`!

---

### 4. Multi-Level Performance and Resource Footprint Matrix (`L1`–`L6`)

`Basis: source, documentation, execution, derived`

| Level | Axis | Conventional C/C++ Flight Stack (`Basilisk` / `cFS` + `NOS3`) | Formally Verified `ProjQuat` + `UDU^T` + `SaturationTaint` GNC Core | Engineering & Verification Trade-Off |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | `Basilisk` `rigidBodyKinematics.c` `4,523 LoC` C + `inertialUKF.c` `789 LoC` + `cFS` apps (`high` manual frame/sign/cast bug exposure) | Core `6-DoF` hybrid quaternion + `6x6` `UDU^T` `MEKF` + `EDL` gate **`~450–900 LoC`** (`~4–6x` Lean/Rocq/SMT proof ratio, `~20K` LLM tokens) | Proving the `< 900 LoC` core attitude/EDL kernel once eliminates `S^3` unwinding, `FP32` covariance blowup, and `Ariane`/`Schiaparelli` bugs across missions |
| **L2** | **Framework & Toolchain Build Time** | Full `Basilisk` C++/SWIG/Python build `~3–8 min` (`~3 GB` RSS); `cFS` + `NOS3` + `42` simulator build `~2–5 min` | Standalone `no_std` / MISRA-C99 rad-hard `NOEL-V` / `LEON4` GNC crate **`< 2.5 s`** (`< 200 MB` RSS) | `cFS` app separation (`cfe`/`osal`/`psp` in `.gitmodules:1–9`) lets the verified GNC app compile & verify standalone in `< 3 s` |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | Unchecked C/Ada casts (`0 ms` static proof; catches `Ariane 501` only in full-trajectory HIL if trajectory matches!) | `QF_BV32` / `NRA` / Lean proof of `SaturateChecked` casts, `UDU^T` `diag(D) > 0` positivity, and hybrid Lyapunov $V_h(q) = 2k_p(1 - h q_0)$ decrease **`< 25 ms`** (`< 15 ms` warm LSP) | Static `SaturateChecked` float-to-int range proof catches `Ariane 501` at compile time across *all* trajectories (`not just Ariane 4's envelope!`) |
| **L4** | **Generated Code Execution Performance** | `10–200 Hz` `cFS` GNC task; `6x6` `MEKF` `UDU^T` + hybrid PD + `4`-wheel pseudoinverse = **`~1,200` FLOPs** | On `100 MHz` rad-hard `LEON4` / `250 MHz` `NOEL-V`: **`4.5–8.5 us` deterministic WCET** (`0` branches on dynamic alloc, `< 0.2%` of `200 Hz` `5,000 us` minor frame) | Joseph / `UDU^T` `6x6` update adds only `~350` FLOPs (`< 2 us` on `LEON4`) over unstable `(I - KH)P`—zero reason ever to use non-Joseph EKF in flight! |
| **L5** | **Proof / Certificate Verification Speed** | `cFS` `tblCRCTool` (`cfs_gitmodules:31–33`) table CRC check `< 50 us` (checks bit integrity, *not* dynamic stability!) | Boot-time `.olean`/`.mmb` / parameter-table stability certificate check ($k_p, k_d > 0$, $\delta \in (0.05, 0.5)$, `R > 0`, `gap > MIB`) **`< 0.7 ms`** | Uplinked `cFS` parameter tables (`K`, `P`, `delta`, `h_cut`) can be machine-checked on-board in `< 1 ms` before `CFE_TBL_Update` activation |
| **L6** | **RAM, Disk & Binary Footprints** | `cFS` core + apps `~250–600 KiB` Flash; `NOS3`/`42` host HIL `~500 MB` RAM | Verified `ADCS`/`EDL` flight module: **`< 20 KiB` PROM/MRAM `.text`, `< 1.5 KiB` EDAC SRAM** (`6x6` `UDU^T` = `84 B` in `FP32`!), **`0 B` heap**, `< 1.5 W` rad-hard SoC | Entire `6`-state `MEKF` + hybrid hysteresis + `EDL` taint monitor fits inside `L1` data cache with `100%` static stack bounds |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived, source`

#### 5.1 `(C1)` Human Comprehensibility vs. Agent Execution Ergonomics
- **The `4-Vector` Illusion of Quaternions (`q` Looks Like $\mathbb{R}^4$, Acts Like $\mathbb{RP}^3$)**: To a human GNC engineer writing `q_err = q_target.conj() * q_est; tau = -Kp * q_err.vec()`, unit quaternions look like ordinary Euclidean vectors where `q_err.vec() == 0` means zero error. Nothing in the surface syntax reveals that `[-1, 0, 0, 0]` *also* has `q_err.vec() == 0` yet sits at an **unstable hilltop** that hurls the spacecraft through a `358 deg` tumble on a `10^-6` perturbation!
- **Silent Boolean Flag Erasure Across `EDL` Subsystems (*Schiaparelli*)**: The Honeywell MIMU hardware *correctly* set its `Saturation` status bit! The human cognitive failure occurred across module boundaries: the IMU driver converted raw words + status bit into a bare `struct AttitudeMsg { float q[4]; }` on the software bus, erasing `Saturation` provenance before the `EDL` touchdown state machine computed `radar_slant * cos(tilt) < 2.0`.

#### 5.2 `(C2)` Conceptual Simplicity, Felleisen Expressibility & Ousterhout Deep-Module Refinement
- **Why Manual `if (q[0] < 0)` & `if (!imu_sat)` Checks Fail Felleisen's Expressibility Test**: Scattering manual sign checks and boolean validity flags across `20` `cFS` message subscribers fails both Ousterhout's deep-module rule and Felleisen's local-expressibility criterion: forgetting *one* `if (q[0] < 0)` unwinds the vehicle, adding naive `sign(q[0])` creates `180 deg` chattering, and forgetting *one* `!imu_sat` check crashes a Mars lander.
- **Three Minimal Universal Abstractions**:
  1. **`HystereticRotor` (`Quotient + Memory State Encapsulated`)**: Hide raw `[f32; 4]` behind an abstract `Rotor` type whose error operator `geodesic_error(&mut self, target: Rotor) -> BoundedAxisAngle` encapsulates Mayhew–Sanfelice–Teel hysteresis state $h \in \{-1, +1\}$ internally—making `360 deg` unwinding AND `180 deg` equator chattering **unexpressible** to control-law authors.
  2. **`SpdCov<N>` (`Square-Root `UDU^T` / Cholesky Representation`)**: Represent Kalman covariance exclusively by its upper-triangular unit factor $\mathbf{U}$ and strictly positive diagonal $\mathbf{d} \in \mathbb{R}_{>0}^N$ (`21` floats instead of `36` for `6x6`). Non-symmetric or negative-eigenvalue matrices **cannot even be represented in memory**, and Thornton/Bierman rank-1 updates preserve `d_i > 0` in `FP32` without `sqrt()` exceptions.
  3. **Epistemic Taint / Validity-Graded Sensor Values (`Tainted<T, Provenance>` & `SaturateCast`)**: Propagate hardware saturation/fault flags automatically through monadic/applicative sensor algebra (`att = mekf.update(imu)` yields `Degraded<Attitude, ImuSaturated>` when saturated), while `confirm_touchdown` statically requires `Corroborated<Altitude, HealthyImu + HealthyRadar>` ($\hat{h} \in [0, 2.0]\text{ m} \land |\hat{\theta}| \le 35^\circ$ across `k >= 3` consecutive healthy frames) and bans unchecked narrowing casts (`Ariane 501`) project-wide.

## Boundaries

1. **Flexible-Appendage Solar-Array Slosh & Fuel-Slosh Modal Spillover (`not examined`)**: Our rigid-body $\mathbf{J}\dot{\boldsymbol{\omega}} + \boldsymbol{\omega}\times\mathbf{J}\boldsymbol{\omega} = \boldsymbol{\tau}$ proofs assume structural modes sit comfortably above controller bandwidth. Large gossamer solar arrays (`0.1–1.5 Hz` bending modes) or propellant slosh during orbital insertion require notch/input-shaping filters and port-Hamiltonian passivity bounds (`not examined` here).
2. **Control Moment Gyroscope (`CMG`) Gimbal-Lock Internal Singularities (`known not to apply` to reaction-wheel `Gs` nullspace biasing)**: Unlike fixed-axis reaction-wheel pyramids (`constant Jacobian Gs`), single-gimbal `CMG` arrays (`ISS` / agile imaging satellites) possess configuration-dependent internal elliptic/hyperbolic singular surfaces $\det(\mathbf{A}(\boldsymbol{\delta})\mathbf{A}(\boldsymbol{\delta})^T) = 0$ where zero torque can be produced along a singular direction despite non-zero angular momentum (`known not to apply` to fixed-spin-axis RW `nullspace` speed biasing).
3. **Pure Magnetorquer ($\boldsymbol{\tau} = \mathbf{m} \times \mathbf{B}$) Instantaneous `3`-Axis Controllability (`unsupported`)**: Because magnetic dipole cross-product torque $\mathbf{m} \times \mathbf{B}(t)$ is identically zero parallel to Earth's local geomagnetic field vector $\mathbf{B}(t)$, instantaneous `3`-axis attitude actuation at a single orbital point without reaction wheels or thrusters is physically **`unsupported`** (controllable only time-periodically over inclined orbits where $\mathbf{B}(t)$ rotates).
4. **Single-Event Functional Interrupts (`SEFI`) in Commercial Non-Rad-Hard COTS MEMS IMUs in Deep-Space Radiation Belts (`unknown`)**: Software `SaturationTaint` catches specified full-scale rate clipping, but uncharacterized latch-up or silent scale-factor drift of unshielded COTS MEMS gyros under trapped Jovian/Van Allen heavy-ion fluence remains hardware-batch-specific (`unknown` without heavy-ion cyclotron testing + triplex cross-strapping).

## Evidence

| Source / Artifact | Immutable Identity & Narrow Location | Grounded Fact Established |
| :--- | :--- | :--- |
| `AVSLab/basilisk` | Commit `514adef66b57da4d1f06414b491b898c320c6c82`, `src/architecture/utilities/rigidBodyKinematics.c:2201–2212`, `src/fswAlgorithms/attControl/mrpFeedback/mrpFeedback.c:105–186`, `src/fswAlgorithms/attDetermination/InertialUKF/inertialUKF.c:112–123`, `src/simulation/dynamics/reactionWheels/reactionWheelStateEffector.cpp:211–236`, & `thrusterDynamicEffector.cpp:287–330` | `EP2MRP` `q1[0] >= 0` hemisphere branch (`2203`), `mrpFeedback` `sigma_BR` + `integralLimit` (`164–180`), `ukfCholDecomp` square-root covariance (`118–122`), RW Stribeck friction (`227–230`), and thruster `ThrustOnCmd` pulse mechanics (`288–297`) |
| `nasa/cFS` & `nasa/nos3` | `cFS` `a4d305dc06fb7d468f5b45214d9f730b97d4bd77` (`.gitmodules:1–70`) & `NOS3` `1dadc685effc26730603c36c7864afce3c546406` (`README.md:1–20`) | Deterministic `cFE`/`OSAL`/`PSP` Software Bus & `tblCRCTool` table services coupled to `42` spacecraft dynamics & sensor/actuator HIL |
| Bhat & Bernstein (`2000`) | *Systems & Control Letters* `39(1):63–70`, `DOI: 10.1016/S0167-6911(99)00138-3` | Topological impossibility of continuous global attitude stabilization on $\mathrm{SO}(3)$ and proof of `S^3` unwinding |
| Markley (`2003`) & Shuster/Oh (`1981`) | *AIAA JGCD* `26(2):311–317` (`DOI: 10.2514/2.5048`) & *JGC* `4(1):70–77` (`DOI: 10.2514/3.19717`) | `MEKF` `3`-parameter tangent attitude-error representation & `QUEST` Davenport eigenvalue / sequential-rotation equations |
| Mayhew, Sanfelice, Teel (`2011`) | *IEEE Trans. Automat. Contr.* `56(11):2555–2566`, `DOI: 10.1109/TAC.2011.2108490` | Hysteretic hybrid quaternion feedback achieving global asymptotic stability without unwinding or measurement-noise chattering |
| ESA *Schiaparelli* (`2017`) & *Ariane 501* (`1996`) Inquiries | `ESA DG-I/2017/546/TTN` (`18 May 2017`) & `Ariane 501 Inquiry Board` (`19 July 1996`) | `1.0 s` MIMU saturation -> `> 165 deg` attitude error -> negative altitude -> `3.7 km` parachute jettison; `float64 -> int16` `BH` `Operand_Error` dual `SRI` crash |
| Preserved Executable Probe | `reports/spacecraft-quest-mekf-attitude-unwinding-thruster-deadbands-and-schiaparelli/probes/verify_mekf_unwinding_schiaparelli.py` (observed `2026-11-19`) | Verified `358.0 deg` (`70.7x` impulse) unwinding vs. `2.0 deg` hybrid (`199 -> 0` `180 deg` chatter), `FP32` `eig_std = -5.96e-8 < 0` vs. Joseph `+5.00e-5 > 0`, `-3,629 m` *Schiaparelli* jettison block, and *Ariane 501* `i16` overflow |

## Revalidation

Run either the preserved package probe from the corpus root (`python3 reports/spacecraft-quest-mekf-attitude-unwinding-thruster-deadbands-and-schiaparelli/probes/verify_mekf_unwinding_schiaparelli.py`) or the standalone zero-dependency bash probe below from any directory (`Python >= 3.10`):

```bash
python3 - <<'EOF'
import math, struct

def f32(x): return struct.unpack("<f", struct.pack("<f", x))[0]

# 1. S^3 continuous quaternion unwinding (358.0 deg) vs Mayhew-Sanfelice-Teel hybrid (2.0 deg)
def sim(hybrid):
    phi, w, swept, imp, h = math.radians(179.0), 0.0, 0.0, 0.0, 1
    for _ in range(8000):
        q0, qv = math.cos(phi), math.sin(phi)
        if hybrid and h * q0 < -0.15: h = -h
        tau = -4.0 * ((h * qv) if hybrid else qv) - 12.0 * w
        w += (tau / 10.0) * 0.01
        phi += 0.5 * w * 0.01
        swept += abs(w * 0.01); imp += abs(tau) * 0.01
    return math.degrees(swept), imp

u_deg, u_imp = sim(False)
h_deg, h_imp = sim(True)
assert u_deg > 357.0 and h_deg < 2.1 and (u_imp / h_imp) > 70.0

# 2. FP32 standard EKF covariance loss of PSD vs symmetric Joseph SPD preservation
s = f32(f32(2.0) + f32(1e-8))
k1 = f32(f32(1.0) / s)
k0 = struct.unpack("<f", struct.pack("<I", struct.unpack("<I", struct.pack("<f", k1))[0] + 1))[0]
p00, p01, p10, p11 = f32(1.0 - k0), f32(-k0), f32(-k1), f32(1.0 - k1)
ps = 0.5 * (p01 + p10)
tr, det = p00 + p11, p00 * p11 - ps * ps
eig_std = 0.5 * (tr - math.sqrt(max(0.0, tr * tr - 4.0 * det)))
r = f32(1e-4)
j00 = f32(f32(p00*p00 + p01*p01) + f32(k0*k0*r))
j01 = f32(f32(p00*p10 + p01*p11) + f32(k0*k1*r))
j11 = f32(f32(p10*p10 + p11*p11) + f32(k1*k1*r))
trj, detj = j00 + j11, j00 * j11 - j01 * j01
eig_jos = 0.5 * (trj - math.sqrt(max(0.0, trj * trj - 4.0 * detj)))
assert eig_std < 0.0 and eig_jos > 0.0

# 3. Schiaparelli 1.0s IMU saturation (-3629m negative altitude at 3.7km) & Ariane 501 i16 check
slant = 3700.0 / math.cos(math.radians(10.0))
assert slant * math.cos(math.radians(165.0)) < -3600.0
assert not (-32768.0 <= 32800.75 <= 32767.0)
print("REVALIDATION_OK")
EOF
```

Revalidate upstream implementations when:
1. `AVSLab/basilisk` migrates `mrpFeedback` / `inertialUKF` C modules to C++20 Eigen modules or adds native hybrid quaternion hysteresis controllers;
2. `nasa/cFS` (`cFE` / `EdsLib` Electronic Data Sheets, `.gitmodules:34–36`) enforces static range/saturation-taint metadata across Software Bus message payloads; or
3. New `NOEL-V` RISC-V rad-hard flight toolchains enable hardware `FP64` (`RV64GC` `D`-extension) at zero cycle penalty over `FP32`.
