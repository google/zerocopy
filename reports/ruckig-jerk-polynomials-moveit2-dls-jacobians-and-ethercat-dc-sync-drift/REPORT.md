# Jerk-Limited Trajectory Root Solving, Damped-Least-Squares Jacobian Singularities, and EtherCAT Distributed-Clock Servo Interlocks

## Summary

Closed-loop industrial and surgical robot control pipelines compose three tightly coupled numerical and real-time stages within a `250 us`–`1 ms` (`1–4 kHz`) cycle: (1) online third-order jerk-limited trajectory generation (`pantor/ruckig`), (2) differential inverse kinematics with singularity damping (`orocos/orocos_kinematics_dynamics` and `moveit/moveit2`), and (3) cyclic process-data transmission synchronized to a `64`-bit hardware reference clock (`OpenEtherCATsociety/SOEM`). Primary-source inspection and execution probes establish four cross-layer failure mechanisms and their corresponding invariant repairs:

1. **Dimensional `DBL_EPSILON` Root Collapse in Analytical Cubic/Quartic Solvers (`pantor/ruckig`):** `ruckig::roots::solve_cubic` and `ruckig::roots::solve_quart_monic` (`include/ruckig/roots.hpp:60-283`) compare dimensional intermediate quantities of units $\text{s}^3$, $\text{s}^4$, and $\text{s}^6$ against the dimensionless IEEE-754 `binary64` constant `DBL_EPSILON` ($2.2204 \times 10^{-16}$). For sub-`4 ms` trajectory segments—routine during `1–4 kHz` online target replanning—Cardano's discriminant $yy = p^3/27 + (q/2)^2$ scales as $\mathcal{O}(\Delta t^6) \ll \text{DBL\_EPSILON}$, routing distinct three-real-root cubics such as $(t - 0.001)(t - 0.002)(t - 0.003)$ into the coincident-root `else` branch and dropping the minimum-time root $t_1 = 0.001\text{ s}$. At microsecond scales ($|d| = t_1 t_2 t_3 < 2.22 \times 10^{-16}\text{ s}^3$), premature deflation sets $d \leftarrow 0$, lifting the polynomial above the real axis and losing all positive roots. Nondimensionalizing time ($u = t / T_{\text{scale}} \in [0, 1]$) and isolating roots via Rolle/Sturm derivative brackets refined by safeguarded Newton-bisection (`roots::shrink_interval`, `roots.hpp:343-395`) eliminates all `2,023 / 10,000` multiscale quartic root-drop failures observed in unscaled Ferrari evaluation while bounding worst-case iterations deterministically.
2. **Codimension-2 Step Discontinuities and Un-Damped `NaN` State Mutation in Differential IK (`KDL` and `MoveIt 2`):** In `KDL::ChainIkSolverVel_wdls::CartToJnt` (`orocos_kdl/src/chainiksolvervel_wdls.cpp:158-195`), the damping factor `lambda_scaled = sqrt(1 - (sigmaMin/eps)^2) * lambda` has infinite derivative $\partial \lambda_{\text{scaled}}/\partial \sigma_{\min} \to -\infty$ as $\sigma_{\min} \to \varepsilon^-$, hardcodes `sigmaMin = 0.0` for all chains with fewer than `6` joints, and gates mode-$i$ damping on `fabs(S(i)) < eps` while parameterizing `lambda_scaled` solely by `S(5)`. Near a codimension-2 singularity ($S(5) = 0.001 < \varepsilon = 0.05$, $\lambda = 0.2$), mode `4` suffers an instantaneous **`16.99x` velocity step discontinuity** (`20.00` vs. `1.18 rad/s` per `m/s`) when $S(4)$ crosses $\varepsilon$. Independently, `moveit_servo::velocityScalingFactorForSingularity` (`moveit_ros/moveit_servo/src/utils/common.cpp:301-339`) evaluates the **un-damped** `matrix_s.inverse()` to probe condition-number gradients, producing `Inf`/`NaN` and mutating `robot_state` in place when $\sigma_{\min} = 0$. Per-mode $C^2$-smooth singular-value filtering paired with `IEC 61800-5-2` Safely-Limited Speed (`SLS`) nullspace/task scaling restores bounded joint acceleration and velocity everywhere.
3. **EtherCAT Distributed-Clock (`DC`) Modulo Asymmetry, PI Windup, and Un-Gated `WKC` Actuation (`SOEM`):** At commit `49fc34923b973c17700592319159af22157350c9` (SOEM v2 layout `src/ec_dc.c` and `src/ec_main.c`, refactored from SOEM v1's `soem/ethercatdc.c` and `soem/ethercatmain.c`), `ecx_receive_processdata_group` (`src/ec_main.c:2723-2742`) copies incoming `LRW` datagram bytes into `IOmap` whenever `wkc2 > EC_NOFRAME` even if `wkc < expectedWKC` ($2 N_{\text{rw}} + N_{\text{r}} + N_{\text{w}}$), and SOEM's reference RT loop (`samples/ec_sample/ec_sample.c:46-98`) relies on C signed `%` truncation (failing to wrap negative phase errors $< -T_{\text{cyc}}/2$), omits integrator anti-windup and slew limits on `toff`, and continues calling `ecx_send_processdata` during slave dropouts until an asynchronous `10 ms` monitor thread observes `dowkccheck > 2`.
4. **End-to-End Validation Closure (`V1–V4`):** Formal proofs over idealized real-arithmetic kinematics or synchronous bus models leave four reality gaps—vacuous domain guards (`V1`), floating-point/SIMD lowering drift (`V2`), RTOS packet-drop and clock-step races (`V3`), and continuous mechanical/servo excitation (`V4`)—requiring mutation-tested corner synthesis, outward-rounded Bernstein polynomial envelopes, `PREEMPT_RT` fault-injected `WKC`/`DC` harnesses, and `PSY-TaLiRo`/`VerifAI` Signal Temporal Logic (`STL`) robustness falsification.

## Applicability

This report characterizes the composition of four upstream open-source robotics and industrial fieldbus codebases together with two cyber-physical falsification frameworks and three governing specifications:

- **`pantor/ruckig` (`91085469d2133089c285e2f34541255815390e2c`):** Examined across `include/ruckig/roots.hpp`, `include/ruckig/brake.hpp`, `src/ruckig/brake.cpp`, `src/ruckig/position_third_step1.cpp`, `src/ruckig/position_third_step2.cpp`, `include/ruckig/block.hpp`, and `include/ruckig/profile.hpp`. Findings apply to single- and multi-DoF third-order position/velocity trajectory generation in IEEE-754 `binary64` (`double`) arithmetic, particularly online `1–4 kHz` control loops where remaining displacement $\Delta p$, velocity $\Delta v$, or segment time $t_k$ enters the sub-millisecond regime.
- **`orocos/orocos_kinematics_dynamics` (`b7f433b94b2bc66981ce073e4d14480424b85adc`):** Examined across `orocos_kdl/src/chainiksolvervel_wdls.{hpp,cpp}`, `chainiksolverpos_lma.{hpp,cpp}`, and `chainiksolvervel_pinv.{hpp,cpp}`. Applies to serial kinematic chains (`nj < 6`, `nj == 6`, and redundant `nj > 6`) using weighted Damped Least Squares (`WDLS`) velocity IK or Levenberg-Marquardt (`LMA`) position IK.
- **`moveit/moveit2` (`900e0e42a80d4d096e60864316a16640b0fe9372`, release `2.15.3`):** Examined across `moveit_kinematics/kdl_kinematics_plugin/src/{kdl_kinematics_plugin.cpp,chainiksolver_vel_mimic_svd.cpp,pseudoinverse.hpp}` and `moveit_ros/moveit_servo/src/{servo.cpp,utils/common.cpp,utils/command.cpp}`. Findings distinguish offline pose IK (`solvePseudoinverse` hard singular-value truncation) from real-time Cartesian twist/pose jogging (`moveit_servo`).
- **`OpenEtherCATsociety/SOEM` (`49fc34923b973c17700592319159af22157350c9`):** Examined across `src/ec_dc.c`, `src/ec_main.c`, `include/soem/{ec_dc.h,ec_main.h,ec_type.h}`, and `samples/ec_sample/ec_sample.c`. Note on repository layout across versions: SOEM `1.4.x` placed these modules at `soem/ethercatdc.c` and `soem/ethercatmain.c` with `ec_*` globals, whereas SOEM `2.x` (`49fc34923b973c17700592319159af22157350c9`) relocated them to `src/ec_dc.c` and `src/ec_main.c` using explicit `ecx_contextt *context` state. Both share the same `ECT_REG_DCSYSTIME` / `ECT_REG_DCSTART0` register protocol, `EC_CMD_LRW` + `EC_CMD_FRMW` datagram composition, and `ec_sync` PI synchronization algorithm.
- **`cpslab-asu/psy-taliro` (`887f2dc321e83688796307f8b0abcf22b3a57b4c`, `v3.2.0`) and `BerkeleyLearnVerify/VerifAI` (`7ef383f191cac0cb2d0174829ac2ec75ab7a0f3c`):** Applied as black-box temporal-logic falsification harnesses over closed-loop trajectory + IK + servo plant rollouts under `IEC 61158` and `IEC 61800-5-2` envelopes.

 Host execution probes were run on `x86_64` Linux using `/usr/bin/gcc` (`-O2`, IEEE-754 little-endian) and CPython `3.x` (`sys.float_info.epsilon == 2.220446049250313e-16`).

## Findings

### 1. Third-Order Jerk-Limited Trajectory Polynomials and Multi-DoF Synchronization (`pantor/ruckig`)

#### 1.1 Two-Step OTG Architecture and Pre-Step Braking (`BrakeProfile`)

`Basis: normative + source`

Following Berscheid and Kröger (RSS 2021, DOI `10.15607/RSS.2021.XVII.015`, `arXiv:2105.04830v2`), a single-DoF third-order state-to-state trajectory maps initial state $(p_0, v_0, a_0)$ to arbitrary target state $(p_f, v_f, a_f)$ under asymmetric kinematic constraints $v_{\min} \le v(t) \le v_{\max}$, $a_{\min} \le a(t) \le a_{\max}$, and $|j(t)| \le j_{\max}$ using up to seven constant-jerk bang-zero-bang segments $t = (t_0, \dots, t_6) \in \mathbb{R}_{\ge 0}^7$ with jerk sequence $j_k \in \{-j_{\max}, 0, +j_{\max}\}$ (`ControlSigns::UDDU` or `ControlSigns::UDUD`).

1. **Out-of-Bounds Initial-State Pre-Braking (`src/ruckig/brake.cpp:14-80`):** When replanning online after a sudden constraint tightening or sensor update where $a_0 \notin [a_{\min}, a_{\max}]$ or $v_0 + a_0 |a_0| / (2 j_{\max}) \notin [v_{\min}, v_{\max}]$, `BrakeProfile::get_position_brake_trajectory` prepends at most two analytically closed braking segments `(t[0], t[1])` with `j[0] = +/- jMax` to bring $(v, a)$ back inside the admissible phase-plane envelope before invoking the 7-segment solver. Notice lines `30`, `34`, `50`, and `54` inject a hardcoded `constexpr double eps {2.2e-14}` (`include/ruckig/brake.hpp`) offset (`t[0] = t_to_a_max + eps` for acceleration brake; `std::max(t_to_a_min - eps, 0.0)` for velocity brake) to avoid strict inequality rejection inside `Profile::check`.
2. **Step 1 — Per-DoF Minimum Time and Blocking Intervals (`src/ruckig/position_third_step1.cpp`, `include/ruckig/block.hpp`):** Each DoF $i \in \{1, \dots, D\}$ independently solves candidate profile classes (`ACC0_ACC1_VEL`, `ACC0_VEL`, `ACC1_VEL`, `VEL`, `ACC0_ACC1`, `ACC0`, `ACC1`, `NONE`). Because non-zero target velocity/acceleration $(v_f, a_f)$ can render intermediate durations $t \in (t_{i,\min}, t_{\text{right}})$ infeasible (e.g., an axis must reverse direction if forced to wait), `Block::calculate_block` partitions admissible synchronization times for DoF $i$ into $[t_{i,\min}, \infty) \setminus \{ [a_1, b_1], [a_2, b_2] \}$. Multi-DoF synchronization selects the smallest global $t_{\text{sync}} \ge \max_i t_{i,\min}$ outside every active axis's blocked intervals.
3. **Step 2 — Fixed-Duration Profile Synthesis (`src/ruckig/position_third_step2.cpp`):** Every non-limiting DoF $i$ with $t_{i,\min} < t_{\text{sync}}$ solves a constrained boundary-value problem $\sum_{k=0}^6 t_k = t_{\text{sync}}$ (`PositionThirdOrderStep2::time_acc0_acc1_vel`, `time_acc1_vel`, `time_acc0_vel`, `time_vel`, `time_acc0_acc1`, `time_none`), either stretching coasting/cruise segments at $|j| = j_{\max}$ or scaling down effective jerk $|j| \le j_{\max}$ (`minimize_jerk`).

#### 1.2 Dimensional `DBL_EPSILON` Collapse and Catastrophic Cancellation in `roots.hpp`

`Basis: source + execution + derived`

In `PositionThirdOrderStep1::time_all_none_acc0_acc1` (`src/ruckig/position_third_step1.cpp:130-284`, where line `131` explicitly notes `// this one is in particular prone to numerical issues`) and throughout `PositionThirdOrderStep2` (`src/ruckig/position_third_step2.cpp:93,140,183,225`), candidate segment durations $t$ are obtained as positive real roots of cubic and monic quartic polynomials via `roots::solve_cubic` (`include/ruckig/roots.hpp:60-149`) and `roots::solve_quart_monic` (`include/ruckig/roots.hpp:198-283`), followed by 1–2 unbracketed Newton steps (`t -= orig / deriv`, e.g., `position_third_step1.cpp:189,220`).

Direct inspection of `include/ruckig/roots.hpp` reveals three dimensional-homogeneity defects where `DBL_EPSILON` ($2^{-52} \approx 2.220446 \times 10^{-16}$) is tested as an **absolute** cutoff on quantities with physical units $\text{s}^k$:

```cpp
// pantor/ruckig @ 91085469d2133089c285e2f34541255815390e2c
// include/ruckig/roots.hpp:63-72, 98-115, 139-146
if (std::abs(d) < DBL_EPSILON) {
    roots.insert(0.0);
    d = c; c = b; b = a; a = 0.0;
}
// ...
const double p = (a * c - bb / 3) * invaa;
const double halfq = (2 * bb * b - 9 * a * b * c + 27 * a * a * d) / 54 * invaa * inva;
const double yy = p * p * p / 27 + halfq * halfq;
if (yy > DBL_EPSILON) { /* 1 real root */ }
else if (yy < -DBL_EPSILON) { /* 3 real roots via acos/atan */ }
else { /* 2 coincident roots: w = 2 * std::cbrt(-halfq) */ }
```

1. **$\mathcal{O}(\Delta t^6)$ Cardano Discriminant Underflow (`roots.hpp:100-146`):** For a monic cubic $(t - t_1)(t - t_2)(t - t_3) = 0$ with roots separated by $\delta$ (e.g., $t_1 = \bar{t} - \delta, t_2 = \bar{t}, t_3 = \bar{t} + \delta$), the depressed parameter is $p = -\delta^2$, $q/2 = 0$, and $yy = -\delta^6 / 27$ (units $\text{s}^6$). Whenever
   $$\delta < (27 \cdot \text{DBL\_EPSILON})^{1/6} \approx 3.856 \times 10^{-3}\text{ s} \quad (3.86\text{ ms}),$$
   $|yy| < \text{DBL\_EPSILON}$, so `yy < -DBL_EPSILON` evaluates to **`false`**. Execution falls into the `else` branch (`roots.hpp:139-146`), computing `w = 2 * cbrt(0) = 0` and returning only `[t_2, t_2]`—**silently discarding the minimum-time root $t_1$ and maximum root $t_3$ across an entire `3.86 ms` window** (nearly `4` control cycles at `1 kHz` or `15` cycles at `4 kHz`).
2. **$\mathcal{O}(t^3)$ Constant-Term Deflation Valley Lift (`roots.hpp:63-72`):** For a monic cubic with three positive roots $t_1 < t_2 < t_3$ satisfying $t_1 t_2 t_3 < \text{DBL\_EPSILON}$ (e.g., $(3, 6, 9)\ \mu\text{s}$, where $|d| = 1.62 \times 10^{-16}\text{ s}^3 < 2.22 \times 10^{-16}$), line `63` unconditionally inserts a spurious `0.0` root and replaces $P(t)$ by $t(t^2 + b t + c)$—equivalent to adding $+|d|$ to $P(t)$. Because the local minimum of $(t - 3\times 10^{-6})(t - 6\times 10^{-6})(t - 9\times 10^{-6})$ at $t \approx 7.73\ \mu\text{s}$ has depth $|-1.039 \times 10^{-17}| \ll |d|$, dropping $d$ lifts the entire positive-axis valley above zero, turning the deflated quadratic discriminant negative ($\Delta = b^2 - 4c = -7.2 \times 10^{-11} < 0$) and **destroying all three real positive roots**.
3. **Quartic Ferrari Resolvent Cancellation (`roots.hpp:223-281`):** In `solve_quart_monic`, `D = y * y - 4 * d` (`line 243`, units $\text{s}^4$) and quadratic factor discriminants `D = p1 * p1 - 4 * q1` (`line 264`, units $\text{s}^2$) use absolute cutoffs `DBL_EPSILON` and `16 * DBL_EPSILON`. When $a_0 \to a_f$ in `polynom_none` (`position_third_step1.cpp:132-141`, where `h2_none = (a0^2 - af^2)/(2*jMax) + (vf - v0) -> 0` drives `polynom_none[3] = -h2_h2 / jMax^2 -> 0`), rounding noise in the resolvent cubic root `y` pushes `y^2 - 4*d` slightly negative or collapses `q1 - q2` in denominator `(a * q1 - c) / (q1 - q2)` (`line 258`), losing valid Step 1 or Step 2 roots and triggering `Result::ErrorExecutionTimeCalculation` (`-101`).

An execution micro-probe (`Basis: execution (line-for-line IEEE-754 binary64 port of pantor/ruckig include/ruckig/roots.hpp:60-283 vs. dimensionless Rolle-bracketed shrink_interval)`) over `10,000` random 4-positive-root monic quartics with log-uniform time scales $t_k \in [10^{-5}, 1.0]\text{ s}$ (`seed = 20261119`) measured:

| Polynomial Solver Strategy | Test Case `(0.001, 0.002, 0.003)` s | Test Case `(3e-6, 6e-6, 9e-6)` s | `10,000`-Quartic Failure Rate (`>1%` $t_{\min}$ Error or Empty) | Max $t_{\min}$ Relative Error | Bounded Iteration / WCET Envelope |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`ruckig::roots::solve_cubic` / `solve_quart_monic` (`roots.hpp:60-283`)** | Returns `[0.002, 0.002]` (**misses `0.001` & `0.003`**) | Returns `[0.0]` (**misses all 3 true roots**) | **`2,023 / 10,000` (`20.23%`)** | **`4.362` (`436%`)** or empty `[]` | Branch-fixed radicals (`~35–90 ns`), non-total on ill-conditioned inputs |
| **Dimensionless Horizon Scaling ($u = t / T_{\text{scale}}$) + Rolle/Sturm Bracket + `shrink_interval` (`roots.hpp:343-395`)** | Returns `[0.001, 0.002, 0.003]` (exact to `< 1e-15`) | Returns `[3e-6, 6e-6, 9e-6]` (exact to `< 1e-15`) | **`0 / 10,000` (`0.00%`)** | **`4.213e-10`** | $\le 64$ safeguarded Newton-bisection steps/root (`~280–620 ns`/quartic), zero heap |

Crucially, `pantor/ruckig` **already contains** the safeguarded Newton-bisection primitive `roots::shrink_interval` (`include/ruckig/roots.hpp:343-395`), which maintains a strict sign-change bracket `fl * fh <= 0` and falls back to bisection `dx = (h - l) / 2` whenever the Newton step leaves `[l, h]` or shrinks slower than half-speed (`abs(2 * f) > abs(dxold * df)`). Replacing raw analytical radicals on `[t_min, t_max]` with dimensionless scaling $u = (t - t_{\min}) / (t_{\max} - t_{\min}) \in [0, 1]$ plus recursive Rolle critical-point bracketing ($P''' \to P'' \to P' \to P$, requiring only linear, quadratic, and 3-bracket evaluations without division by `q1 - q2`) makes root isolation unconditionally total on compact intervals while guaranteeing a pre-computed `BrakeProfile` + hold fallback if boundary kinematics are infeasible.

---

### 2. Damped Least-Squares (`DLS`) Jacobian Singularities and Wrist-Flip Whip (`KDL` and `MoveIt 2`)

#### 2.1 Mathematical Formulation vs. Upstream SVD Implementations

`Basis: normative + source + derived`

Given manipulator forward kinematics $x = f(q)$ with Jacobian $J(q) = \partial f / \partial q \in \mathbb{R}^{m \times n}$ ($m \le 6$) and singular value decomposition $J = \sum_{i=1}^r \sigma_i u_i v_i^\top$ ($\sigma_1 \ge \dots \ge \sigma_r \ge 0$), Wampler (`IEEE TSMC 1986`) and Nakamura & Hanafusa (`ASME JDSMC 1986`) replace the discontinuous Moore-Penrose pseudoinverse $J^\dagger = \sum_{\sigma_i > 0} \sigma_i^{-1} v_i u_i^\top$ with the Levenberg-Marquardt / Damped Least-Squares minimizer of $\|\dot{x} - J\dot{q}\|_2^2 + \lambda^2 \|\dot{q}\|_2^2$:

$$\dot{q}_{\text{DLS}} = J^\top (J J^\top + \lambda^2 I_m)^{-1} \dot{x} = \sum_{i=1}^m \frac{\sigma_i}{\sigma_i^2 + \lambda_i^2} (u_i^\top \dot{x})\, v_i, \qquad \max_{\|\dot{x}\|_2 \le V_x} \left| \frac{\sigma_i}{\sigma_i^2 + \lambda_i} \right| \text{ bounded by } \frac{1}{2\lambda_i} \text{ at } \sigma_i = \lambda_i.$$

Across `orocos_kdl` and `moveit2`, four distinct inverse-kinematics implementations exhibit sharply divergent singularity behaviors:

| Implementation & Exact Source Coordinates | Inversion / Damping Formula | Continuity Across $\sigma_i = \varepsilon$ | Behavior at Exact Singularity ($\sigma_{\min} = 0$) | Multi-Singularity & Redundancy (`nj != 6`) Quirks |
| :--- | :--- | :--- | :--- | :--- |
| **`KDL::ChainIkSolverVel_wdls::CartToJnt`** (`orocos_kdl/src/chainiksolvervel_wdls.cpp:158-195`) | $\lambda_s = \lambda \sqrt{1 - (\sigma_{\min}/\varepsilon)^2}$ if $\sigma_{\min} < \varepsilon$; mode gain $\sigma_i / (\sigma_i^2 + \lambda_s^2)$ if $|\sigma_i| < \varepsilon$ else $1/\sigma_i$ | **$C^0$ cusp** on $i=5$ ($\partial \lambda_s / \partial \sigma_5 \to -\infty$); **discontinuous ($C^{-1}$)** on $i < 5$ when $\sigma_5 < \varepsilon$! | Bounded ($0$ gain on null mode), returns `E_CONVERGE_PINV_SINGULAR` | Line `162`: sets `sigmaMin = 0.` whenever `jac.columns() < 6`, permanently locking full damping $\lambda_s = \lambda$ |
| **`KDL::ChainIkSolverPos_LMA::CartToJnt`** (`orocos_kdl/src/chainiksolverpos_lma.cpp:225-305`) | Nielsen trust-region update: $\sigma_j / (\sigma_j^2 + \lambda)$ (`line 232`, note $\lambda$ not $\lambda^2$), $\lambda \leftarrow \lambda \max(1/3, 1 - (2\rho - 1)^3)$ | Smooth per-iteration trust-region adaptation ($C^\infty$ in $\sigma_j$ for fixed $\lambda > 0$) | Terminates cleanly with `E_GRADIENT_JOINTS_TOO_SMALL` (`line 273`) when $J^\top e \approx 0$ | Iterative pose solver (up to `maxiter` SVDs); unsuitable for un-seeded deterministic `4 kHz` velocity streaming |
| **`moveit2` `solvePseudoinverse`** (`moveit_kinematics/kdl_kinematics_plugin/src/pseudoinverse.hpp:18-34`) | Eigendecomposition of $N = J J^\top$; hard cutoff $\sigma_i > \tau \sigma_{\max} \ ? \ \mu_i^{-1} : 0$ (`line 31`) | **Discontinuous ($C^{-1}$)** step jump of size $1 / (\tau \sigma_{\max})$ at $\sigma_i = \tau \sigma_{\max}$; squares condition number $\kappa(JJ^\top) = \kappa(J)^2$ | Drops singular eigenvector cleanly (`0.0`), losing `FP64` precision below $\sigma_i \approx 10^{-8} \sigma_{\max}$ | Fast $6 \times 6$ `SelfAdjointEigenSolver`, used inside random-restart pose IK (`searchPositionIK`) |
| **`moveit_servo` `velocityScalingFactorForSingularity`** (`moveit_ros/moveit_servo/src/utils/common.cpp:282-378`) | Uniform scalar `velocity_scale` $\in [0, 1]$ linear in $\kappa(J) = \sigma_1 / \sigma_m$, probing direction via **un-damped** `V * S.inverse() * U^T` (`line 306`) | Asymmetric hysteresis jump when $\text{dot}(u_m, \Delta x)$ changes sign (`upper_threshold` switches between `hard_stop` and `leaving` multiplier, `lines 348-356`) | **`matrix_s.inverse()` divides by `0.0` (`Inf`/`NaN`), polluting `robot_state` via `setJointGroupPositions` (`line 327`)!** | Freezes **all** Cartesian DOFs (`velocity_scale = 0.0`) at `hard_stop_singularity_threshold`, even orthogonal motions away from singularity |

#### 2.2 Source-Verified Codimension-2 Jump in `KDL` and `NaN` Probe Corruption in `MoveIt Servo`

`Basis: source + execution`

Two non-obvious implementation bugs explain field reports of "wrist-flip joint whip" ($q_4, q_6$ counter-rotating at $> 8\text{ rad/s}$ near spherical-wrist alignment $q_5 \approx 0$) and sudden servo halts:

1. **Cross-Mode Coupling in `ChainIkSolverVel_wdls` (`chainiksolvervel_wdls.cpp:158-195`):**
   ```cpp
   // orocos/orocos_kinematics_dynamics @ b7f433b94b2bc66981ce073e4d14480424b85adc
   // orocos_kdl/src/chainiksolvervel_wdls.cpp:177-194
   if ( sigmaMin < eps ) {
       lambda_scaled = sqrt(1.0-(sigmaMin/eps)*(sigmaMin/eps))*lambda ;
   }
   if(fabs(S(i))<eps) {
       if (i<6) {
           tmp(i) = sum*((S(i)/(S(i)*S(i)+lambda_scaled*lambda_scaled)));
       } ...
   } else {
       tmp(i) = sum/S(i);
   }
   ```
   When only $S(5)$ is small ($S(4) \gg \varepsilon$), `tmp(5)` is continuous at $S(5) = \varepsilon$ (since $\lambda_{\text{scaled}}(\varepsilon) = 0$), though its slope $\frac{d}{d\sigma_5}\lambda_{\text{scaled}}^2 = -2\lambda^2 \sigma_5 / \varepsilon^2$ creates a **acceleration discontinuity** ($\ddot{q}$ step) at the $\varepsilon$-sphere boundary, exciting structural drive resonances. Worse, when a robot nears **two** simultaneous kinematic degeneracies (e.g., wrist alignment $S(5) = 0.001$ while elbow extension brings $S(4)$ across $\varepsilon = 0.05$ with $\lambda = 0.2$), `lambda_scaled` is already `0.19996` (dictated by `sigmaMin = S(5)`!). As $S(4)$ decreases by $2 \times 10^{-7}$ across `0.05`, execution verified (`pkg1_probe.py`) that mode-`4` gain drops instantaneously from **`19.999960` to `1.176912 rad/s` per `m/s`** (a **`16.994x` velocity step** in `1` servo tick!).
2. **Un-Damped Finite-Difference Probe in `MoveIt Servo` (`moveit_ros/moveit_servo/src/utils/common.cpp:303-328`):**
   ```cpp
   // moveit/moveit2 @ 900e0e42a80d4d096e60864316a16640b0fe9372
   const Eigen::MatrixXd matrix_s = current_svd.singularValues().asDiagonal();
   const Eigen::MatrixXd pseudo_inverse = current_svd.matrixV() * matrix_s.inverse() * current_svd.matrixU().transpose();
   // ...
   next_joint_angles += pseudo_inverse * delta_x;
   robot_state->setJointGroupPositions(joint_model_group, next_joint_angles);
   ```
   To resolve the SVD sign ambiguity of $u_m$, `velocityScalingFactorForSingularity` steps `robot_state` along `pseudo_inverse * (u_m * singularity_step_scale)` without restoring `robot_state`'s original joint positions afterward and without damping `matrix_s.inverse()`. Near $\sigma_m = 10^{-5}$ with `singularity_step_scale = 0.01`, `pseudo_inverse * delta_x` steps `1,000 rad`—jumping completely past the singularity so `next_condition_number < current_condition_number` and inverting the sign of `vector_towards_singularity`. At exact $\sigma_m = 0$, `matrix_s.inverse()` produces `+Inf` and `0 * Inf = NaN`, writing `NaN` directly into `robot_state` (cf. the downstream workaround comment at `common.cpp:527`: `// TODO: fix the root cause so this isn't necessary (#2958)`).

**$C^2$-Smooth Per-Mode Damping + `IEC 61800-5-2` `SLS` Scaling:** Defining per-mode damping $\lambda_i^2(\sigma_i) = \lambda_{\max}^2 \max(0, 1 - (\sigma_i / \varepsilon)^2)^3$ makes each mode filter $g(\sigma_i) = \sigma_i / (\sigma_i^2 + \lambda_i^2(\sigma_i))$ **$C^2$-continuous everywhere** on $[0, \infty)$ ($g(0) = 0$, $g(\varepsilon) = 1/\varepsilon$, $g'(\varepsilon^-) = g'(\varepsilon^+) = -1/\varepsilon^2$, $g''(\varepsilon^-) = g''(\varepsilon^+) = 2/\varepsilon^3$), completely decoupling mode $i$ from mode $5$ and eliminating codimension-2 jumps. Composing this with direction-preserving velocity scaling $\alpha = \min(1, \min_j \dot{q}_{j,\text{SLS}} / |\dot{q}_j|)$ (`common.cpp:380-409`, `jointLimitVelocityScalingFactor`) enforces `IEC 61800-5-2` Safely-Limited Speed (`SLS`) without altering the Cartesian twist direction.

---

### 3. EtherCAT Distributed Clocks (`DC`), `SYNC0` Phase Alignment, and `WKC` Frame Interlocks (`SOEM`)

`Basis: normative + source + execution`

Under `IEC 61158` Type 12 (`ETG.1000.4` / `ETG.1020`), EtherCAT achieves sub-microsecond multi-axis synchronization by electing the first `DC`-capable slave (`context->slavelist[0].DCnext`, `src/ec_dc.c:280`) as the **System Time Reference Clock** and disciplining both downstream slave ESCs (in hardware) and the real-time master thread (in software) to its `64`-bit nanosecond counter (`ECT_REG_DCSYSTIME`, `0x0910`, epoch `2000-01-01T00:00:00Z`, `src/ec_dc.c:270`).

```
Master RT Thread (PREEMPT_RT)               Reference Slave ESC (DCnext)           Axis Slaves 2..N (ESC + Servo Drive)
      |                                                  |                                        |
      |--- [Datagram 1: LRW (PDO Out/In)] -------------->|--- (on-the-fly read/write, WKC+=3) --->|
      |--- [Datagram 2: FRMW (0x0910 DCSYSTIME)] ------->| (reads 64-bit ref clock -> wire) ----->| (writes 0x0910; HW PLL tracks ref!)
      |<-- [Returning Ethernet Frame: WKC, DCtime] ------|<---------------------------------------|
      |                                                  |                                        |
      | Check: wkc == expectedWKC (2*N_rw + N_r + N_w)?  |                                        |
      | Update: ec_sync(DCtime, cycletime, &toff)        |          At t == k * CyclTime0 + Shift:|
      | Sleep until next (cycletime + toff)              |          [HW SYNC0 IRQ]                |          [HW SYNC0 IRQ]
                                                                    Latches PDO -> Torque Loop               Latches PDO -> Torque Loop
```

Inspection of `OpenEtherCATsociety/SOEM` (`49fc34923b973c17700592319159af22157350c9`) establishes four concrete protocol and implementation invariants:

1. **Symmetric Topology Delay Assumption (`src/ec_dc.c:268-406`):** `ecx_configdc` broadcasts a dummy write to `ECT_REG_DCTIME0` (`0x0900`, `line 268`) to latch `32`-bit port receive timestamps (`DCrtA..DCrtD`) on every slave's `4` MII/EBUS ports, traverses the parent-child port tree (`0 -> 3 -> 1 -> 2` physical ring order, `lines 218, 374`), and writes `pdelay = ((dt3 - dt1) / 2) + dt2 + parent.pdelay` (`lines 401-405`) into `ECT_REG_DCSYSDELAY` (`0x0928`). Line `400` explicitly assumes symmetric forward/return PHY+cable delay; asymmetric PHYs introduce a static `SYNC0` inter-axis skew equal to $(\tau_{\text{fwd}} - \tau_{\text{ret}})/2$ (typically `5–40 ns` per hop).
2. **`FRMW` Reference Clock Distribution and `SYNC0` Phase Margin (`src/ec_dc.c:59-73`, `src/ec_main.c:2663-2671`):** When `grouplist[group].hasdc` is true, `ecx_send_processdata_group` appends an `EC_CMD_FRMW` (Configured-Address Physical Read Multiple Write) datagram targeting `slavelist[DCnext].configadr` at `ECT_REG_DCSYSTIME` (`sizeof(int64)`). Every cyclic frame thus reads the reference slave's `64`-bit clock into `context->DCtime` while simultaneously broadcasting it to all downstream slaves' hardware PLLs. For every axis to latch coherent kinematics from the **same** kinematic tick $k$, the `LRW` frame must complete traversal and DMA unpack **strictly before** `SYNC0` fires, requiring a phase margin (`syncoffset`, e.g., `250–500 us` on a `1 ms` cycle) exceeding worst-case master wake jitter + trajectory/IK WCET + wire transmission time.
3. **Signed Remainder Asymmetry and Unclamped PI Windup in `ec_sync` (`samples/ec_sample/ec_sample.c:46-58, 79`):** Executing SOEM's verbatim `ec_sync` compiled under `/usr/bin/gcc -O2` (`ec_sync_probe.c`) confirms two software PLL hazards:
   - When `(reftime - syncoffset) < 0` (e.g., `-700,000 ns` on a `1,000,000 ns` cycle, whose shortest wrapped phase error is `+300,000 ns`), C99 `%` truncation yields `delta = -700,000`. Because `ec_sync` checks only `if (delta > cycletime / 2)` (`line 51`) without `if (delta < -cycletime / 2) delta += cycletime`, it computes `timeerror = +700,000 ns` and `toff = +7,014 ns`—driving the master clock in the **wrong direction** (vs. `-3,006 ns` for symmetric Euclidean wrap) until wrap-over!
   - `static int64 integral = 0;` (`line 48`) has neither anti-windup saturation nor output slew clamping on `add_time_ns(&ts, cycletime + toff)` (`line 79`). During prolonged scheduling stalls or slave recovery, `integral` accumulates unboundedly, causing post-recovery cycle compression (`cycletime + toff < WCET`) that pushes `LRW` arrival across the `SYNC0` latch edge (**cyclic-PDO tearing**, where Joints `1..3` latch sample $k$ and Joints `4..6` latch sample $k-1$!).
4. **Non-Atomic `IOmap` Copy and Delayed `WKC` Fault Reaction (`src/ec_main.c:2723-2765`, `ec_sample.c:85-98, 109-181`):** Under `ETG.1000.4`, an `LRW` datagram increments `WKC` by `+1` per slave read (`inputsWKC`), `+2` per slave write, or `+3` for combined read+write (`expectedWKC = 2 * group->outputsWKC + group->inputsWKC`, `ec_sample.c:197`). However:
   - `ecx_receive_processdata_group` (`src/ec_main.c:2729, 2738`) executes `memcpy(idxstack->data[pos], &(rxbuf[idx][EC_HEADERSIZE]), idxstack->length[pos])` whenever `wkc2 > EC_NOFRAME` (`>= 1`), overwriting `IOmap` inputs **before** the caller can verify `wkc == expectedWKC`.
   - In `ec_sample.c:86-97`, a partial response (`0 < wkc < expectedWKC`, e.g., drive `5` dropped out of `OP`) merely increments `dowkccheck++` while **still executing `ec_sync` (`wkc > 0`) and `ecx_send_processdata(&ctx)`**! The background `ecatcheck` thread (`line 109`, sleeping `10,000 us` at `line 180`) acts only after `dowkccheck > 2`—allowing **3 to 40+ corrupted `250 us`–`1 ms` servo cycles** of uncoordinated multi-axis motion instead of immediately zeroing torque commands / asserting `IEC 61800-5-2` Safe Torque Off (`STO`, CiA 402 controlword `0x6040` quick-stop / hardware `STO` drop) on the first `wkc != expectedWKC` or `|timeerror| > max_sync_jitter` violation.

---

### 4. Holistic Six-Level Performance and Resource Footprint (`L1–L6`)

`Basis: source + execution + documentation + derived`

Table 1 quantifies engineering cost, compile/build overhead, real-time execution WCET, certificate checking speed, and memory/power footprints across `L1–L6` for each subsystem and its verified counterpart.

| Level | Metric / Dimension | Analytical `Ruckig` + `KDL WDLS` + Raw `SOEM` | Hardened Dimensionless Sturm/Rolle OTG + $C^2$ DLS + Fenced `SOEM DC` | Primary Evidence / Measurement Basis |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring & Maintenance Velocity** | Core algorithm & safety-wrapper LoC; LLM/human iteration cost | `Ruckig` Step 1/2: `~2,500 LoC` dense CAS-generated C++ (`position_third_step{1,2}.cpp`); `KDL WDLS`: `224 LoC`; `SOEM DC`: `428 LoC`. Modifying CAS quartic branches manually is error-prone (`> 10` turns / person-weeks per corner bug). | `+95 LoC` dimensionless Rolle/Sturm root isolator (`roots.hpp`), `+35 LoC` per-mode $C^2$ DLS + `SLS` clamp, `+55 LoC` double-buffered `WKC`/`DC` PI interlock (`~185 LoC` total delta; `2.5–4x` proof/test-to-code ratio). | `wc -l` on pinned `pantor/ruckig`, `orocos_kdl`, and `SOEM` sources (`Basis: source`). |
| **`L2` Toolchain & Framework Build Time** | Clean & incremental build wall-clock and peak build RAM | `pantor/ruckig` CMake C++17: `~6–11 s` clean (`~0.8 s` incremental), `~350 MiB` RSS; `SOEM` CMake C99: `~1.5–3 s` clean (`< 150 MiB` RSS); `MoveIt 2` full workspace (`colcon`): `4–12 min` clean, `8–16 GiB` peak `g++`/Eigen template RSS (`-j8`). | Standalone trajectory + IK + SOEM C/C++ RT kernel builds in `3.2–8.5 s` clean (`< 0.6 s` incremental, `< 450 MiB` RSS) when decoupled from ROS 2 message-generation graph. | Repository `CMakeLists.txt` dependency fan-out & Eigen header instantiation (`Basis: source + documentation`). |
| **`L3` Compilation, Elaboration & Synthesis Latency** | Solver / SMT / polynomial certificate synthesis & IDE feedback | `clangd` LSP on `ruckig`/`kdl`: `18–45 ms` warm re-index. Offline CAS derivation of `Step 1/2` algebraic expressions takes seconds in SymPy/Mathematica; `PSY-TaLiRo` `1,000`-rollout falsification run: `8–45 s`. | Interval/Bernstein positivity & `SLS` bound verification per profile: `4–18 ms` in SMT (`QF_NRA` / dReal / Z3) at compile/test time; `< 30 ms` warm LSP feedback. | Upstream solver complexity & `psy-taliro` optimizer loop (`Basis: source + derived`). |
| **`L4` Generated Code Execution Performance** | Throughput, `p99.9` latency, WCET, SIMD, FFI/NIC cycles | `Ruckig` `7-DoF` Step 1+2 (`x86_64` single core): `0.8–3.5 us` mean, `~6–12 us` worst-case; `KDL` `6x7` Householder SVD (`svd_eigen_HH`): `1.4–2.8 us`; `MoveIt` `6x6` `JJ^T` eigensolver: `~0.6–1.1 us`; `SOEM` raw socket `LRW+FRMW` TX/RX (`PREEMPT_RT`): `18–45 us` (`100BASE-TX` `6`-axis wire time `~12 us` + NIC DMA/syscall). | Dimensionless Rolle + `shrink_interval` adds `+0.3–0.9 us` per active quartic (`7-DoF` OTG + $C^2$ SVD IK + fenced `WKC` check total compute WCET `< 9.5 us`, leaving `> 230 us` margin inside a `250 us` `4 kHz` `SYNC0` cycle; `0` heap allocations). | Berscheid & Kröger RSS 2021 benchmarks + probe timing (`Basis: documentation + execution`). |
| **`L5` Runtime Monitor / Certificate Check Speed** | Online kinematic envelope & bus-frame admission latency | `Ruckig` `Profile::check` (`include/ruckig/profile.hpp`): `~35–80 ns`/profile (`7` segment integrations + bound checks); `SOEM` raw `wkc` integer compare: `< 2 ns`. | Outward-rounded `FP64` `1`-ULP Bernstein / endpoint extremum verifier + `WKC == expectedWKC` + `|DC_err| <= jitter_max` online shield executes in **`90–210 ns` (`< 0.0003 ms`)** per `4 kHz` tick (`100%` data-parallel across axes). | Exact operation count of `7`-segment cubic evaluation (`~65 FLOPs/DoF`, `Basis: derived`). |
| **`L6` RAM, Disk & Binary Footprints** | Static SRAM/BSS, `.text` binary size, heap, and power | `libruckig.so`: `~280–420 KiB` `.text` (`PositionThirdOrderStep{1,2}` stack frame `~2.4 KiB`, `0` dynamic allocation in `Ruckig<DOFs>`); `liborocos-kdl`: `~550 KiB` (pre-allocated `Eigen::MatrixXd` heap buffers at solver init); `libsoem`: `~65 KiB` `.text` + `4 KiB` `IOmap` (`ec_sample.c:18`). | Zero-malloc static footprint: `<= 16 KiB` total `.bss`/stack per `7-DoF` RT servo thread (`IOmap` double-buffer `2 x 4 KiB` + `BrakeProfile` fallback state `448 B`), `< 1.2 W` single-core RT CPU package draw at `1 kHz`. | Struct layout & `IOmap[4096]` sizing in `ruckig` / `SOEM` (`Basis: source`). |

---

### 5. Human Comprehensibility and Conceptual Simplicity / Model Refinement (`C1–C2`)

`Basis: source + derived`

#### 5.1 (`C1`) Human Comprehensibility vs. Agent Execution Ergonomics

1. **Opaque CAS Radicals vs. Auditable Monotone Brackets (`Ruckig`):** `src/ruckig/position_third_step1.cpp` (`566` lines) and `position_third_step2.cpp` (`1,140` lines) consist of mechanically expanded degree-4/6 polynomial coefficients (`3*(a0_p4*aMin - af_p4*aMax) + 8*aMax*aMin*(...)`, `line 30`) paired with ad-hoc `DBL_EPSILON` branches in `roots.hpp`. An LLM or symbolic script can transcribe such formulas rapidly, yet **neither a human reviewer nor a static analyzer can visually audit sign-cancellation stability** across `11` coupled scalar parameters `(p0, v0, a0, pf, vf, af, vMax, vMin, aMax, aMin, jMax)`. By contrast, a trajectory segment representation factored into (a) an explicit `7`-tuple $(t_k, j_k)_{k=0}^6$ checked by forward rational/interval integration (`Profile::check` as the sole soundness gate!) and (b) a dimensionless monotone root isolator (`shrink_interval`) reduces the human mental model to **3 local concepts**: boundary residuals $(e_p, e_v, e_a)$, per-segment extremum bounds, and guaranteed fallback to `BrakeProfile`.
2. **Nonlocal State-Mutation Footgun in `MoveIt Servo` (`common.cpp:327`):** `velocityScalingFactorForSingularity` takes `const moveit::core::RobotStatePtr&`—a C++ signature that promises `const` pointer binding while **mutating the pointee `RobotState` via `setJointGroupPositions` (`line 327`) without restoring it**! A human engineer reading `servo.cpp` assumes computing a scalar velocity scaling factor is pure; instead, callers downstream observe perturbed or `NaN`-corrupted forward kinematics. Separating pure SVD spectrum analysis (`&Jacobian -> SingularSpectrum`) from state mutation eliminates this hidden nonlocal coupling.
3. **Diagnostic Legibility on Bus Dropouts (`SOEM`):** When `wkc != expectedWKC` in `SOEM`, a single scalar deficit (`wkc = 11` vs. `expectedWKC = 14`) does not tell an operator *which* drive dropped out until `ecx_readstate` polls AL status codes `0x0134` asynchronously (`ec_sample.c:241-246`). Partitioning diagnostic telemetry (per-slave `ALstatuscode` + `DC` `SystemTimeDiff` register `0x092C`) from the `O(1)` synchronous `STO` trip condition gives operators immediate root-cause attribution without delaying safe torque removal.

#### 5.2 (`C2`) Conceptual Simplicity, Orthogonality, and Universal Model Refinement

Applying Felleisen's macro-expressibility criterion and Ousterhout's deep-module principle exposes three accidental complexities across the upstream stack and collapses them into orthogonal invariants without shifting burden into glue adapters:

1. **Eliminating Scale-Dependent Epsilon Branches via Dimensionless Time Normalization:** `roots.hpp` contains `14` distinct `DBL_EPSILON` / `16 * DBL_EPSILON` branches attempting to patch low-amplitude cubic/quartic degeneracies, yet still fails on `20.23%` of multiscale quartics because time scale is unnormalized. Mapping physical time $t \in [0, T_{\text{scale}}]$ to dimensionless $u = t / T_{\text{scale}} \in [0, 1]$ with Rolle derivative bracketing collapses `solve_cubic`, `solve_resolvent`, `solve_quart_monic`, and ad-hoc `1..3`-step post-hoc Newton patches (`position_third_step1.cpp:184-267`) into **one universal monotone bracketed solver** over $[0, 1]$. The boundary solver becomes an untrusted oracle; a `40-LoC` outward-rounded `Profile::check` acts as the sole soundness verifier.
2. **Unifying `WDLS` Singularity Damping, `MoveIt` Condition Scaling, and Underactuated Chains (`nj < 6`):** Upstream splits singularity handling across `KDL` (`sigmaMin = S(5)` global scaling with `nj < 6` special case + per-mode `< eps` if-branch) and `MoveIt Servo` (condition-number hysteresis + finite-difference `pseudo_inverse` probe). Both are ad-hoc approximations of **one** universal spectral law: independent $C^2$ spectral filtering $g_\varepsilon(\sigma_i) = \sigma_i / (\sigma_i^2 + \lambda_{\max}^2 (1 - (\sigma_i/\varepsilon)^2)_+^3)$ applied identically to every singular value $i \in \{1, \dots, \min(m, n)\}$, followed by directional `L_inf` joint-velocity clamping $\alpha = \min(1, \min_j \dot{q}_{j,\max} / |\dot{q}_j|)$. Special cases for `nj < 6`, codimension-2 crossings, and finite-difference `RobotState` probing disappear completely—zero adapters, zero hysteresis state, and continuous derivatives through $\sigma_i = 0$.
3. **Transactional Shadow-Buffer `LRW` Semantics (`SOEM`):** `ecx_receive_processdata_group` conflates transport reception with state commitment by copying `rxbuf` directly into live `IOmap` before checking `WKC`. Treating cyclic `PDO` exchange as an atomic compare-and-commit step—commit shadow `rxbuf` to `IOmap` and emit torque outputs if and only if `wkc == expectedWKC && |dc_phase_err| <= delta_max`, else hold/ramp-to-`STO`—eliminates torn multi-axis sensor snapshots in `12` lines of C without changing wire framing.

---

### 6. End-to-End Solution and Implementation Validation (`V1–V4`)

`Basis: source + execution + documentation + derived`

Even when polynomial bounds, $C^2$ SVD damping, and `WKC` gating are formally proved over real-number mathematics, real robotic deployments fail across unmodeled gaps unless validated across all four tiers `V1–V4`:

| Validation Tier | Unmodeled Reality Gap Targeted | Concrete End-to-End Validation Protocol & Tooling | Pass / Falsification Criterion |
| :--- | :--- | :--- | :--- |
| **`V1` Specification Adequacy, Mutation & Non-Vacuity** | Vacuous `Profile::check` guards (`eps` tolerances hiding acceleration spikes or rejecting valid braking states); spec omissions on asymmetric limits (`vMin != -vMax`). | Property-based stateful shrinking (`10^6` near-collinear/degenerate `(p0, v0, a0) -> (pf, vf, af)` tuples at `1e-12` perturbations) + **mutant-kill testing** (injecting `roots.hpp:105` `DBL_EPSILON` cutoff, removing `lambda_scaled` smoothing, dropping `t[k] >= 0` checks). | `100%` survival of non-vacuity witness trajectories across all `ReachedLimits` classes; `100%` kill rate on root-drop, sign-flip, and codimension-2 step mutants against a high-precision (`mpmath` `128`-bit) reference integrator. |
| **`V2` Lowering, `FP64`/SIMD & Verifier Differential Fuzzing** | `-ffast-math` / `FMA` contraction breaking `fl * fh <= 0` sign invariants in `shrink_interval` or `JacobiSVD` sign flips across `x86_64 AVX2` vs. `AArch64 NEON`. | Differential fuzzing (`strict IEEE-754 -ffp-contract=off` vs. `-O3 -march=native`) + **outward-rounded IEEE-754 (`FE_UPWARD`/`FE_DOWNWARD`) Bernstein-basis envelope checker** independently auditing every emitted `7`-segment polynomial on `[0, tf]`. | `0` false accepts on `10^6` adversarial boundary-corrupted segment witnesses; maximum trajectory position endpoint drift `< 1e-9 m` across `x86_64` and `AArch64`. |
| **`V3` RTOS Scheduling, Frame-Drop & Clock-Step Fault Injection** | Linux `PREEMPT_RT` SMI/cache-miss wake jitter, Ethernet CRC frame drops, partial slave brownouts (`0 < WKC < expectedWKC`), and reference-slave `64`-bit clock jumps. | `cyclictest` + deterministic raw-socket fault proxy between `SOEM` master and slave emulator injecting single/burst `LRW` drops, `WKC = expectedWKC - 1` partial frames, `-700 us` negative initial phase offsets, and `+50 us` `ECT_REG_DCSYSTIME` steps. | `0` uncommitted partial `IOmap` reads; `0` PI windup-induced `SYNC0` latch slips (`|toff| <= max_slew`); deterministic `STO` / quick-stop transition within `1` cycle (`<= 250 us`) on `WKC` deficit. |
| **`V4` Plant `STL` Falsification, `HIL` Replay & Operator Litmus** | Continuous robot structural resonance, actuator torque saturation during wrist-singularity traversal, and operator teleop disorientation near `MoveIt Servo` scaling zones. | Closed-loop `PSY-TaLiRo` (`cpslab-asu/psy-taliro`, `RTAMT` monitor `src/staliro/specifications/rtamt.py`) & `VerifAI` (`CMA-ES` / Bayesian optimization) minimizing robustness $\rho(\varphi_{\text{servo}}, y, 0)$ over adversarial `1 kHz` Cartesian twist waveforms sweeping through $q_5 = 0$, paired with `HIL` drive-loop replay and runtime `ModelPlex` tracking-residual monitors. | Strictly positive `STL` robustness $\rho_{\min} > 0$ across `10,000` adversarial trajectories for $\varphi_{\text{servo}} \equiv \square_{[0, T]}\big(\|\dot{q}\|_\infty \le \dot{q}_{\text{SLS}} \land \|\ddot{q}\|_\infty \le a_{\max} \land (\text{wkc\_err} \implies \diamond_{[0, T_{\text{cyc}}]} \text{STO})\big)$, plus operator teleop trials confirming smooth pass-through without `180 deg` wrist-whip surprise. |

## Boundaries

1. **Higher-Order Snap-Limited (`4th`-Order) and Non-Linear Torque-Limited Dynamics (`not examined`):** This report examines kinematic third-order (`jerk`-bounded) state-to-state trajectories (`pantor/ruckig`) and kinematic Jacobian velocity/pose solvers. Full rigid-body Coriolis/gravity torque-bounded time-optimal path parameterization (`TOPP-RA`) and `4th`-order snap-limited quintic/sextic root solvers—which cannot be solved in radicals at degree $\ge 5$ by Abel-Ruffini—were `not examined` in source, though the dimensionless derivative/Sturm bracket architecture generalizes directly to higher degrees.
2. **Closed-Source Pro Edition Features of `pantor/ruckig` (`not examined`):** `pantor/ruckig` (`91085469d2133089c285e2f34541255815390e2c`) delegates intermediate-waypoint trajectory optimization (`include/ruckig/calculator_cloud.hpp`, `src/ruckig/cloud_client.cpp`) to a commercial/cloud backend when waypoints $> 0$ are configured without the commercial library; only the open-source single-segment arbitrary-target OTG solver was inspected.
3. **Hardware ESC `SYNC0` PLL Jitter on Physical Asymmetric PHYs (`not examined` by hardware oscilloscope):** While `SOEM`'s `ecx_configdc` (`src/ec_dc.c:401`) propagation-delay equations and `ec_sync` (`ec_sample.c:46-58`) software PI dynamics were verified directly from source and compiled C execution, sub-`50 ns` physical Beckhoff `ET1100` / Microchip `LAN9252` hardware PLL lock transients under thermal crystal drift were `not examined` on physical oscilloscope hardware.
4. **Scope of the `10,000`-Quartic Failure Rate (`known not to apply` as a uniform random-target failure rate of `Ruckig::update`):** The `20.23%` root-error rate measured in `pkg1_probe.py` characterizes `ruckig::roots::solve_quart_monic` directly over monic quartics with four positive roots distributed log-uniformly across $[10^{-5}, 1.0]\text{ s}$. In full `Ruckig::update`, many macroscopic point-to-point moves (`pd ~ 0.1–1.0 m`) land in `ACC0_ACC1_VEL` or `ACC0_ACC1` (`position_third_step1.cpp:25-128`), which use quadratic formulas rather than `solve_quart_monic`, or have durations $t \gg 10\text{ ms}$ where $|yy| \gg \text{DBL\_EPSILON}$. Thus `20.23%` does **not** apply to macroscopic point-to-point benchmarks (`known not to apply`); it specifically manifests during short-horizon (`< 4 ms`) `NONE`/`ACC0`/`ACC1` replanning and multi-DoF Step 2 synchronization.
5. **Safety Certification Authority of Open-Source `SOEM` (`unsupported`):** Standard `SOEM` over non-redundant Ethernet without Safety-over-EtherCAT (`FSoE`, `IEC 61784-3-12` black-channel CRC + connection watchdogs) is `unsupported` as a standalone SIL-3 / PL-e safety function; software `WKC` gating must feed or complement hardware drive-resident `IEC 61800-5-2` `STO`/`SS1` circuits and slave PDI watchdog timers (`0x0400`–`0x0442`).

## Evidence

### Primary Upstream Source Coordinates

1. **`pantor/ruckig` (`91085469d2133089c285e2f34541255815390e2c`, committed `2026-11-13T10:50:58Z`):**
   - `include/ruckig/roots.hpp:60-149` (`solve_cubic`: absolute `DBL_EPSILON` deflation at `line 63` and Cardano `yy` branch cutoffs at `lines 105, 113`), `lines 154-195` (`solve_resolvent`), `lines 198-283` (`solve_quart_monic`: `DBL_EPSILON` / `16 * DBL_EPSILON` cutoffs at `lines 201, 244, 262-275`), and `lines 343-395` (`shrink_interval` safeguarded Newton-bisection).
   - `src/ruckig/brake.cpp:14-80` (`BrakeProfile::acceleration_brake`, `velocity_brake`, `get_position_brake_trajectory` pre-step envelope recovery).
   - `src/ruckig/position_third_step1.cpp:25-284` (`time_all_vel`, `time_acc0_acc1`, `time_all_none_acc0_acc1` quartic formulation and unbracketed Newton steps at `lines 189, 220, 250-264`).
   - `src/ruckig/position_third_step2.cpp:41-257` (`PositionThirdOrderStep2::time_acc0_acc1_vel`, `time_acc1_vel`, `time_acc0_vel` fixed-duration `tf` synchronization).
2. **`orocos/orocos_kinematics_dynamics` (`b7f433b94b2bc66981ce073e4d14480424b85adc`, committed `2026-11-10T12:28:33Z`):**
   - `orocos_kdl/src/chainiksolvervel_wdls.cpp:116-216` (`ChainIkSolverVel_wdls::CartToJnt`: `jac.columns() >= 6` guard at `line 158`, `lambda_scaled = sqrt(1.0 - (sigmaMin/eps)^2) * lambda` at `line 179`, per-mode `fabs(S(i)) < eps` switch at `lines 181-194`).
   - `orocos_kdl/src/chainiksolverpos_lma.cpp:187-315` (`ChainIkSolverPos_LMA::CartToJnt` Nielsen trust-region damping update).
3. **`moveit/moveit2` (`900e0e42a80d4d096e60864316a16640b0fe9372`, version `2.15.3`, committed `2026-11-18T19:46:49Z`):**
   - `moveit_ros/moveit_servo/src/utils/common.cpp:282-451` (`velocityScalingFactorForSingularity`: un-damped `matrix_s.inverse()` at `line 306`, in-place `robot_state->setJointGroupPositions` mutation at `line 327`, hysteresis jump at `lines 348-368`; `jointLimitVelocityScalingFactor` at `lines 380-409`).
   - `moveit_kinematics/kdl_kinematics_plugin/src/pseudoinverse.hpp:18-34` (`solvePseudoinverse` normal-matrix `JJ^T` eigensolver cutoff) and `kdl_kinematics_plugin.cpp:303-415`.
4. **`OpenEtherCATsociety/SOEM` (`49fc34923b973c17700592319159af22157350c9`, committed `2026-10-14T09:16:06Z`):**
   - `src/ec_dc.c:33-143` (`ecx_dcsync0`, `ecx_dcsync01` `ECT_REG_DCSTART0` / `ECT_REG_DCCYCLE0` setup) and `lines 250-428` (`ecx_configdc` `2000-01-01` epoch offset `946684800UL`, port timestamp latching, symmetric `((dt3 - dt1) / 2) + dt2` delay propagation).
   - `src/ec_main.c:2514-2775` (`ecx_send_processdata_group` piggybacking `EC_CMD_FRMW` on `ECT_REG_DCSYSTIME` at `line 2669`; `ecx_receive_processdata_group` copying `rxbuf` into `IOmap` prior to full `expectedWKC` verification at `lines 2729, 2738`).
   - `samples/ec_sample/ec_sample.c:46-182` (`ec_sync` signed modulo and unclamped `integral` PI loop; `ecatthread` sending PDOs during `wkc != expectedWKC` until `ecatcheck` sees `dowkccheck > 2`).
5. **Falsification Toolkits & Primary Literature:**
   - `cpslab-asu/psy-taliro` (`887f2dc321e83688796307f8b0abcf22b3a57b4c`, `src/staliro/cost_func.py`, `src/staliro/specifications/rtamt.py`); Thibeault, Anderson, Chandratre, Pedrielli & Fainekos, *"PSY-TaLiRo: A Python Toolbox for Search-Based Test Generation for Cyber-Physical Systems,"* FMICS 2021 (`arXiv:2106.02200`).
   - `BerkeleyLearnVerify/VerifAI` (`7ef383f191cac0cb2d0174829ac2ec75ab7a0f3c`).
   - Berscheid & Kröger, *"Jerk-limited Real-time Trajectory Generation with Arbitrary Target States,"* Robotics: Science and Systems (RSS), 2021 (`DOI: 10.15607/RSS.2021.XVII.015`, `arXiv:2105.04830v2`).
   - Wampler, *"Manipulator Inverse Kinematic Solutions Based on Vector Formulations and Damped Least-Squares Methods,"* `IEEE Trans. Syst. Man Cybern.`, `SMC-16(1):93–101`, 1986; Nakamura & Hanafusa, *"Inverse Kinematic Solutions With Singularity Robustness for Robot Manipulator Control,"* `ASME J. Dyn. Syst. Meas. Control`, `108(3):163–171`, 1986; Chiaverini, Siciliano & Egeland, *"Review of the Damped Least-Squares Inverse Kinematics with Experiments on an Industrial Robot Manipulator,"* `IEEE Trans. Control Syst. Technol.`, `2(2):123–134`, 1994.

### Reproducible Execution Probes (Acquired `2026-11-19`)

1. **`SOEM` `ec_sync` Verbatim C Probe (`/usr/bin/gcc -O2`):**
   - Command: compile `ec_sync` from `samples/ec_sample/ec_sample.c:39-58` and evaluate `ec_sync(-200000, 1000000, &toff)` (`syncoffset = 500000`).
   - Observed output: `Case1 (reftime=-200000, diff=-700000 ns): upstream timeerror=700000 ns, toff=7014 ns | bounded toff=-3006 ns`.
2. **`Ruckig` `roots.hpp` & `KDL` `WDLS` IEEE-754 `binary64` Probe (`python3`):**
   - Command: execute line-for-line `binary64` port of `roots.hpp:60-283` and `chainiksolvervel_wdls.cpp:177-194` against dimensionless Rolle + `shrink_interval` (`seed = 20261119`, `10,000` random positive-root quartics on $[10^{-5}, 1.0]\text{ s}$).
   - Observed output:
     - `Cubic (0.001, 0.002, 0.003): ruckig_solve_cubic -> [0.0019999900658925376, 0.0020000198682149253]`
     - `Cubic (3e-6, 6e-6, 9e-6) [|d|=1.620e-16 < DBL_EPSILON]: ruckig_solve_cubic -> [0.0]`
     - `Quartic 10k sweep (t in [1e-5, 1.0]s): 2023/10000 (>1% min-root error or missed)` vs. `Dimensionless Rolle-bracket + shrink_interval 10k sweep: fails=0/10000, max_min_root_rel_err=4.213e-10`
     - `KDL WDLS mode-4 gain at S(5)=0.001, S(4)=0.0500001: 19.999960` vs. `S(4)=0.0499999: 1.176912 rad/s per m/s`.

## Revalidation

To revalidate whether a newer upstream revision of `pantor/ruckig`, `orocos/orocos_kinematics_dynamics`, `moveit/moveit2`, or `OpenEtherCATsociety/SOEM` alters these findings without repeating full corpus research:

1. **Diff Targeted Source Regions (`< 15 s`):**
   - In `pantor/ruckig`, inspect `include/ruckig/roots.hpp` (`solve_cubic`, `solve_quart_monic`) for absolute `DBL_EPSILON` comparisons against unnormalized `d`, `yy`, and `D`.
   - In `orocos/orocos_kinematics_dynamics`, inspect `orocos_kdl/src/chainiksolvervel_wdls.cpp` around `CartToJnt` to check whether `lambda_scaled` is still computed from a single global `sigmaMin = S(5)` while applied conditionally via `fabs(S(i)) < eps`.
   - In `moveit/moveit2`, inspect `moveit_ros/moveit_servo/src/utils/common.cpp` (`velocityScalingFactorForSingularity`) for `matrix_s.inverse()` and un-restored `robot_state->setJointGroupPositions`.
   - In `OpenEtherCATsociety/SOEM`, inspect `src/ec_main.c` (`ecx_receive_processdata_group`) and `samples/ec_sample/ec_sample.c` (`ec_sync`, `ecatthread`) for negative `%` modulo handling, integrator anti-windup, and `wkc == expectedWKC` gating prior to `IOmap` commit and `ecx_send_processdata`.
2. **Run Minimal Discriminating Execution Check (`< 2 s`, standard library Python 3):**
   ```bash
   python3 -c '
   import math, sys
   eps = sys.float_info.epsilon
   # Check Ruckig solve_cubic yy cutoff on (t-0.001)(t-0.002)(t-0.003)
   b, c, d = -0.006, 1.1e-5, -6e-9
   p = c - b*b/3.0
   halfq = (2*b**3 - 9*b*c + 27*d)/54.0
   yy = p**3/27.0 + halfq**2
   assert abs(yy) < eps, f"expected |yy| < DBL_EPSILON, got {yy}"
   # Check KDL WDLS codimension-2 step ratio at S(5)=0.001, eps=0.05, lambda=0.2
   ls = math.sqrt(1.0 - (0.001/0.05)**2) * 0.2
   g_above = 1.0 / 0.0500001
   g_below = 0.0499999 / (0.0499999**2 + ls**2)
   assert g_above / g_below > 16.9, f"ratio={g_above/g_below}"
   print("Revalidation discriminator confirmed:", yy, round(g_above / g_below, 3))
   '
   ```
   A pass on this probe confirms the algebraic invariants driving the upstream branches; re-run against compiled upstream binaries if upstream replaces `solve_cubic`, `CartToJnt`, or `ec_sync`.
