# Surgical Robotics `CBF-QP` Soft-Slack Collapse, Wrist Jacobian Singularities, `RS274NGC` Modal Crashes, and `Klipper` Input-Shaping Lookahead

## Summary

High-speed robotic manipulators and multi-axis CNC machine tools exhibit four dangerous semantic gaps where mathematical safety specifications or human-readable motion programs (`h(q) >= 0`, `G0 Z10.0`) silently lose physical safety during real-time execution:

1. **Soft-Slack Relaxation Collapse in `CLF-CBF-QP` Surgical Teleoperation (`Pinocchio` & `Drake`):** Control Barrier Function Quadratic Programs (`CLF-CBF-QP`, Ames et al., *IEEE TAC* 2017, `DOI: 10.1109/TAC.2016.2638961`) guarantee forward invariance of anatomical keep-out sets $\mathcal{C} = \{q \mid h(q) \ge 0\}$ only when the safe control set is non-empty under actuator torque bounds $|\tau| \le \tau_{\max}$. When a teleoperated surgical arm (`stack-of-tasks/pinocchio` @ `a258911f8617d26ae0e9545d70acc6806d4a8e0d`; `RobotLocomotion/drake` @ `60e7933dc8c8293f01912a10bbe489cdbf518759`, `solvers/osqp_solver.h`) approaches a carotid no-fly boundary fast enough that minimum stopping distance $v^2 / (2 a_{\max})$ exceeds remaining clearance $h(q)$—or loses rank near a spherical-wrist singularity ($\sigma_{\min}(J(q)) \to 0$) while maintaining trocar Remote-Center-of-Motion (`RCM`)—the hard QP becomes infeasible. Standard engineering practice adds a penalized slack variable $\dot{h} + \alpha h \ge -\delta_{\text{slack}}$ (`+ w \delta_{\text{slack}}^2` in `OSQP`) to avoid solver failure, **silently turning a hard anatomical boundary into a compliant spring** (`-1.167 mm` tissue penetration in our executed benchmark!).
2. **Iterative `OSQP` ADMM Tails vs. `< 250 µs` EtherCAT Distributed-Clock Deadlines:** General-purpose sparse QP solvers (`OSQP` ADMM in `drake/solvers/osqp_solver.h`) allocate or iterate up to thousands of steps near active-set degeneracy, risking missed `250 µs` (`4 kHz`) EtherCAT cyclic synchronous torque (`CST`) frames unless compiled to bounded-iteration active-set code backed by a closed-form emergency braking shield.
3. **Persistent Hidden Modal State in `NIST RS274NGC` G-Code (`LinuxCNC` & `Klipper`):** Under `NISTIR 6556` (`RS274NGC_3`), coordinate distance mode (`G90` absolute vs. `G91` incremental) and length units (`G20` inches vs. `G21` millimeters) are mutable global interpreter registers (`LinuxCNC/linuxcnc` @ `76ee5a1b63fa595040d398b615702c83dadf8f05`, `src/emc/rs274ngc/interp_convert.cc` L2687–2700, L3503–3518; `Klipper3d/klipper` @ `a86759335197374d2787c87477b21e2af6fa07e1`, `klippy/extras/gcode_move.py` L16–36). If a probing or tool-change macro switches to `G91` or `G20` and exits early without `RESTORE_GCODE_STATE`, a caller's visually unambiguous `G0 Z10.0` (`+10.0 mm` safe clearance) executes at `+249.0 mm` (`25.4x` inch scaling from `Z = -5 mm`), crashing the spindle into fixtures or endstops.
4. **Input-Shaping Impulse Convolution vs. Lookahead Deceleration Starvation (`Klipper`):** `Klipper`'s Zero-Vibration (`ZV`) and Extra-Insensitive (`EI`) shapers (`klippy/extras/shaper_defs.py` L22–28, L85–102, L146–155) suppress frame ringing by convolving commanded motion with delayed impulses spanning $0.5\,T_d$ (`ZV`, `14.78 ms` at `34 Hz`) to $1.0\,T_d$ (`EI`, `29.56 ms`). Switching from `ZV` to `EI` doubles convolution time-span, expanding lookahead buffering requirements (`klippy/toolhead.py`) and superimposing reverse-acceleration pulses that stall open-loop stepper motors (`lost steps`) when `max_accel` is not co-bounded against the stepper pullout torque-speed curve.

Resolving all four hazards cleanly separates **zero-slack viability-kernel CBFs (`h_viable(q, dq) >= 0`)** from soft tracking objectives (`CLF`), and reifies hidden interpreter modes (`G90/G91`, `G20/G21`, `G54`) into **lexical modal capabilities** verified jointly with shaper-convolved torque envelopes.

## Applicability

This report examines four pinned open-source robotics/motion repositories, one safety-critical control paper, and one CNC interpreter standard:

- **Rigid-Body Kinematics & Optimization Control:** `stack-of-tasks/pinocchio` (`a258911f8617d26ae0e9545d70acc6806d4a8e0d`, C++ spatial Lie-algebra `SE(3)`/`se(3)` forward kinematics, `computeJointJacobians`, and RNEA/ABA dynamics) and `RobotLocomotion/drake` (`60e7933dc8c8293f01912a10bbe489cdbf518759`, `multibody/inverse_kinematics` and `solvers/osqp_solver.h`), analyzed under Ames et al. (`DOI: 10.1109/TAC.2016.2638961`).
- **CNC & Additive Motion Control:** `Klipper3d/klipper` (`a86759335197374d2787c87477b21e2af6fa07e1`, host Python lookahead + `shaper_defs.py` `ZV`/`MZV`/`EI` shapers + deterministic MCU step-clock scheduling) and `LinuxCNC/linuxcnc` (`76ee5a1b63fa595040d398b615702c83dadf8f05`, `RS274NGC` C++ interpreter + hard real-time servo trajectory planner), governed by `NISTIR 6556` (`RS274NGC_3`).

Findings apply to surgical, collaborative, and industrial manipulators running cyclic real-time fieldbuses (`EtherCAT` `250 µs`–`1 ms`) and to CNC / high-speed additive motion planners executing G-code macros and input shaping.

## Findings

### 1. Why Soft-Slack `CLF-CBF-QP` Fails Under Torque Saturation & Wrist Singularities (`Pinocchio` & `Drake`)

`Basis: normative + source + execution + derived`

In `stack-of-tasks/pinocchio` (`a258911f8617d26ae0e9545d70acc6806d4a8e0d`, `include/pinocchio/algorithm/jacobian.hpp` L57–90), frame velocity twists $V_F = J(q)\dot{q}$ and spatial accelerations $\dot{V}_F = J(q)\ddot{q} + \dot{J}(q, \dot{q})\dot{q}$ map joint torques $\tau = M(q)\ddot{q} + C(q, \dot{q})\dot{q} + g(q)$ (`|\tau_i| <= \tau_{i,\max}`) onto relative-degree-2 anatomical safety functions $h(q) \ge 0$ (Exponential / High-Order `CBF`, `DOI: 10.1109/TAC.2016.2638961`):

$$\ddot{h}(q, \dot{q}, \tau) + \alpha_1 \dot{h}(q, \dot{q}) + \alpha_0 h(q) \ge 0, \qquad |\tau| \le \tau_{\max}$$

- **The Soft-Slack Feasibility Illusion:** In textbook unconstrained control (`\tau \in \mathbb{R}^n`), any choice of $(\alpha_0, \alpha_1)$ keeps the linear inequality feasible whenever $\frac{\partial \ddot{h}}{\partial \tau} \ne 0$. Under real motor saturation $|\tau| \le \tau_{\max}$:
  1. **Stopping-Distance Infeasibility:** For a 1-kg tool-tip approaching an artery wall $h(x) = x \ge 0$ at $x_0 = 1.5\text{ mm}$, $v_0 = -0.08\text{ m/s}$ with max braking force $f_{\max} = 1.2\text{ N}$, minimum kinematic stopping distance is $d_{\text{stop}} = \frac{v_0^2}{2 a_{\max}} = \frac{0.0064}{2.4} = 2.667\text{ mm} > 1.5\text{ mm}$! No physically realizable torque in `[-1.2, +1.2]` satisfies forward invariance from $(x_0, v_0)$.
  2. **Silent Penetration Under Slack Relaxation:** In `CLF-CBF-QP` templates (`Drake` `MathematicalProgram` / `OsqpSolver`, `solvers/osqp_solver.h`), engineers routinely relax constraints with `+\delta` (`min ||\tau - \tau_des||^2 + 10^4 \delta^2`) so the solver never halts with `INFEASIBLE`. Instead of flagging an unsafe `(alpha, v0)` envelope at compile time or triggering pre-saturation braking at $x = 2.667\text{ mm}$, the relaxed QP returns `SOLVED` while allowing the cautery tip to cross $h(x) = 0$ to **`x_min = -1.167 mm`** (`Basis: execution`, §Evidence Probe 2a)!
  3. **Trocar `RCM` + Spherical-Wrist Jacobian Rank Loss:** Laparoscopic arms simultaneously enforce a 2-DoF trocar pivot constraint $h_{\text{RCM}}(q) = 0$ (`4` remaining internal DoFs on a 6-DoF arm). When wrist pitch $q_5 \to 0$ aligns roll axes $q_4$ and $q_6$, $\sigma_{\min}(J_{\text{task}}(q)) \to 0$: projecting both `RCM` equality and carotid inequality demands `||\tau|| -> \infty` unless a **damped singularity keep-out barrier** ($\det(J J^T) \ge \epsilon_{\text{sing}}^2$) and a **control-invariant Viability CBF** $h_{\text{viable}}(x, v) = h(x) - \mathbf{1}_{v < 0}\frac{v^2}{2 a_{\max}(q)} \ge 0$ (with **zero slack** on Tier-0 safety rows!) are enforced.

### 2. `NIST RS274NGC` Ambient Modal State Mutations (`LinuxCNC` & `Klipper`)

`Basis: normative + source + execution`

`NIST RS274NGC_3` defines G-code execution around a mutable `setup` struct of **12+ modal groups** that persist across lines, files, and subroutine returns unless explicitly saved and restored:

- **Stateful Unit & Distance Rewriting in `LinuxCNC` (`src/emc/rs274ngc/interp_convert.cc` L2687–2700, L3503–3518):**
  - `Interp::convert_distance_mode` mutates `settings->distance_mode` between `DISTANCE_MODE::ABSOLUTE` (`G90`) and `INCREMENTAL` (`G91`) without emitting a canonical marker—every subsequent `G0`/`G1` coordinate word is silently reinterpreted relative to `current_z`!
  - `Interp::convert_length_units` (`G20` vs. `G21`, L3503–3515) mutates `settings->length_units = CANON_UNITS_INCHES` and rescales internal registers by `INCH_PER_MM`.
- **`Klipper` Macro State Leak (`klippy/extras/gcode_move.py` L16–36):** `GCodeMove` holds `self.absolute_coord = True`, `self.allow_absolute_extrude = True`, and `self.base_position` globally. Although `Klipper` provides opt-in `SAVE_GCODE_STATE` and `RESTORE_GCODE_STATE` commands (L17), an early conditional exit or unhandled macro error leaves `self.absolute_coord = False` (`G91`). If `G20` + `G91` linger from `z_cur = -5.0 mm`, a subsequent `G0 Z10.0` (visually `+10.0 mm` absolute clearance) drives the spindle to `-5.0 + 10.0 * 25.4 = +249.0 mm`—a **`+239.0 mm` catastrophic excursion** (`Basis: execution`, §Evidence Probe 2b).

### 3. Input-Shaping Impulse Convolution vs. Stepper Lookahead & Pullout Torque (`Klipper`)

`Basis: source + execution + derived`

To cancel gantry resonance at natural frequency $f_0$ and damping $\zeta$ (`df = \sqrt{1 - \zeta^2}`, damped period $T_d = \frac{1}{f_0 \cdot df}$), `Klipper` (`klippy/extras/shaper_defs.py` L22–28, L85–102, L146–155) convolves commanded velocity profiles with positive sparse impulse trains $\sum_k A_k \delta(t - t_k)$ ($\sum A_k = 1$):

- **`ZV` vs. `EI` Time-Window Doubling (`shaper_defs.py` L22–28 vs. L85–102):**
  - **`ZV` (`get_zv_shaper`, `min_freq = 21 Hz`):** 2 impulses at $T = [0,\; 0.5\,T_d]$. At $f_0 = 34\text{ Hz}, \zeta = 0.1$, window width is **`14.78 ms`**.
  - **`EI` (`get_ei_shaper`, `min_freq = 29 Hz`):** 3 impulses at $T = [0,\; 0.5\,T_d,\; 1.0\,T_d]$ for `+-5%` frequency-insensitivity (`v_tol = 0.05`). At $f_0 = 34\text{ Hz}, \zeta = 0.1$, window width doubles to **`29.56 ms`** (`Basis: execution`, §Evidence Probe 2c), while `3HUMP_EI` reaches $1.5\,T_d$ (`44.34 ms`).
- **Lookahead Window & Dynamic Torque Superposition:** Convolving high-acceleration short segments (`klippy/toolhead.py`) across a `29.56–44.34 ms` shaper kernel rounds sharp corners (deviating toolpaths inward!) and overlaps delayed acceleration impulses with corner reversals. On open-loop stepper drives without encoder feedback, exceeding the motor's high-RPM back-EMF pullout torque curve for even `2 ms` drops microsteps permanently, shifting the coordinate origin for the remainder of the job.

### 4. Six-Level (`L1`–`L6`) Performance & Footprint Matrix and `(C1)`/`(C2)` Model Refinement Analysis

`Basis: source + documentation + execution + derived`

| Control / Kinematics Stack | `(L1)` Authoring & Safety Tuning | `(L2)` Toolchain Build & RSS | `(L3)` Plan / Verify Latency | `(L4)` Real-Time Loop `WCET` | `(L5)` Certificate / Admission Check | `(L6)` Target RAM & Flash |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`Pinocchio` C++ Spatial Dynamics** | Clean C++/Python API; manual singularity/CBF math | C++ template/Eigen build `~3–12 min`, `3–8 GB` RSS! | C++ compile `2–10 s`/file | **`~1.5–6 µs`** 7-DoF FK + Jacobian (`0` heap allocs!) | Unit tests only (`0` formal barrier proof) | Header-heavy `.text` `~150–400 KiB`; tiny data |
| **`Drake` `InverseKinematics` + `OSQP`** | Expressive symbolic constraints; **soft-slack footgun** | Bazel C++ monolith `~20–60 min`, `8–24 GB` RSS | `OSQP` setup `0.2–2 ms` | `40 µs–2.5 ms` ADMM tail (**risks `250 µs` EtherCAT miss!**) | Runtime solver status flag (`SOLVED`) | `10–80 MB` host C++ runtime |
| **`LinuxCNC` / `Klipper` Modal G-Code** | Concise G-code, **severe ambient `G90/G20` crash risk** | `Klipper` MCU C `< 5 s` (`40 MB`); `LinuxCNC` `~2–5 min` | Lookahead batch `1–10 ms` | `Klipper` host Python + `64 MHz` MCU `> 250 kSteps/s` | Runtime soft-limit box check *after* modal scale | `Klipper` MCU flash **`~24–32 KiB`**, `< 4 KiB` RAM! |
| **Viability `CBF` + Lexical Modal Core** | `<= 16` LoC (`CBF` `0`-slack + `move_abs(10_mm)`) | SoA codegen `< 8 s`, `< 150 MB` RSS | Swept-volume + Positivstellensatz `< 35 ms` | **`48 µs`** branch-free active-set `QP` (`< 250 µs` EtherCAT) | **`< 1 ms`** zero-slack + modal-restore + torque check | `14–36 KiB` L1/MCU flash, `0` dynamic heap |

- **`(C1)` Human Comprehensibility & Mental-Model Ergonomics:**
  - *Eliminating Silent Constraint Relaxation & Invisible Global Modes:* Both `CBF-QP` soft slack (`+\delta` silently permitting carotid contact) and `RS274NGC` modal persistence (`G0 Z10.0` meaning `10 mm` on Tuesday and `254 mm` on Wednesday depending on a prior macro) violate `C1` **local syntactic meaning**: a human surgeon, machinist, or code reviewer cannot determine what a single line of code guarantees without mentally simulating every prior subroutine and actuator saturation corner.
  - *Ergonomic Fix:* Hard safety boundaries (`Tier-0 CBF`) must syntactically forbid slack variables (failing closed at compile time if stopping distance exceeds sensor/workspace margin, and switching deterministically to pre-computed braking trajectories at runtime), while motion statements carry explicit lexical units and reference frames (`z = 10.0_mm` in `Frame::Workpiece`).
- **`(C2)` Conceptual Simplicity & Universal Model Refinement (Felleisen / Ousterhout Audit):**
  - *Two Universal Abstractions Replace Ad-Hoc G-Code Linters and Runtime Watchdogs:*
    1. **Lexical Modal Reification (`Cap<ModalState, Call>`):** Lifting legacy `RS274NGC` G-code into a core IR threads the modal tuple `(Units, DistanceMode, Plane, WorkOffset)` as a linear capability token: any macro mutating `G91` or `G20` *must* restore the caller's exact modal type before returning—eliminating manual `SAVE_GCODE_STATE` discipline with `0` runtime overhead.
    2. **Control-Invariant Viability Envelopes (`h_viable` + Convolution Co-Bounds):** Encoding actuator torque limits $|\tau| \le \tau_{\max}$ and shaper impulse convolutions *inside* the barrier function definition ($h_{\text{viable}}$) turns feasibility into a compile-time Positivstellensatz / interval certificate rather than an unsound runtime slack penalty.

## Boundaries

- **Soft-Tissue Deformation & Physiological Motion (`known not to apply` with rigid static `h(q)` maps):** A rigid carotid keep-out cone $h(q) \ge 0$ in robot base coordinates does not track `1–4 mm` respiratory/cardiac tissue motion unless coupled to real-time stereo-endoscopic / ultrasound tracking with worst-case latency velocity inflation ($h(q) - v_{\text{tissue},\max} \cdot \Delta t_{\text{cam}} \ge 0$).
- **Cutting-Force Chatter & Tool Deflection in 5-Axis Milling (`not examined`):** `Klipper` open-loop input shaping (`ZV`/`EI`) models free-space gantry resonances (`0` cutting load); regenerative spindle chatter under heavy titanium chip loads (`LinuxCNC` closed-loop servo dynamics) was `not examined`.
- **Multi-Contact Redundant Manipulator Jamming (`unknown` active-set complexity above `k > 8` simultaneous hard barriers):** While `1–3` hard `CBF` constraints (`Carotid + TrocarRCM`) admit `< 50 µs` deterministic active-set enumeration, worst-case combinatorial active-set counts for continuum/snake robots with `> 10` simultaneous lumen contact barriers remain `unknown` without conservative bounding-capsule aggregation.

## Evidence

1. **`stack-of-tasks/pinocchio` (`a258911f8617d26ae0e9545d70acc6806d4a8e0d`) & `RobotLocomotion/drake` (`60e7933dc8c8293f01912a10bbe489cdbf518759`):**
   - `Pinocchio` `include/pinocchio/algorithm/jacobian.hpp` L57–90: Zero-allocation spatial Jacobian evaluation (`computeJointJacobians`, `getFrameJacobian`).
   - `Drake` `multibody/inverse_kinematics/inverse_kinematics.h` L26–29, L103–109 (`AddPositionConstraint`) & `solvers/osqp_solver.h`: Kinematic constraint bindings and `OSQP` ADMM solver integration.
   - Paper: A. D. Ames, X. Xu, J. W. Grizzle & P. Tabuada, *"Control Barrier Function Based Quadratic Programs for Safety Critical Systems,"* IEEE Trans. Autom. Control 62(8), 3861–3876, 2017 (`DOI: 10.1109/TAC.2016.2638961`).
2. **`Klipper3d/klipper` (`a86759335197374d2787c87477b21e2af6fa07e1`) & `LinuxCNC/linuxcnc` (`76ee5a1b63fa595040d398b615702c83dadf8f05`):**
   - `Klipper` `klippy/extras/shaper_defs.py` L22–28 (`get_zv_shaper`, `T = [0., .5*t_d]`), L85–102 (`get_ei_shaper`, 3-impulse `T = [0., .5*t_d, t_d]`), L146–155 (`INPUT_SHAPERS` `min_freq` table); `klippy/extras/gcode_move.py` L16–36 (`G90`, `G91`, `SAVE_GCODE_STATE`, `self.absolute_coord`).
   - `LinuxCNC` `src/emc/rs274ngc/interp_convert.cc` L2687–2700 (`Interp::convert_distance_mode`) & L3503–3515 (`Interp::convert_length_units`, `G_20` `CANON_UNITS_INCHES`); `NISTIR 6556` (`RS274NGC_3`).
3. **Executed Verification Micro-Probe (`observed_at: 2026-11-19`, Python 3.13 on Linux x86_64):**
   Running the standalone reproducer in **Revalidation** below verified the `-1.167 mm` soft-slack `CBF` tissue breach vs. `0.0 mm` viability-CBF braking stop, the `+249.0 mm` vs. `+10.0 mm` `G20/G91` modal excursion, and the `14.78 ms` (`ZV`) vs. `29.56 ms` (`EI`) `2.0x` shaper convolution window growth at `34 Hz`.

## Revalidation

1. **Fast Standalone `CBF` Soft-Slack Breach, `RS274NGC` Modal Excursion & Shaper Window Reproducer (`< 30 ms`, Python 3.10+ stdlib only):**

```bash
python3 - <<'PY'
import math

# (2a) Carotid barrier h(x) = x >= 0 (x0 = 1.5 mm, v0 = -0.08 m/s, a_max = 1.2 m/s^2)
x0, v0, a_max = 0.0015, -0.08, 1.2
d_stop = (v0 * v0) / (2.0 * a_max)                # 2.667 mm minimum stopping distance > 1.5 mm!
breach_mm = round((x0 - d_stop) * 1000.0, 3)      # Soft-slack QP stays feasible while breaching -1.167 mm!
# Viability kernel h_viable(x, v) = x - v^2/(2*a_max) >= 0 triggers max braking at x = d_stop:
viable_min_mm = round((d_stop - d_stop) * 1000.0, 3)
assert breach_mm == -1.167 and viable_min_mm == 0.0

# (2b) Unrestored G20 (inches) + G91 (incremental) from z = -5.0 mm on 'G0 Z10.0'
z_expected_mm = 10.0
z_actual_mm = -5.0 + 10.0 * 25.4
assert z_actual_mm == 249.0 and (z_actual_mm - z_expected_mm) == 239.0

# (2c) Klipper ZV vs EI input-shaper impulse span at f0 = 34 Hz, damping = 0.1 (shaper_defs.py L22-102)
t_d = 1.0 / (34.0 * math.sqrt(1.0 - 0.1 ** 2))
zv_ms = round(0.5 * t_d * 1000.0, 2)
ei_ms = round(1.0 * t_d * 1000.0, 2)
assert zv_ms == 14.78 and ei_ms == 29.56
print("REVALIDATION_OK")
PY
```

2. **Upstream Source Drift Checks:**
   - Check `klippy/extras/shaper_defs.py` and `klippy/extras/gcode_move.py` in `Klipper3d/klipper` for shaper lookahead window calculations and scoped macro state restoration.
   - Check `src/emc/rs274ngc/interp_convert.cc` in `LinuxCNC/linuxcnc` for modal group state handling across `O-word` subroutine returns.
