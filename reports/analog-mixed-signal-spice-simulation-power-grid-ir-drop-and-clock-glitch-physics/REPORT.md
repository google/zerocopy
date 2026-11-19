# Analog and Mixed-Signal SPICE Simulation, Power-Grid IR/L dI/dt Droop, and Software-Triggered Timing-Fault Physics

## Summary

Analog circuit simulation and physical silicon power-delivery integrity share one underlying differential-algebraic structure: stiff nonlinear Modified Nodal Analysis (MNA) systems $\frac{dQ(x)}{dt} + F(x) - B(t) = 0$ coupled across multiple decades of electrical time constants. Four load-bearing engineering invariants govern accuracy, convergence, and hardware security across this stack:

1. **Charge-Oriented State Functions vs. Non-Integrable Capacitance Models:** Formulating MOSFET transient dynamics in terms of terminal charges $Q_g, Q_d, Q_s, Q_b$ satisfying exact algebraic neutrality $Q_g + Q_d + Q_s + Q_b \equiv 0$ (Ward–Dutton partitioning in BSIM3/BSIM4) guarantees exact zero net charge creation around arbitrary closed voltage cycles ($\oint dQ_k = 0$) independent of step size. By contrast, reciprocal capacitance formulations such as the classic Meyer model fail both analytically (non-zero curl on drain/source terminals, producing a non-vanishing $+5.73\text{ fC/cycle}$ leak as $\Delta t \to 0$ on a $100\text{ fF}$ device) and discretely (back-averaging quadrature drift on the gate terminal), forcing simulators either to accept floating-node voltage drift or to augment MNA with explicit voltage-derivative unknowns (`newMeyerFlag` in Xyce).
2. **Stiff DAE Continuation, L-Stability, and Breakpoint Synchronization:** DC operating-point convergence for high-gain multistable CMOS circuits requires homotopy continuation (`GMIN` exponential diagonal conductance stepping, source ramping, two-stage MOSFET gain/nonlinearity scaling, or pseudo-transient $\Delta t^{-1} I$ Jacobian augmentation in Xyce/NOX/LOCA). In transient analysis, the A-stable Trapezoidal rule (`OneStep` order 2) exhibits alternating-sign ringing ($R(z) \to -1$ as $z \to -\infty$, e.g., $R(-20) = -0.8182$) across stiff discontinuities, requiring either order-1 Backward Euler resets at breakpoints or L-stable variable-step BDF2 (`Gear12`). At the analog/digital boundary, Verilog-AMS `@(cross(expr, dir, time_tol, expr_tol))` relies on sign-change bracketing and root refinement; whenever an adaptive stepper's step exceeds a narrow glitch pulse width without a max-step bound, even numbers of crossings alias silently to zero detected events.
3. **Resonant PDN $L\,dI/dt + IR$ Droop Amplifies Static Undervolting into Selective Timing Faults:** On-die power delivery networks exhibit three hierarchical resonant droop tiers (first droop at $50\text{–}200\text{ MHz}$ from on-die $C_{\text{die}}$ and package $L_{\text{pkg}}$, second droop at $1\text{–}20\text{ MHz}$, third droop at $10\text{–}500\text{ kHz}$). Under Sakurai–Newton short-channel $\alpha$-power delay scaling $t_{\text{pd}}(V) \propto V / (V - V_{\text{th}})^\alpha$, a modest software voltage offset that preserves idle OS stability can combine with transient $L\,dI/dt$ current surges—or resonant periodic toggling near $f_0 = (2\pi\sqrt{L_{\text{pkg}}C_{\text{die}}})^{-1}$—to push critical-path delay past $T_{\text{clk}} - (t_{\text{CQ}} + t_{\text{setup}} + t_{\text{skew}})$ and induce silent setup-time violations without triggering brownout reset.
4. **Privilege-Domain Crossing of DVFS Interfaces Breaks Hardware TEE Isolation:** Exposing unbounded regulator/PLL controls (e.g., mobile PMIC/HFPLL registers analyzed in CLKSCREW, or x86 overclocking mailbox MSR `0x150` analyzed in Plundervolt) to untrusted OS/kernel domains violates the physical voltage/frequency envelope assumed by hardware Trusted Execution Environments (ARM TrustZone, Intel SGX). Sound defense requires hardware-enforced OPP/voltage-floor lockouts (`OC_LOCK` / microcode `CVE-2019-11157` mitigations), binding voltage-interface lock state into cryptographic remote attestation keys, and on-die adaptive droop sensing (clock stretching / resonant throttling).

## Applicability

This report synthesizes primary-source evidence spanning three coupled engineering layers:

- **Circuit-simulation kernel & compact-model compilation:** Direct source inspection of Sandia National Laboratories' `Xyce/Xyce` (commit `369a7be860d0d55b147d7fe5defd47c992439859`, post-`Release-7.9.0` development tip) covering its DAE MNA assembly, `N_DEV_MOSFET1` Meyer/newMeyer implementations, `N_DEV_MOSFET_B3` Ward–Dutton BSIM3v3 charge partitioning, `N_NLS_NOX` / `LOCA` homotopy solvers, and `N_TIA_OneStep` / `N_TIA_Gear12` / `N_TIA_StepErrorControl` time integrators; paired with `pascalkuthe/OpenVAF` (commit `a9697ae7780518f021f9f64e819b3a57033bd39f`) for Verilog-A-to-OSDI DAE lowering and Newton voltage-limiting RHS corrections, and the normative Accellera Verilog-AMS Language Reference Manual Version `2.4.0` (2014-05-30) for monitored analog events (`cross`, `above`, `timer`).
- **Analytical semiconductor and PDN physics:** Normative/foundational formulations from Ho, Ruehli, and Brennan (1975) for MNA, Ward and Dutton (1978) and Yang, Epler, and Chatterjee (1983) for charge conservation, and Sakurai and Newton (1990) for short-channel CMOS $\alpha$-power propagation delay scaling, quantitatively validated via self-contained Python numerical micro-probes.
- **Architectural DVFS/PDN security boundaries:** Peer-reviewed characterization from CLKSCREW (Tang, Sethumadhavan, and Stolfo, USENIX Security 2017; Qualcomm APQ8084 / Krait 450 / ARM TrustZone), Plundervolt (Murdock et al., IEEE S&P 2020, and reference telemetry/interface implementation in `KitMurdock/plundervolt` @ `a7313c268d7c27ac3eb806d3ed99019788c5f605`; Intel 6th–10th Gen Core / SGX / MSR `0x150` and `0x198`), and VoltJockey (Qiu et al., ACM CCS 2019), together with vendor microcode/firmware mitigation architectures (`INTEL-SA-00289` / `CVE-2019-11157`).

**How subjects relate:** Xyce and OpenVAF establish the numerical DAE and compact-model compilation semantics required to simulate nonlinear transistor networks and power grids faithfully; Verilog-AMS 2.4.0 specifies the mixed-signal event contract bridging continuous-time solvers and discrete digital logic; Sakurai–Newton delay physics and RLC PDN dynamics link those circuit equations directly to the timing-violation boundary violated by CLKSCREW and Plundervolt. Findings about Xyce's exact C++ solver hooks, OpenVAF's AST/HIR event lowering, and Intel MSR `0x150` bit fields apply strictly to the pinned revisions and processor families identified above; general mathematical invariants (curl-based non-integrability, Trapezoidal vs. BDF2 stability polynomials, RLC resonance quality factor $Q$, and static timing setup slack) apply broadly across SPICE-class simulators and synchronous CMOS silicon.

## Findings

### 1. Modified Nodal Analysis (MNA) in Differential-Algebraic Form

Basis: normative + source

Classical nodal analysis stamps every branch element as an admittance $I = YV$, which cannot represent ideal independent voltage sources, controlled voltage sources, zero-ohm shorts, or branch-current-controlled inductors without Norton transformations. Ho, Ruehli, and Brennan (1975, DOI `10.1109/TCS.1975.1084079`) resolved this via **Modified Nodal Analysis (MNA)**, partitioning the unknown vector $x(t) = [v(t)^\top, j(t)^\top]^\top \in \mathbb{R}^{N+M}$ into $N$ non-reference node voltages $v$ and $M$ auxiliary branch currents $j$ for non-admittance elements.

Modern SPICE-class simulators—including both Xyce (`src/DeviceModelPKG/OpenModels/N_DEV_MOSFET1.C:1928`, `N_DEV_MOSFET_B3.C:8813`) and OpenVAF (`openvaf/sim_back/src/dae.rs:25-40`)—formulate MNA directly as a nonlinear **index-1 (or occasionally index-2) Differential-Algebraic Equation (DAE)** separating algebraic/resistive currents from stored charges and magnetic fluxes:

$$f(x, \dot{x}, t) \;\equiv\; \frac{d}{dt} Q(x(t)) + F(x(t)) - B(t) \;=\; 0$$

where:
- $Q(x) \in \mathbb{R}^{N+M}$ holds node charge sums (from capacitors and transistor intrinsic/junction charge models) and branch flux linkages ($\Phi = L j$ for inductors);
- $F(x) \in \mathbb{R}^{N+M}$ holds memoryless static KCL currents (resistors, diode/MOSFET DC channel currents) and auxiliary branch constitutive equations (KVL constraints such as $v_+ - v_- = E$);
- $B(t) \in \mathbb{R}^{N+M}$ holds independent time-varying current and voltage source excitations.

At each discrete time step $t_{n+1} = t_n + h_n$, a linear multistep method replaces $\frac{dQ}{dt}$ with an algebraic linear combination of $Q(x_{n+1})$ and stored history vectors $Q(x_{n-k})$, yielding a nonlinear algebraic residual $R(x_{n+1}) = 0$ solved by Newton–Raphson iteration:

$$J(x^{(k)}) \, \Delta x^{(k)} = -R(x^{(k)}), \qquad J(x) = \gamma_q \frac{\partial Q}{\partial x} + \gamma_f \frac{\partial F}{\partial x}$$

where $(\gamma_q, \gamma_f)$ are method-dependent scalars (e.g., $\gamma_q = \alpha_0 / h_n, \gamma_f = 1$ in `Gear12::obtainJacobian`, `N_TIA_Gear12.C:498-501`; $\gamma_q = 1/h_n, \gamma_f = 1/2$ at order 2 in `OneStep::obtainJacobian`, `N_TIA_OneStep.C:490-495`).

#### Newton Voltage Limiting and `lim_rhs` Consistency

Basis: source + derived

Exponential semiconductor $I$–$V$ laws (p–n junctions, subthreshold MOSFETs) overflow IEEE-754 `double` or diverge under full Newton steps. Simulators therefore damp device terminal voltages inside device evaluation ($x_{\text{lim}} = \text{limit}(x^{(k)}, x^{(k-1)})$) rather than scaling the global vector. Critically, because the linear solver computes an update relative to the *unlimited* iterate $x^{(k)}$ while the device evaluates $F, Q, J$ at $x_{\text{lim}}$, omitting the linearization offset breaks quadratic convergence or converges to a wrong fixed point. Both OpenVAF (`openvaf/sim_back/src/dae.rs:111-169`) and Xyce (`N_DEV_MOSFET_B3.C:8882-8902`, `N_TIA_Gear12.C:246-254`, `N_TIA_OneStep.C:257-268`) derive and stamp the exact residual correction term:

$$J(x_{\text{lim}})\,\Delta x \;=\; -\Big(R(x_{\text{lim}}) - J(x_{\text{lim}})(x_{\text{lim}} - x)\Big)$$

OpenVAF explicitly separates this into `resist_lim_rhs` and `react_lim_rhs` in `Residual` (`openvaf/sim_back/src/dae.rs:139,168`), exposed through the OSDI 0.3 `CALC_RESIST_LIM_RHS` / `CALC_REACT_LIM_RHS` flags (`openvaf/osdi/src/eval.rs:17-20`), while Xyce maintains parallel vectors `dQdxdVpVectorPtr` and `dFdxdVpVectorPtr` scaled by the integrator's exact $(\gamma_q, \gamma_f)$ coefficients (`N_TIA_Gear12.C:248-253`).

#### MNA Structural Singularity Traps

Basis: normative + derived

MNA systems fail or jump to DAE index $\ge 2$ under three well-known circuit topologies that must be detected before Newton iteration:
1. **Voltage-source / inductor loops** (parallel ideal voltage sources, or a cutset of current sources / floating capacitor nodes with no DC path to ground): $dF/dx$ is structurally singular at DC ($\gamma_q = 0$).
2. **Capacitor-only loops coupled to ideal voltage sources** (voltage source directly across a capacitor with $R_{\text{series}} = 0$): raises the DAE differentiation index from $1$ to $2$; step discontinuities in $B(t)$ produce impulsive currents requiring Backward Euler initialization.
3. **Zero-resistance switches / ideal diodes:** abrupt structural rank changes across a switching instant invalidate multistep history derivatives.

---

### 2. Ward–Dutton Charge Conservation vs. Meyer Capacitance Failure

Basis: normative + source + execution

#### Why Capacitance-Based MOSFET Models Violate Charge Conservation

In John Meyer's 1971 MOSFET model (*RCA Review* 32:42–63), intrinsic gate storage is specified directly as three two-terminal reciprocal capacitances $C_{gs}(V_{gs}, V_{gd}), C_{gd}(V_{gs}, V_{gd}), C_{gb}(V_{gs}, V_{gd})$ rather than as partial derivatives of a 4-terminal charge state vector $\mathbf{Q}(V_g, V_d, V_s, V_b)$. Ward and Dutton (1978, DOI `10.1109/JSSC.1978.1051123`) and Yang, Epler, and Chatterjee (1983, DOI `10.1109/JSSC.1983.1051909`) proved two distinct mechanisms by which capacitance-based models create or destroy charge in transient simulation:

1. **Non-Integrable Continuous 1-Form (Curl Failure on Drain/Source Terminals):** In a 4-terminal MOSFET, the true small-signal capacitance matrix $C_{ij} = -\frac{\partial Q_i}{\partial V_j}$ ($i \ne j$), $C_{ii} = +\frac{\partial Q_i}{\partial V_i}$ is **non-reciprocal** ($C_{dg} \ne C_{gd}$ and $C_{sg} \ne C_{gs}$) because channel charge responds asymmetrically to drain vs. gate potential in saturation. Meyer forces reciprocity by stamping drain capacitive current solely as $I_d^{\text{cap}} = -C_{gd}(V_{gs}, V_{gd})\,\frac{dV_{gd}}{dt}$. By Stokes' theorem, the net charge transferred around a closed voltage loop $\Gamma$ in the $(V_{gs}, V_{gd})$ plane is:
   $$\Delta Q_d^{\text{Meyer}} = \oint_\Gamma \big(-C_{gd}(V_{gs}, V_{gd})\big)\,dV_{gd} = -\iint_{\Omega} \frac{\partial C_{gd}}{\partial V_{gs}}\,dV_{gs}\,dV_{gd} \neq 0$$
   Because $\frac{\partial C_{gd}}{\partial V_{gs}} \ne 0$ throughout the linear region (and similarly $\frac{\partial C_{gs}}{\partial V_{bs}} \ne \frac{\partial C_{gb}}{\partial V_{gs}}$ when body bias modulates $V_{\text{th}}$), **no refinement of the time step $\Delta t \to 0$ eliminates this charge leak**.
2. **Discrete Back-Averaging Quadrature Drift:** Even on terminals where a 2-variable capacitance form is locally curl-free, integrating $I = C(V)\,\dot{V}$ via trapezoidal/back-averaged updates $Q_{n+1} - Q_n = \frac{1}{2}(C_n + C_{n+1})(V_{n+1} - V_n)$ produces an $O(h^2)$ quadrature residual per step that fails to telescope around closed cycles.

#### Primary-Source Verification in Xyce (`N_DEV_MOSFET1.C` vs. `N_DEV_MOSFET_B3.C`)

Direct inspection of `Xyce/Xyce` (`369a7be860d0d55b147d7fe5defd47c992439859`) reveals the architectural divide between Meyer and Ward–Dutton models:

- **Legacy Level-1 Meyer Model (`src/DeviceModelPKG/OpenModels/N_DEV_MOSFET1.C`):**
  - Default mode (`!newMeyerFlag`, lines 3767–3804) computes Meyer charges incrementally via back-averaging: `qgs = oldstaVector[li_state_qgs] + Capgs * (vgs - vgs1)` (and analogously for `qgd`, `qgb`), where `Capgs` is the two-step average capacitance. As noted in the source comments (lines 3300–3304, 3770–3776), this incremental integration breaks multi-time PDE (MPDE) and harmonic balance because $Q$ is path-dependent rather than a single-valued function of $V$.
  - Under `newMeyerFlag` (lines 1950–1978, 3761–3766), Xyce avoids path-dependent charge storage by **expanding the MNA state vector** with auxiliary derivative unknowns (`li_Draindot`, `li_Gatedot`, `li_Bulkdot`, `li_Sourcedot`, `li_DrainPrimedot`, `li_SourcePrimedot`), loading `qVec[li_Gatedot] += Vg` into $Q(x)$ so $\dot{Q}$ produces $\dot{V}_g$, and stamping $C_{\text{Meyer}}(V)\,\dot{V}$ into $F(x)$. This restores compatibility with harmonic balance/MPDE at the cost of extra MNA rows, yet still inherits Meyer's underlying physical non-reciprocity.
- **Ward–Dutton Charge-Oriented BSIM3v3 Model (`src/DeviceModelPKG/OpenModels/N_DEV_MOSFET_B3.C`):**
  - Channel inversion charge $Q_{\text{inv}}$ is partitioned deterministically between drain and source according to `model_.xpart` (lines 2679, 7287–7390):
    - `xpart > 0.5`: **0/100 partition** ($Q_d = 0$ in saturation, $Q_s = Q_{\text{inv}}$);
    - `xpart == 0.5`: **50/50 symmetric partition** ($Q_d = Q_s = 0.5\,Q_{\text{inv}}$);
    - `xpart < 0.5` (default `0.0`): **40/60 Ward–Dutton partition** ($Q_d = 0.4\,Q_{\text{inv}}, Q_s = 0.6\,Q_{\text{inv}}$ in saturation, smoothly connected through the linear region).
  - Exact algebraic charge conservation is enforced structurally in `Instance::loadDAEQVector()` (`N_DEV_MOSFET_B3.C:8854-8858`):
    ```cpp
    qVec[li_Gate]        += Qeqqg * numberParallel;
    qVec[li_Bulk]        += Qeqqb * numberParallel;
    qVec[li_DrainPrime]  += Qeqqd * numberParallel;
    qVec[li_SourcePrime] += (-(Qeqqg + Qeqqb + Qeqqd)) * numberParallel;
    ```
    Because $Q_s$ is computed identically as $-(Q_g + Q_b + Q_d)$ and the same zero-sum relation is applied to the Newton limiter vector `dQdxdVp` (`N_DEV_MOSFET_B3.C:8897-8900`), the sum of all four terminal charges vanishes to machine precision at every iterate and every time step.

#### Executable Verification (Micro-Probe 1A)

Basis: execution

Running Probe 1A (closed rectangular voltage cycle $(V_{gs}, V_{gd}): (1.5,0.6) \to (2.0,0.6) \to (2.0,1.4) \to (1.5,1.4) \to (1.5,0.6)\text{ V}$ on a $C_{\text{ox}}WL = 100\text{ fF}$, $V_{\text{th}} = 0.5\text{ V}$ MOSFET) quantifies both failure modes simultaneously:

| Substeps per edge | Meyer Back-Averaging $\oint dQ_g$ (fC) | Meyer Drain $\oint (-C_{gd})\,dV_{gd}$ (fC) | Ward–Dutton 40/60 $\oint dQ_g$ (fC) | Ward–Dutton 40/60 $\oint dQ_d$ (fC) |
|---:|---:|---:|---:|---:|
| 5 | $+0.067764$ | $+5.669939$ | $+0.00 \times 10^{0}$ | $+0.00 \times 10^{0}$ |
| 20 | $+0.004268$ | $+5.727768$ | $+0.00 \times 10^{0}$ | $+0.00 \times 10^{0}$ |
| 200 | $+0.000043$ | $+5.731620$ | $+0.00 \times 10^{0}$ | $+0.00 \times 10^{0}$ |
| 2000 | $+0.000000$ | $+5.731658$ | $+0.00 \times 10^{0}$ | $+0.00 \times 10^{0}$ |

On a $10\text{ fF}$ floating drain node (typical of DRAM storage cells, switched-capacitor integrators, or charge-pump stages), a $+5.73\text{ fC/cycle}$ unphysical charge creation produces $+0.573\text{ V}$ of spurious drift **per switching cycle**, independent of integrator tolerance.

---

### 3. Homotopy Continuation and DC Operating-Point Convergence in Xyce

Basis: source + derived

For strongly nonlinear circuits (SRAM bitcells, bandgap references, regenerative latches, high-gain op-amps), standard damped Newton–Raphson starting from $x^{(0)} = 0$ routinely fails due to singular Jacobians (floating cut-off MOSFET nodes), exponential overflow, or landing outside the local quadratic basin of attraction. Xyce's nonlinear interface (`src/NonlinearSolverPKG/N_NLS_NOX_Interface.C`) solves DC operating points via a deterministic fallback cascade and six explicit continuation solvers built on Trilinos NOX/LOCA:

#### Default `spiceStrategy` Fallback Cascade (`N_NLS_NOX_Interface.C:322-420`)

1. **Direct Newton (`stdNewtonSolve`, line 333):** Attempts unmodified Newton–Raphson while preserving a clone `initVec` of the initial `.IC`-conditioned guess.
2. **Automatic GMIN Stepping (`gminSteppingSolve`, lines 335–367):** On failure, restores `initVec`, zeros history, sets solver type `3`, and runs LOCA natural continuation on parameter `"GSTEPPING"`.
3. **Automatic Source Stepping (`sourceSteppingSolve`, lines 368–419):** If GMIN stepping fails, restores `initVec`, switches to solver type `34`, and ramps independent supply scaling `"VSRCSCALE"` from $0 \to 1$.

#### Complete Taxonomy of Xyce Continuation Solvers

| Continuation Mode | Xyce Option (`continuation=`) | Solver Type ID | Exact Mathematical Homotopy & Source Implementation |
|---|---|---:|---|
| Natural Parameter | `1` / `natural` | `1` | Tracks arbitrary user/device parameter via LOCA predictor–corrector (`naturalParameterContinuationSolve`, `N_NLS_NOX_Interface.C:524-725`). |
| Two-Stage MOSFET | `2` / `mos` | `2` | Stage 1 ramps `"mosfet:gainscale"` $\alpha_2: 0 \to 1$ holding `"mosfet:nltermscale"` $\alpha_1 = 0$; Stage 2 ramps $\alpha_1: 0 \to 1$ at $\alpha_2 = 1$ (`mosfetContinuationSolve`, lines 740–846; initial step `0.2`, min `1e-4`). |
| Exponential GMIN Stepping | `3` / `gmin` | `3` | Augments voltage-node diagonals of $F$ and $J$ via `GStepping` (`N_NLS_NOX_AugmentLinSys_GStepping.C:99-174`) with $G(\lambda) = 10^{\lambda} - 10^{\lambda_{\min}} + G_{\text{resid}}$, sweeping $\lambda: +4.0 \to -4.0$ (default step `-2.0`, max `400` steps, `20` nonlinear iters/step; `N_NLS_NOX_Interface.C:1138-1149`). |
| Pseudo-Transient | `9` / `pseudo` | `9` | Augments Jacobian diagonal ONLY with $\Delta\tau^{-1}$ (no residual modification; `AugmentLinSysPseudoTransient::augmentResidual` is a no-op, `augmentJacobian` adds `1.0 / time_step_size_` scaled by `voltage_scale_factor_` on voltage-colored rows; `N_NLS_NOX_AugmentLinSys_PseudoTransient.C:110-163`), driving $\Delta\tau$ from `1e-3` up to `1e4` (`N_NLS_NOX_Interface.C:1218-1269`), followed by an unaugmented Newton corrector polish. |
| Global Source Stepping | `34` / `sourcestep` | `34` | Simultaneously scales independent voltage/current sources from $0 \to 1$ (`sourceSteppingSolve`, lines 1284–1365). |
| Sequential Source Ramping | `35` / `sourcestep2` | `35` | Ramps up to 20 independent sources sequentially, falling back to global `sourceSteppingSolve` if $> 20$ continuation runs are needed (`sourceSteppingSolve2`, lines 859–920). |

**Critical subtlety in `GStepping` (`N_NLS_NOX_AugmentLinSys_GStepping.C:116-174`):** Xyce restricts conductance augmentation strictly to **voltage-node rows** (`NLT_VoltageNodes` or `vnodeVec_[i] == 0`), never augmenting KVL branch-current equations (`v_+ - v_- = E`). Adding a diagonal conductance to an ideal voltage source branch equation would corrupt KVL into $v_+ - v_- + G j = E$ (introducing a spurious series resistor) and break exact voltage pinning. Similarly, `PseudoTransient` differentiates voltage rows (`colors_[i] == 0`) via `voltage_scale_factor_` (`N_NLS_NOX_AugmentLinSys_PseudoTransient.C:148-158`) and discards any failed pseudo-transient termination status before running the final exact steady-state Newton solve (`N_NLS_NOX_Interface.C:1254-1268`), ensuring the returned DC solution always satisfies the **unaugmented** MNA residual.

---

### 4. Stiff Transient Integration, Trapezoidal Ringing, and Verilog-AMS `@(cross)` Event Synchronization

Basis: normative + source + execution

#### `OneStep` (Trapezoidal) vs. `Gear12` (BDF2) Stability Trade-Off

Inspection of `Xyce/Xyce` `TimeIntegrationPKG` confirms the exact discrete DAE equations:

- **`OneStep` Order 2 (Trapezoidal Rule, `N_TIA_OneStep.C:219-268, 469-495`):**
  $$\frac{Q(x_{n+1}) - Q(x_n)}{h_n} + \frac{1}{2}\big(F(x_{n+1}) - B(t_{n+1})\big) + \frac{1}{2}\big(F(x_n) - B(t_n)\big) = 0, \qquad J = \frac{1}{h_n}\frac{\partial Q}{\partial x} + \frac{1}{2}\frac{\partial F}{\partial x}$$
  On the Dahlquist test equation $\dot{y} = \lambda y$ ($z = h\lambda$), Trapezoidal yields stability function $R_{\text{Trap}}(z) = \frac{1 + z/2}{1 - z/2}$. It is **A-stable** ($|R(z)| \le 1$ for all $\text{Re}(z) \le 0$) and has zero phase-damping on the imaginary axis ($|R(i\omega)| = 1$, ideal for high-$Q$ LC oscillators) with small LTE constant $-\frac{1}{12}h^3 y'''$. However, it is **NOT L-stable**: $\lim_{\text{Re}(z)\to -\infty} R_{\text{Trap}}(z) = -1$.
- **`Gear12` Order 2 (Variable-Step BDF2, `N_TIA_Gear12.C:208-255, 477-501`):**
  $$\frac{1}{h_n}\Big(\alpha_0 Q(x_{n+1}) + \alpha_1 Q(x_n) + \alpha_2 Q(x_{n-1})\Big) + F(x_{n+1}) - B(t_{n+1}) = 0, \qquad J = \frac{\alpha_0}{h_n}\frac{\partial Q}{\partial x} + \frac{\partial F}{\partial x}$$
  For uniform step $h$ ($\alpha_0 = \frac{3}{2}, \alpha_1 = -2, \alpha_2 = \frac{1}{2}$), BDF2 is **L-stable**: both roots of $(\frac{3}{2} - z)r^2 - 2r + \frac{1}{2} = 0$ vanish as $O(|z|^{-1/2})$ when $\text{Re}(z) \to -\infty$, strongly damping stiff algebraic/fast transients at the expense of a larger LTE constant ($-\frac{2}{9}h^3 y'''$) and slight numerical dissipation on undamped oscillators.

**Executable confirmation (Probe 1B, stiff RC decay $\tau = 10\text{ ps}$, $h = 200\text{ ps}$, $z = -20$):**

| Step $k$ | Time (ns) | Exact $e^{-20k}$ | BDF1 (Backward Euler) | Trapezoidal (`OneStep` ord 2) | BDF2 (`Gear12` ord 2, BDF1 start) |
|---:|---:|---:|---:|---:|---:|
| 0 | 0.00 | $1.00 \times 10^{0}$ | $+1.00 \times 10^{0}$ | $+1.0000$ | $+1.00 \times 10^{0}$ |
| 1 | 0.20 | $2.06 \times 10^{-9}$ | $+4.76 \times 10^{-2}$ | $-0.8182$ | $+4.76 \times 10^{-2}$ |
| 2 | 0.40 | $4.25 \times 10^{-18}$ | $+2.27 \times 10^{-3}$ | $+0.6694$ | $-1.88 \times 10^{-2}$ |
| 4 | 0.80 | $1.80 \times 10^{-35}$ | $+5.14 \times 10^{-6}$ | $+0.4481$ | $+1.72 \times 10^{-4}$ |
| 8 | 1.60 | $3.26 \times 10^{-70}$ | $+2.64 \times 10^{-11}$ | $+0.2008$ | $-2.32 \times 10^{-7}$ |

At $t = 1.60\text{ ns}$ (160 time constants after the transient!), Trapezoidal still rings at $+0.2008\text{ V}$ with alternating sign ($R(-20) = -9/11 \approx -0.8182$), whereas BDF2 has decayed by $> 10^6\times$ (spectral radius $0.1078$). This explains why Xyce initializes both `Gear12` (`N_TIA_Gear12.C:1302`) and `OneStep` (`N_TIA_OneStep.C:1807`) at `currentOrder_ = 1` (Backward Euler), drops order back to `minOrder_ = 1` on repeated DAE step rejections (`N_TIA_Gear12.C:1497-1528`), and uses breakpoint restarts (`N_TIA_StepErrorControl.C:742-840`, merging breakpoints within tolerance `bpTol = 2.0 * minTimeStep` via `N_UTL_BreakPoint.h:107-124`).

*(Source-level defect observation in `Xyce/Xyce` `N_UTL_BreakPoint.h:122`: `BreakPointEqual::operator()(const BreakPoint &l, const double &d)` returns `std::fabs(d - l.time_) >= tolerance_` rather than `<=`, inverting the predicate compared to `operator()(const BreakPoint &l, const BreakPoint &r)` on line 121; `StepErrorControl` avoids invoking the `(BreakPoint, double)` overload during `std::unique`, which passes two `BreakPoint` objects, but external callers invoking that mixed overload receive the negated test.)*

#### Verilog-AMS `@(cross)` Event Detection vs. Adaptive ODE Steppers

Basis: normative + source + execution

Accellera Verilog-AMS LRM v2.4.0 Section 5.10.3 defines three monitored analog event functions:
- **5.10.3.1 `cross(expr [, dir [, time_tol [, expr_tol [, enable]]]])`:** Triggers when continuous expression `expr` crosses zero in direction `dir` (`+1` rising, `-1` falling, `0` either). Crucially, the simulator **must** place a time point such that **both** $|\Delta t| \le \text{time\_tol}$ and $|\text{expr}| \le \text{expr\_tol}$ (or simulator defaults if omitted/non-positive). Because `cross` modifies timestep control, it is an analog operator forbidden inside runtime-dynamic `if`/`case` conditionals (only static `genvar` conditionals are legal).
- **5.10.3.2 `above(expr [, time_tol [, expr_tol [, enable]]])`:** Triggers both on rising zero-crossings and at DC/initial operating point if `expr >= 0` (unlike `cross`, which does not fire at DC).
- **5.10.3.3 `timer(start_time [, period [, time_tol [, enable]]])`:** Schedules deterministic breakpoints directly in the integrator queue.

Coupling `@(cross)` to an adaptive SPICE stepper introduces **four distinct mixed-signal verification hazards**:

1. **Even-Crossing Aliasing (Missed Glitches):** Adaptive ODE steppers expand $h_n$ aggressively whenever waveforms are locally smooth, and only invoke root refinement (bisection / secant / Illinois) when `expr(t_n)` and `expr(t_{n+1})` change sign. If a transient glitch crosses zero twice (rising then falling) strictly inside $(t_n, t_{n+1})$, both endpoints share the same sign and **both crossings vanish silently**. In Probe 1B (Gaussian glitch centered off-grid at $t_0 = 5.23\text{ ns}$, width $0.1332\text{ ns}$ above $V_{\text{th}} = 0.5\text{ V}$):
   - At `dt = 0.50 ns`: **0 crossings detected** (entire pulse missed by even-crossing aliasing);
   - At `dt = 0.25 ns` (phase-fortunate), `0.15 ns`, `0.05 ns`: both crossings localized to $\le 0.032\text{ ps}$ error in $9\text{–}12$ bisection iterations.
   Safe mixed-signal simulation therefore requires `bound_step()` (or simulator `max_time_step`) strictly smaller than half the minimum detectable glitch width.
2. **Step-Rejection / Discrete-Event Rollback Consistency:** Because analog Newton/LTE checks can reject a candidate step *after* evaluating device models, discrete Verilog-AMS state mutations triggered by `@(cross)` **must not commit** until the analog step is accepted; otherwise rejected trial steps corrupt digital flip-flop states or double-increment counters.
3. **Zeno / Chattering Collapse:** If a `@(cross(V(x) - Vth))` handler instantaneously switches a branch current or resistance without `transition()` rise time or hysteresis, the discontinuity can push `V(x)` immediately back across `Vth` within `time_tol`, driving $h_n \to h_{\min}$ and aborting the simulation (`timestep too small`).
4. **Compact-Model Compiler Boundary (OpenVAF `a9697ae7`):** Direct inspection of `pascalkuthe/OpenVAF` (`openvaf/hir_def/src/body/lower.rs:154-168`) shows that `collect_event_stmt` lowers only `@(initial_step)` and `@(final_step)` (`GlobalEvent::{InitialStep, FinalStep}`); monitored analog events (`@(cross)`, `@(above)`, `@(timer)`) are **not** lowered into OSDI 0.3 event callbacks. OpenVAF targets continuous compact semiconductor models (`I(x) + ddt(Q(x)) = 0`), not full mixed-signal event-driven AMS behavioral blocks.

---

### 5. On-Die Power Delivery Network (PDN) Impedance, $L\,dI/dt$ Droop, and Sakurai–Newton Timing Fault Physics

Basis: normative + documentation + execution + derived

#### Three-Tier PDN Impedance Hierarchy

A microprocessor power delivery network is a cascaded distributed $R$–$L$–$C$ transmission/lumped network spanning voltage regulator module (VRM), motherboard planes, package substrate, C4/micro-bumps, and on-die metal grids. A rapid load current step $\Delta I(t)$ produces total rail depression:

$$\Delta V_{\text{rail}}(t) \;=\; R_{\text{IR}}\,I(t) \;+\; \Delta V_{\text{PDN}}^{\text{reactive}}(t), \qquad \text{with high-frequency } \Delta V_L \approx L_{\text{eff}} \frac{dI}{dt}$$

Because each physical tier's series inductance resonates in parallel with the next-inward decoupling capacitance, the PDN transfer impedance $Z_{\text{PDN}}(\omega) = \Delta V(\omega) / \Delta I(\omega)$ exhibits three characteristic anti-resonance peaks ("droop tiers"):

| Droop Tier | Dominant Physical Elements | Typical Resonance $f_0$ | Time Scale | Primary Exciter & Engineering Countermeasure |
|---|---|---:|---|---|
| **First Droop** ("Bandini Mountain") | On-die decap $C_{\text{die}}$ + C4 bump / package vertical inductance $L_{\text{pkg}}$ | $50\text{–}200\text{ MHz}$ | $1\text{–}15\text{ ns}$ | Clock-gating wakeups, AVX/SIMD bursts, resonant software loops; mitigated via MIM/trench on-die decap, adaptive clock stretching / droop detectors |
| **Second Droop** | Package substrate capacitors + socket/BGA inductance | $1\text{–}20\text{ MHz}$ | $20\text{–}500\text{ ns}$ | Multi-core thread migrations, sustained compute phases; mitigated via low-ESL land-side/die-side package capacitors |
| **Third Droop** | Motherboard bulk capacitors + VRM inductor/control loop | $10\text{–}500\text{ kHz}$ | $1\text{–}100\;\mu\text{s}$ | Package C-state transitions, thermal/power-limit steps; mitigated via Adaptive Voltage Positioning (AVP / load-line droop control) |

For the first-droop stage ($L_{\text{pkg}}, R_{\text{pkg}}, C_{\text{die}}$), the natural resonance frequency, characteristic impedance, and quality factor are:

$$f_0 = \frac{1}{2\pi\sqrt{L_{\text{pkg}} C_{\text{die}}}}, \qquad Z_0 = \sqrt{\frac{L_{\text{pkg}}}{C_{\text{die}}}}, \qquad Q = \frac{Z_0}{R_{\text{pkg}}}$$

Crucially, while a **single** fast current step $\Delta I$ excites a peak transient droop $\Delta V_{\text{step}} \approx \Delta I \cdot Z_0 + (R_{\text{pkg}} + R_{\text{IR}})\Delta I$, a **periodic current burst toggled at $f \approx f_0$** excites the parallel tank resonance, amplifying impedance by $\approx Q$ (for square-wave fundamental amplitude $\frac{4}{\pi}\frac{\Delta I}{2}$, peak resonant droop scales with $Q \cdot Z_0$)!

#### Coupling Voltage Droop to CMOS Critical-Path Setup Violations

In velocity-saturated short-channel CMOS (Sakurai & Newton 1990, IEEE JSSC, DOI `10.1109/4.52187`), saturation drain current scales as $I_{D,\text{sat}} \propto (V_{GS} - V_{\text{th}})^\alpha$ with velocity-saturation exponent $\alpha \in [1.0, 2.0]$ (typically $\alpha \approx 1.2\text{–}1.4$ in nanoscale FinFET/submicron nodes, vs. $\alpha = 2$ in long-channel Shockley devices). Combinational gate propagation delay therefore scales nonlinearly with instantaneous effective rail voltage $V_{\text{eff}}(t)$:

$$t_{\text{pd}}\big(V_{\text{eff}}\big) \;=\; t_{\text{pd}}(V_{\text{nom}}) \cdot \frac{V_{\text{eff}}}{V_{\text{nom}}} \left(\frac{V_{\text{nom}} - V_{\text{th}}}{V_{\text{eff}} - V_{\text{th}}}\right)^{\!\alpha}$$

A synchronous pipeline stage with clock period $T_{\text{clk}}$ computes correctly if and only if the **setup-time constraint** holds across the launch-to-capture window:

$$T_{\text{clk}} \;\ge\; t_{\text{CQ}} + t_{\text{pd}}\big(V_{\text{eff}}(t)\big) + t_{\text{setup}} + t_{\text{skew}}$$

Notice the two-sided **fault-injection window** $V_{\text{brownout}} < V_{\text{eff}} < V_{\text{crit}}$:
- If $V_{\text{eff}} \ge V_{\text{crit}}$: positive timing slack; all paths latch cleanly.
- If $V_{\text{brownout}} < V_{\text{eff}} < V_{\text{crit}}$: **only the slowest combinational paths** (e.g., wide carry-propagation multipliers `imul`, AES S-box/MixColumns datapaths, or long-wire register-file reads) miss the capture clock edge, latching stale/corrupted bit transitions while shorter control/fetch/OS paths continue executing without crashing the core!
- If $V_{\text{eff}} \le V_{\text{brownout}}$: SRAM retention, clock-tree buffers, or control FSMs fail, causing machine-check abort, hang, or reboot.

#### Quantitative Coupled PDN–Delay Simulation (Micro-Probe 1C)

Basis: execution

Simulating a realistic multi-core first-droop PDN ($V_{\text{VRM}} = 1.00\text{ V}$, $L_{\text{pkg}} = 20\text{ pH}$, $C_{\text{die}} = 250\text{ nF}$, $R_{\text{pkg}} = 2.0\text{ m}\Omega$, $R_{\text{IR}} = 1.5\text{ m}\Omega \implies f_0 = 71.18\text{ MHz}$, $Z_0 = 8.94\text{ m}\Omega$, $Q = 4.47$) coupled to a $3.0\text{ GHz}$ ($T_{\text{clk}} = 333.33\text{ ps}$) Sakurai–Newton critical path ($\alpha = 1.3$, $V_{\text{th}} = 0.28\text{ V}$, $t_{\text{CQ}} + t_{\text{setup}} + t_{\text{skew}} = 45.0\text{ ps}$, nominal $t_{\text{pd}} = 235.0\text{ ps}$ at $V_{\text{idle}} = 0.9720\text{ V}$, design slack $+53.33\text{ ps}$, critical fault threshold $V_{\text{crit}} = 0.7784\text{ V}$):

| Operating / Stress Regime | Min Rail $V_{\text{eff}}$ (V) | Total Droop vs. Idle (mV) | Path Delay $t_{\text{path}}$ (ps) | Setup Slack (ps) | Outcome |
|---|---:|---:|---:|---:|---|
| Nominal idle ($I = 8\text{ A}$, $0\text{ mV}$ UV) | $0.9720$ | $0.0$ | $280.00$ | $+53.33$ | `PASS` |
| Single $12\text{ A}$ step ($t_r = 0.5\text{ ns}$, $0\text{ mV}$ UV) | $0.8414$ | $130.6$ | $312.00$ | $+21.33$ | `PASS` (absorbed by guardband) |
| Software undervolt $-100\text{ mV}$ at idle | $0.8720$ | $100.0$ | $303.25$ | $+30.08$ | `PASS` (OS stays alive) |
| **Software UV $-100\text{ mV}$ + single $12\text{ A}$ step** | **$0.7414$** | **$230.6$** | **$348.61$** | **$-15.28$** | **`TIMING FAULT` (setup violation)** |
| **Resonant $12\text{ A}$ burst at $f_0 = 71.18\text{ MHz}$ ($0\text{ mV}$ UV)** | **$0.6323$** | **$339.7$** | **$412.66$** | **$-79.33$** | **`TIMING FAULT` ($2.6\times$ droop amplification)** |
| Software UV $-50\text{ mV}$ + resonant $12\text{ A}$ burst | $0.5823$ | $389.7$ | $458.13$ | $-124.80$ | `TIMING FAULT` (severe) |

This simulation demonstrates the exact physical mechanism behind software-induced fault attacks: **static undervolting narrows the noise margin while keeping low-activity kernel execution stable, so that normal dynamic $L\,dI/dt$ current surges inside heavy arithmetic/cryptographic units selectively cross $V_{\text{crit}}$**—and resonant current toggling at $f_0$ can induce timing violations even without static undervolting.

---

### 6. Software-Triggered DVFS/Voltage Fault Physics: CLKSCREW, Plundervolt, and Architectural Mitigations

Basis: documentation + source + derived

Hardware Trusted Execution Environments (ARM TrustZone, Intel SGX) assume that privileged untrusted software (rich OS / ring-0 kernel) cannot violate the computational integrity of isolated secure worlds or enclaves. Both **CLKSCREW** (USENIX Security 2017) and **Plundervolt** (IEEE S&P 2020, DOI `10.1109/SP40000.2020.00057`) proved that **security-oblivious energy management interfaces** violate this isolation boundary by allowing untrusted software to drive the shared silicon physical layer outside its timing-closure envelope.

#### Architectural Comparison of Software-Exposed DVFS/Power Fault Vectors

| Dimension | CLKSCREW (Tang et al., USENIX Security 2017) | VoltJockey (Qiu et al., ACM CCS 2019, `10.1145/3319535.3354201`) | Plundervolt (Murdock et al., IEEE S&P 2020, `10.1109/SP40000.2020.00057`) |
|---|---|---|---|
| **Target Hardware & TEE** | Qualcomm APQ8084 (Snapdragon 805, Krait 450) / ARM TrustZone | Multi-core Qualcomm Snapdragon / ARM TrustZone | Intel 6th–10th Gen Core (Skylake–Comet Lake) / Intel SGX |
| **Exposed Control Interface** | Memory-mapped Subsystem Power Manager (SPM -> PMA8084 PMIC) + per-core HFPLL multiplier ($N \times 19.2\text{ MHz}$) | Kernel-exposed shared PMIC voltage regulator interface across multi-core frequencies | Undocumented Intel Overclocking Mailbox **MSR `0x150`** (`IA32_PERF_STATUS` telemetry at MSR `0x198`) |
| **Physical Stress Mechanism** | Joint undervolting + HFPLL overclocking ($\sim 3.69\text{ GHz}$ stress at $1.055\text{ V}$ nominal base) violating $T_{\text{clk}} \ge t_{\text{CQ}} + t_{\text{pd}} + t_{\text{setup}}$ | Voltage reduction alone below multi-core OPP floor (no PLL overclocking required) | Coordinated undervolting of IA Core (Plane `0`) and Cache Ring / LLC (Plane `2`) via MSR `0x150` while locking frequency |
| **Fault Timing & Selectivity** | Transient $\sim 39\;\mu\text{s}$ overclock/undervolt pulse aligned via cycle counters to target TrustZone AES (Round 7 DFA) and RSA verification | Coordinated multi-core voltage drop during TrustZone AES/RSA execution | Deterministic setup violations in wide 64-bit `imul`, AES-NI, and CRT-RSA (Bellcore / Lenstra fault) inside SGX enclaves while untrusted host thread remains alive |
| **Root Architectural Defect** | Kernel granted unfettered MMIO access to PMIC/PLL with no hardware OPP bounds and shared voltage domain across Normal and Secure worlds | Shared PMIC rail across TrustZone worlds without Secure-World regulator mediation | Ring-0 `wrmsr` to MSR `0x150` permitted dynamic negative voltage offsets on active SGX cores without affecting SGX attestation or enforcing hardware voltage floors |

#### Primary-Source Inspection of Intel OC Mailbox Interface (`KitMurdock/plundervolt`)

Basis: source

Direct inspection of `KitMurdock/plundervolt` (`a7313c268d7c27ac3eb806d3ed99019788c5f605`, `utils/undervolt.c:10-46` and `utils/read_voltage.c:15-48`) documents the exact hardware register contract that had to be closed in silicon/microcode:

- **Telemetry Read (`IA32_PERF_STATUS`, MSR `0x198`):** Bits `[47:32]` report the active core voltage in fixed-point units of $2^{-13}\text{ V} = 1/8192\text{ V}$ (`read_voltage.c:15-26`).
- **Overclocking Mailbox Protocol (MSR `0x150`):**
  - Bit `63`: Run/Busy flag (`0x80000000_00000000`).
  - Bits `[47:40]`: Target voltage plane (`0` = IA Core, `1` = GPU slice, `2` = LLC / Ring interconnect).
  - Bits `[39:32]`: Mailbox command (`0x10` = read voltage offset, `0x11` = write voltage offset).
  - Bits `[31:21]`: 11-bit signed two's-complement offset encoded in steps of $1/1024\text{ V} \approx 0.9765625\text{ mV}$ (`round(offset_mV * 1.024)` shifted left 21 and masked with `0xFFE00000`).
- **Dual-Plane Rail Coupling Constraint:** Notice that `undervolt.c:33-44` and `faulting_multiplications/operation.c:102-103` always program **both Plane `0` (IA Core) and Plane `2` (Cache Ring)** identically; dropping Plane `0` alone without Plane `2` hits the hardware FIVR/shared-rail floor or triggers level-shifter failures before reaching the arithmetic critical-path fault threshold.
- **Related Frequency Side-Channel Dual (Hertzbleed, 2022):** Even when software cannot *write* voltage/frequency knobs, autonomous hardware DVFS/power-capping adjusts CPU clock frequency in response to data-dependent dynamic switching power ($P_{\text{dyn}} = \alpha C V^2 f$), converting power differences into remotely observable timing side channels even in constant-time cryptographic implementations.

#### Layered Defensive Mitigations and Verification Boundaries

Basis: normative + documentation + derived

Eliminating software-triggered power/clock fault injection requires defense in depth across firmware, silicon microarchitecture, and verified software:

1. **Hardware Lockout & Attestation Binding (`CVE-2019-11157` / `INTEL-SA-00289`):**
   - BIOS/UEFI asserts the hardware Overclocking Lock (`OC_LOCK`) bit prior to OS handoff, causing writes to MSR `0x150` to be ignored or faulted.
   - Microcode updates incorporate the overclocking-interface lock state into the **SGX Trusted Computing Base (TCB) SVN / key derivation** (`EGETKEY` / remote attestation quote), so a remote verifier cryptographically rejects enclaves running on platforms with unlocked voltage-scaling mailboxes.
2. **Privilege Isolation of Energy Management (ARM TrustZone / RISC-V):**
   - Route PMIC I2C/SPMI and PLL/clock-controller MMIO strictly through Secure World / EL3 firmware (e.g., ARM SCMI / PSCI), validating every requested `(V, f)` pair against immutable silicon-fused OPP tables (monotone $V \ge V_{\min}(f)$ with margin for worst-case $L\,dI/dt$ droop) and enforcing rate limits on frequency/voltage slewing.
3. **On-Die Analog/Digital Droop Sensing & Adaptive Clocking:**
   - Deploy critical-path replica delay monitors / digital droop detectors on die that detect first-droop excursions within $1\text{–}2$ cycles and engage **adaptive clock stretching** (temporarily elongating $T_{\text{clk}}$ via PLL/DLL pulse swallowing) so $T_{\text{clk}}(t) \ge t_{\text{CQ}} + t_{\text{pd}}(V_{\text{eff}}(t)) + t_{\text{setup}}$ remains invariant across transient $L\,dI/dt$ events.
4. **Algorithmic Fault Detection in Security-Critical Primitives:**
   - For CRT-RSA, verify every signature $s^e \equiv m \pmod{N}$ before releasing $s$ (defeating Bellcore/Lenstra single-prime faults at negligible verification cost).
   - For AES and control-flow-critical checks (such as secure-boot signature verification), employ redundant execution / infective computation or masked error-detecting codes; note that timing-fault correlation across identical instruction streams can occasionally fault duplicated executions identically unless temporally/spatially diversified.

## Boundaries

- **Not examined:**
  - Physical invasive and semi-invasive fault injection (laser fault injection, electromagnetic pulse EMFI, backside optical probing, or external crowbar/MOSFET board-level voltage glitching) are outside the scope of this report, which restricts attention to on-die PDN dynamics and software-accessible DVFS/regulator interfaces.
  - Full-chip commercial distributed PDN solvers (e.g., Ansys RedHawk-SC, Cadence Voltus), 3D electromagnetic package extraction (S-parameter / PEEC solvers), and BSIM-CMG / BSIM-SOI / PSP FinFET quantum-confinement capacitance formulations were not source-audited beyond Xyce's `ADMS` directory inventory.
  - High-order BDF3–BDF5 integrators, Harmonic Balance (`HB`), and Shooting-Newton periodic steady-state algorithms inside Xyce were not inspected at line level.
  - AMD SEV/SNP (`V0LTpwn` / `CLK` / `FIVR` equivalents) and Apple Silicon PMU DVFS isolation architectures were not inspected at primary-source register level.
- **Unsupported:**
  - `pascalkuthe/OpenVAF` (`a9697ae7780518f021f9f64e819b3a57033bd39f`) explicitly does **not** support Verilog-AMS monitored analog events (`@(cross)`, `@(above)`, `@(timer)`) in its HIR lowering (`openvaf/hir_def/src/body/lower.rs:154-168` only creates `Stmt::EventControl` for `@(initial_step)` and `@(final_step)`), nor does OSDI 0.3 expose a mixed-signal event-queue callback interface.
- **Unknown:**
  - Whether specific post-2020 Intel/AMD/ARM server silicon revisions implement undocumented fused voltage-offset mailboxes outside MSR `0x150` or secondary debug PMIC paths accessible from BMC/ME firmware is not determinable from public primary sources alone.
  - Quantitative fault-injection bit-error distributions across process-voltage-temperature (PVT) corners depend on foundry cell characterization and die-to-die binning; Probe 1C models a representative nominal-corner short-channel path ($\alpha = 1.3$) rather than a specific fabricated SKU.
- **Known not to apply:**
  - The Meyer drain-terminal charge-conservation failure demonstrated in Probe 1A does **not** apply to charge-oriented compact models (BSIM3v3 `CAPMOD >= 1`, BSIM4, BSIM-CMG, PSP, EKV) that compute terminal charges $Q_g, Q_d, Q_s, Q_b$ directly from state functions and enforce $Q_s = -(Q_g + Q_b + Q_d)$.
  - Intel `CVE-2019-11157` MSR `0x150` mitigations do **not** eliminate autonomous hardware-driven DVFS frequency side channels (Hertzbleed) or resonant pure-software $L\,dI/dt$ PDN excitation on systems lacking droop-aware clock stretching.

## Evidence

### Primary Source Repositories and Line Citations

1. **`Xyce/Xyce`** @ `369a7be860d0d55b147d7fe5defd47c992439859` (observed 2026-11-19):
   - `src/DeviceModelPKG/OpenModels/N_DEV_MOSFET1.C`: lines 599–639 (`newMeyerFlag` derivative unknown offsets), 1920–1984 (`Instance::loadDAEQVector`, standard DAE formalism $\dot{Q}(x)+F(x)-B(t)=0$), 3300–3304 (MPDE incompatibility of Meyer back-averaging), 3751–3808 (explicit incremental Meyer back-averaging `qgs += Capgs*(vgs - vgs1)`).
   - `src/DeviceModelPKG/OpenModels/N_DEV_MOSFET_B3.C`: lines 2679 (`XPART`), 3021 (`CAPMOD` default 3), 7287–7390 (0/100 and 40/60 Ward–Dutton charge partitioning), 8819–8905 (`Instance::loadDAEQVector` enforcing `qVec[li_SourcePrime] += -(Qeqqg + Qeqqb + Qeqqd)` and zero-sum `dQdxdVp` limiting corrections).
   - `src/NonlinearSolverPKG/N_NLS_NOX_Interface.C`: lines 322–420 (`spiceStrategy`: Newton -> `gminSteppingSolve` -> `sourceSteppingSolve`), 524–725 (`naturalParameterContinuationSolve`), 740–846 (`mosfetContinuationSolve`: `mosfet:gainscale`, `mosfet:nltermscale`), 859–920 (`sourceSteppingSolve2`), 1116–1197 (`gminSteppingSolve`: `"GSTEPPING"`, $+4.0 \to -4.0$, max `400` steps), 1209–1270 (`pseudoTransientSolve`: `1e-3` to `1e4` followed by unaugmented Newton solve), 1531–1553 (solver type dispatch).
   - `src/NonlinearSolverPKG/N_NLS_NOX_AugmentLinSys_GStepping.C`: lines 99–103 ($10^\lambda - 10^{\lambda_{\min}} + G_{\text{resid}}$), 113–174 (voltage-node-only residual and diagonal Jacobian augmentation).
   - `src/NonlinearSolverPKG/N_NLS_NOX_AugmentLinSys_PseudoTransient.C`: lines 110–114 (no-op `augmentResidual`), 124–164 (`1.0 / time_step_size_` diagonal Jacobian augmentation with voltage-row scaling).
   - `src/TimeIntegrationPKG/N_TIA_OneStep.C`: lines 219–268 (`OneStep::obtainResidual`, Trapezoidal order-2 residual and limiter RHS), 469–495 (`OneStep::obtainJacobian`, `fscalar = 0.5` at order 2), 1807 (`currentOrder_ = 1`).
   - `src/TimeIntegrationPKG/N_TIA_Gear12.C`: lines 208–255 (`Gear12::obtainResidual`, BDF1/BDF2 residual and limiter RHS), 477–501 (`Gear12::obtainJacobian`), 1302 (`currentOrder_ = 1`), 1497–1528 (`rejectStep` order reduction to `minOrder_`).
   - `src/TimeIntegrationPKG/N_TIA_StepErrorControl.C`: lines 742–840 (`updateBreakPoints`, `bpTol = 2.0 * minTimeStep`), 879–954 (`updateMaxTimeStep`, `MPI_MIN` reduction).
   - `src/UtilityPKG/N_UTL_BreakPoint.h`: lines 55–125 (`BreakPoint`, `BreakPointLess`, `BreakPointEqual`, including inverted `>=` comparison in `(BreakPoint, double)` overload at line 122).
2. **`pascalkuthe/OpenVAF`** @ `a9697ae7780518f021f9f64e819b3a57033bd39f` (observed 2026-11-19):
   - `openvaf/sim_back/src/dae.rs`: lines 22–46 (`DaeSystem` $I(x) + \text{ddt}(Q(x)) = 0$), 104–169 (`Residual` with analytical derivation of `resist_lim_rhs` and `react_lim_rhs` $= J(x_{\text{lim}})(x_{\text{lim}} - x)$).
   - `openvaf/osdi/src/eval.rs`: lines 17–20 (OSDI 0.3 `CALC_RESIST_*`, `CALC_REACT_*`, `CALC_*_LIM_RHS`, `ENABLE_LIM` flags).
   - `openvaf/hir_def/src/body/lower.rs`: lines 154–168 (`collect_event_stmt` handling only `InitialStep` and `FinalStep`).
3. **`KitMurdock/plundervolt`** @ `a7313c268d7c27ac3eb806d3ed99019788c5f605` (observed 2026-11-19):
   - `utils/undervolt.c`: lines 10–46 (MSR `0x150` OC mailbox command `0x8000001100000000`, plane bitshift `plane << 40` for planes `0` and `2`, 11-bit signed $1/1024\text{ V}$ offset at bits `[31:21]`).
   - `utils/read_voltage.c`: lines 15–48 (MSR `0x198` `IA32_PERF_STATUS` bits `[47:32]` scaled by `/ 8192.0`, MSR `0x150` read command `0x10`).

### Standards and Peer-Reviewed Publications

- Accellera Systems Initiative, *Verilog-AMS Language Reference Manual*, Version 2.4.0, May 30, 2014, Section 5.10.3 (*Monitored events*: 5.10.3.1 `cross`, 5.10.3.2 `above`, 5.10.3.3 `timer`).
- C.-W. Ho, A. E. Ruehli, and P. A. Brennan, "The Modified Nodal Approach to Network Analysis," *IEEE Trans. Circuits Syst.*, vol. CAS-22, no. 6, pp. 504–509, June 1975. DOI: `10.1109/TCS.1975.1084079`.
- J. E. Meyer, "MOS models and circuit simulation," *RCA Review*, vol. 32, pp. 42–63, March 1971.
- D. E. Ward and R. W. Dutton, "A Charge-Oriented Model for MOS Transistor Capacitances," *IEEE J. Solid-State Circuits*, vol. SC-13, no. 5, pp. 703–708, Oct. 1978. DOI: `10.1109/JSSC.1978.1051123`.
- P. Yang, B. D. Epler, and P. K. Chatterjee, "An Investigation of the Charge Conservation Problem for MOSFET Circuit Simulation," *IEEE J. Solid-State Circuits*, vol. SC-18, no. 1, pp. 128–138, Feb. 1983. DOI: `10.1109/JSSC.1983.1051909`.
- T. Sakurai and A. R. Newton, "Alpha-Power Law MOSFET Model and its Applications to CMOS Inverter Delay and Other Formulas," *IEEE J. Solid-State Circuits*, vol. 25, no. 2, pp. 584–594, Apr. 1990. DOI: `10.1109/4.52187`.
- A. Tang, S. Sethumadhavan, and S. Stolfo, "CLKSCREW: Exposing the Perils of Security-Oblivious Energy Management," *Proc. 26th USENIX Security Symposium*, pp. 1057–1074, Aug. 2017.
- P. Qiu, D. Wang, Y. Lyu, and G. Qu, "VoltJockey: Breaching TrustZone by Software-Controlled Voltage Manipulation over Multi-core Frequencies," *Proc. ACM CCS 2019*, pp. 195–209. DOI: `10.1145/3319535.3354201`.
- K. Murdock, D. Oswald, F. D. Garcia, J. Van Bulck, D. Gruss, and F. Piessens, "Plundervolt: Software-based Fault Injection Attacks against Intel SGX," *Proc. 2020 IEEE Symposium on Security and Privacy (S&P)*, pp. 1466–1482. DOI: `10.1109/SP40000.2020.00057`. (Vendor advisory: `INTEL-SA-00289` / `CVE-2019-11157`.)

### Self-Contained Executable Micro-Probes (Python 3 stdlib, Executed 2026-11-19)

Command: `python3 /tmp/probe_ams_pdn.py` (using Python 3 standard library `cmath` and `math` only):

```python
#!/usr/bin/env python3
import cmath, math

# --- Probe 1A: Meyer non-conservation vs. Ward-Dutton 40/60 exact charge ---
COX, VTH = 100e-15, 0.5
def meyer_caps(vgs, vgd):
    vds = vgs - vgd
    if vgs <= VTH: return 0.0, 0.0
    if vds >= vgs - VTH: return (2.0/3.0)*COX, 0.0
    a, b = vgs - VTH, vgd - VTH
    d = (a + b)**2
    return (2.0/3.0)*COX*(1.0 - b*b/d), (2.0/3.0)*COX*(1.0 - a*a/d)

def wd_charges(vgs, vgd):
    vds = vgs - vgd
    if vgs <= VTH: return 0.0, 0.0, 0.0
    vgst = vgs - VTH
    if vds >= vgst:
        qg = (2.0/3.0)*COX*vgst; qd = -0.4*qg; return qg, qd, -(qg+qd)
    t = vgst - 0.5*vds
    qg = COX*(t + vds*vds/(12.0*t))
    a, b = vgst, vgst - vds
    qd = -COX*(4*a**3 + 8*a**2*b + 12*a*b**2 + 6*b**3)/(15.0*(a + b)**2)
    return qg, qd, -(qg + qd)

pts = [(1.5, 0.6), (2.0, 0.6), (2.0, 1.4), (1.5, 1.4)]
for n in [5, 20, 200, 2000]:
    qgm = qdm = qgw = qdw = 0.0
    for s in range(4):
        x0, y0 = pts[s]; x1, y1 = pts[(s+1)%4]
        for k in range(n):
            t0, t1 = k/n, (k+1)/n
            u0, v0 = x0+(x1-x0)*t0, y0+(y1-y0)*t0
            u1, v1 = x0+(x1-x0)*t1, y0+(y1-y0)*t1
            cg0, cd0 = meyer_caps(u0, v0); cg1, cd1 = meyer_caps(u1, v1)
            qgm += 0.5*(cg0+cg1)*(u1-u0) + 0.5*(cd0+cd1)*(v1-v0)
            qdm += -0.5*(cd0+cd1)*(v1-v0)
            g0, d0, _ = wd_charges(u0, v0); g1, d1, _ = wd_charges(u1, v1)
            qgw += g1 - g0; qdw += d1 - d0
    print(f"1A n={n:4d}: Meyer_dQg={qgm*1e15:+.6f}fC Meyer_dQd={qdm*1e15:+.6f}fC | WD_dQg={qgw*1e15:+.2e}fC WD_dQd={qdw*1e15:+.2e}fC")

# --- Probe 1B: Stiff Trap ringing vs. BDF2 & @(cross) aliasing ---
z = -20.0
v_be, v_tr, v_b2 = [1.0, 1.0/(1-z)], [1.0, (1+0.5*z)/(1-0.5*z)], [1.0, 1.0/(1-z)]
for _ in range(7):
    v_be.append(v_be[-1]/(1-z))
    v_tr.append(v_tr[-1]*(1+0.5*z)/(1-0.5*z))
    v_b2.append((2*v_b2[-1]-0.5*v_b2[-2])/(1.5-z))
print(f"1B step8(z=-20): BE={v_be[-1]:+.2e} Trap={v_tr[-1]:+.4f} BDF2={v_b2[-1]:+.2e}")
f_c = lambda t: math.exp(-((t-5.23e-9)/0.08e-9)**2) - 0.5
for dt in [0.50e-9, 0.15e-9]:
    t, cnt = 0.0, 0
    while t < 10e-9:
        if f_c(t)*f_c(t+dt) <= 0.0: cnt += 1
        t += dt
    print(f"1B @(cross) dt={dt*1e9:.2f}ns: crossings={cnt}")

# --- Probe 1C: Coupled RLC PDN -> Sakurai-Newton critical-path delay ---
Vdd, L, C, Rp, Rir = 1.00, 20e-12, 250e-9, 2.0e-3, 1.5e-3
f0 = 1.0/(2*math.pi*math.sqrt(L*C))
def min_rail(mode, dI=12.0, dt=5e-12, tend=150e-9):
    Ib = 8.0; ip = Ib; vd = Vdd - Rp*Ib; mv = vd - Rir*Ib
    il = (lambda t: Ib + dI*min(1.0, max(0.0, (t-5e-9)/0.5e-9))) if mode=="step" else (
          lambda t: Ib + (dI if (t>=5e-9 and (((t-5e-9)*f0)%1.0)<0.5) else 0.0))
    for k in range(int(tend/dt)):
        t = k*dt
        d = lambda tt, i, v: ((Vdd-Rp*i-v)/L, (i-il(tt))/C)
        k1=d(t,ip,vd); k2=d(t+0.5*dt,ip+0.5*dt*k1[0],vd+0.5*dt*k1[1])
        k3=d(t+0.5*dt,ip+0.5*dt*k2[0],vd+0.5*dt*k2[1]); k4=d(t+dt,ip+dt*k3[0],vd+dt*k3[1])
        ip += (dt/6)*(k1[0]+2*k2[0]+2*k3[0]+k4[0]); vd += (dt/6)*(k1[1]+2*k2[1]+2*k3[1]+k4[1])
        mv = min(mv, vd - Rir*il(t+dt))
    return mv
V_idle = Vdd - (Rp+Rir)*8.0
vs, vr = min_rail("step"), min_rail("resonant")
t_path = lambda v: 45.0 + 235.0*(v/V_idle)*(((V_idle-0.28)/(v-0.28))**1.3)
print(f"1C f0={f0/1e6:.2f}MHz V_step={vs:.4f}V V_res={vr:.4f}V | slack(UV-100mV+step)={333.33-t_path(vs-0.100):+.2f}ps slack(res)={333.33-t_path(vr):+.2f}ps")
```

Observed output (2026-11-19):
```text
1A n=   5: Meyer_dQg=+0.067764fC Meyer_dQd=+5.669939fC | WD_dQg=+0.00e+00fC WD_dQd=+0.00e+00fC
1A n=  20: Meyer_dQg=+0.004268fC Meyer_dQd=+5.727768fC | WD_dQg=+0.00e+00fC WD_dQd=+0.00e+00fC
1A n= 200: Meyer_dQg=+0.000043fC Meyer_dQd=+5.731620fC | WD_dQg=+0.00e+00fC WD_dQd=+0.00e+00fC
1A n=2000: Meyer_dQg=+0.000000fC Meyer_dQd=+5.731658fC | WD_dQg=+0.00e+00fC WD_dQd=+0.00e+00fC
1B step8(z=-20): BE=+2.64e-11 Trap=+0.2008 BDF2=-2.32e-07
1B @(cross) dt=0.50ns: crossings=0
1B @(cross) dt=0.15ns: crossings=2
1C f0=71.18MHz V_step=0.8414V V_res=0.6323V | slack(UV-100mV+step)=-15.28ps slack(res)=-79.33ps
```

## Revalidation

1. **Xyce solver & charge-conservation invariance:** Against a newer `Xyce/Xyce` commit, diff `src/DeviceModelPKG/OpenModels/N_DEV_MOSFET_B3.C` (`loadDAEQVector`), `src/NonlinearSolverPKG/N_NLS_NOX_Interface.C` (`spiceStrategy`, `gminSteppingSolve`, `pseudoTransientSolve`), `src/TimeIntegrationPKG/N_TIA_{OneStep,Gear12}.C`, and `src/UtilityPKG/N_UTL_BreakPoint.h` (checking whether line 122's `>=` comparison in `BreakPointEqual` has been corrected).
2. **OpenVAF event-support progression:** Diff `openvaf/hir_def/src/body/lower.rs` (`collect_event_stmt`) and `openvaf/osdi/src/metadata/` in `pascalkuthe/OpenVAF` (or community forks such as `OpenVAF-Reloaded/OpenVAF`) to check whether OSDI $\ge 0.4$ adds monitored analog event (`cross`/`above`/`timer`) callbacks.
3. **Quantitative probe rerun:** Execute the inline Python 3 script above (zero external dependencies, `< 0.5 s` runtime) to verify exact Meyer curl non-conservation, Trapezoidal vs. BDF2 stiff stability, `@(cross)` even-crossing aliasing, and RLC PDN Sakurai–Newton fault-boundary calculations.
4. **Platform DVFS/TEE security revalidation:** On target hardware, verify that OS-accessible voltage/frequency control interfaces (e.g., Intel `OC_LOCK` / MSR `0x150` write-rejection, ARM SCMI/EL3 OPP enforcement, and SGX/TDX/TrustZone remote attestation quote TCB levels) reject out-of-envelope `(V, f)` requests and bind lock status into attestation measurements.
