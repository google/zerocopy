<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Historical Verification, Compiler, and Specification Failures Across Cyber-Physical, Aerospace, EDA/VLSI, Quantum, and Analog/Photonic Systems

## Summary

Across cyber-physical systems (CPS), robotics, aerospace flight control,
industrial programmable logic controllers (PLCs), Electronic Design Automation
(EDA) and VLSI synthesis, quantum circuit compilation, and analog/photonic
metamaterial modeling, formal verification and compilation pipelines have
repeatedly suffered four structural classes of failure:

1. **Kernel soundness bugs, solver floating-point escapes, and compiler
   miscompilations:** Taclet/rule side-condition bugs and computer-algebra
   division-by-zero escapes in `KeYmaera 3` (Quesel et al., STTT 2016; Fulton
   et al., CADE 2015), unverified `IEEE-754` simplex pivoting in `SpaceEx`
   (`GLPK` backend; Frehse et al., CAV 2011), 31 simulator/synthesizer
   mistranslation bugs (`25` CVEs) across `Yosys`, `Verilator`, `CXXRTL`, and
   `Icarus Verilog` exposed by `TransFuzz` (`MiRTL` confused-deputy gadgets;
   Solt & Razavi, USENIX Security 2024), behavioral Verilog synthesis
   miscompilations in `Yosys` and `Vivado` exposed by `Verismith` (Herklotz et
   al., FPGA 2020), High-Level Synthesis (HLS) schedule/aliasing
   miscompilations in commercial C-to-RTL tools motivating `VeriCert` (Herklotz
   et al., OOPSLA 2021), and quantum pass miscompilations in `Qiskit`, `TKET`,
   `Cirq`, and `PyZX` exposed by `QDiff` (Wang et al., ASE 2021) and `MorphQ`
   (Paltenghi & Pradel, ICSE 2022).
2. **Vacuity bugs, contradictory premises, and "proved the wrong specification"
   postmortems:** Finite-time blowup differential ghosts ($y' = y^2$) and empty
   evolution domains $[x' = f(x) \,\&\, H]\phi$ in differential dynamic logic
   ($\text{dL}$) that vacuously discharge safety after the trajectory ceases to
   exist; the "Freezing Robot Problem" (Trautman & Krause, IROS 2010) and empty
   Control Barrier Function (CBF) quadratic programs (Ames et al., TAC 2017)
   that satisfy collision-freedom by commanding zero velocity forever or
   stepping to an infeasible `.stuck` state; Ariane 5 Flight 501's reuse of
   Ariane 4's horizontal-velocity precondition on an unguarded 64-bit float to
   16-bit integer conversion (Lions Report, 1996); Mars Climate Orbiter's
   `lbf·s` vs. `N·s` unit-codec mismatch across `SM_FORCES` (NASA MCO MIB,
   1999); Mars Polar Lander's unreset Hall-effect leg-deployment transient
   (JPL D-18709, 2000); Boeing 737 MAX MCAS's single-sensor Angle-of-Attack
   (AoA) vulnerability and authority escalation (NTSB ASR-19-01, 2019); Patriot
   missile's 24-bit fixed-point `0.1`-second drift (GAO/IMTEC-92-26, 1992);
   Intel Pentium `FDIV`'s omitted SRT radix-4 lookup-table boundary entries
   (Pratt, 1995; Harrison, FMSD 2000); RTL-to-gate `X`-optimism escapes (Turpin,
   SNUG 2003); and correlated cosmic-ray phonon bursts violating surface-code
   independent-noise assumptions (Wilen et al., Nature 2021; McEwen et al.,
   Nature Physics 2022).
3. **Proof-maintenance collapses, Taylor-model wrapping effects, and real-time
   usability walls:** Exponential dependency growth and parallelotope/zonotope
   wrapping effects in `Flow*` (Chen et al., CAV 2013) and `CORA` on stiff or
   long-horizon nonlinear ODEs; real quantifier elimination (CAD) doubly
   exponential blowup $O(d^{2^n})$ stalling interactive CPS proofs; and the
   quantum syndrome decoder backlog catastrophe (Terhal, Rev. Mod. Phys. 2015)
   when decoder Worst-Case Execution Time (WCET) exceeds the syndrome
   measurement cycle.
4. **Core formalism expressiveness boundaries:** Continuous-time CBFs and ODE
   proofs (`VeriPhy`, Bohrer et al., PLDI 2018) that cannot directly express
   inter-sample zero-order-hold (ZOH) drift, fixed-point quantization, or
   multi-rate inner ADMM solver loops; structural 2-FF Clock-Domain Crossing
   (CDC) checkers that cannot express multi-bit reconvergence correlations;
   2-state booleans that cannot represent 4-valued `{0, 1, X, Z}` hardware wire
   states or analog threshold-window `[V_IL, V_IH]` forbidden zones; and
   independent-channel models that omit thermo-optic crosstalk $K_{\text{thermal}}$
   or non-50:50 beam-splitter coverage holes in Mach-Zehnder Interferometer
   (MZI) meshes (Bandyopadhyay et al., Optica 2021).

Every failure class in this corpus maps directly onto—and validates the
design necessity of—Anneal's four orthogonal `trusted/` verification
primitives:

- **`Language SemObs` & `Partial` (`defined` vs. `Partial.ub`) +
  `BehaviorCodec L₁ L₂` (`decodeOut : L₂.Out → Option L₁.Out`,
  `decodeOut_encodeOut`, `encodeOut_of_decodeOut`, `obs_decodeOut`):** Prevents
  representation-mismatch, unit-scaling, `X`-optimism, diagnostic-data-as-pose,
  and global-to-relative-phase escalation bugs by enforcing fail-closed partial
  outcome decoding (`decodeOut = none` maps to `False`) and observable trace
  preservation (`obs_decodeOut`).
- **`ProductiveOn` & `InhabitedPre` (`InhabitedDemonic` / `TotalStep`):**
  Prevents vacuous safety proofs caused by empty evolution domains, finite-time
  ODE ghost blowup, unverified Ariane 4 trajectory preconditions, freezing
  robots, infeasible CBF-QPs, probability-zero quantum post-selection,
  non-50:50 MZI extinction holes, and zero-power HIFU phased arrays.
- **`SmallStepMachine` with `EventualBehaviorOf` &
  `StepResult.externalCall`:** Decouples multi-rate execution scales (inner
  MPC/ADMM solver ticks, PLC scan cycles, pipelined RTL stall cycles, variable
  magic-state distillation rounds) from single specification steps without
  `Classical.choice` or coinduction, while `StepResult.externalCall` enforces
  pre-call launch invariants (`boundaryInv`) and demonic environment framing
  across ADC/DAC plant boundaries, CDC synchronizers, and mid-circuit quantum
  measurements.
- **Positive Per-Obligation Waiver Envelopes (`VerificationResult policy waived
  obligations`):** Isolates empirical physical, aerodynamic, foundry PDK/`.lib`,
  BSIM transistor, and depolarizing noise assumptions as positive audited waiver
  tags rather than negative implication antecedents (`hTcb → ...`), preventing
  any discrepancy between an idealized physics model and reality from triggering
  logical explosion (`False.elim`) across the crate's mathematical proofs.

## Applicability

This report applies to the design and review of Anneal's trusted refinement core
(`trusted/lean/Trusted/Refinement.lean` and
`trusted/lean/Trusted/StepResult.lean` across
`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`,
`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`,
`joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`, and the hardening
corpus `joshlf/anneal@df55c524a051d59e7dd35564f282b30d29133392`) when evaluating
whether those four primitives generalize beyond Rust/x86-64 software to
physical, cyber-physical, hardware EDA, quantum, and analog/photonic domains.

The seven subjects in `REPORT.json` are related as follows: Subject 1 is the
Anneal verification architecture under evaluation; Subjects 2 through 7 are the
primary historical systems, toolchains, and official mishap investigation
records whose documented failures serve as empirical stress tests for Subject
1's primitives. Claims about specific historical incidents and tool bugs are
scoped to the exact versions, commits, DOIs, and official investigation reports
cited in `## Findings` and `## Evidence`.

## Findings

### 1. CPS, Hybrid Automata, and Reachability Verifier Failures

`Basis: normative + documentation + source + derived`

#### 1.1 `KeYmaera 3` vs. `KeYmaera X`: Taclet Soundness Escapes, Computer-Algebra Singularities, and Differential Ghost Blowup

Differential dynamic logic ($\text{dL}$) verifies hybrid programs combining
discrete assignments, tests `?H`, nondeterministic repetitions $\alpha^*$, and
continuous ODE evolutions $x' = f(x) \,\&\, H(x)$ (where the system must remain
within evolution domain constraint $H(x)$). Across the transition from the
monolithic taclet prover `KeYmaera 3` (~66,000+ lines of Java/Scala; Platzer &
Quesel, IJCAR 2008) to the microkernel prover `KeYmaera X` (~1,700–2,000 LOC
core; Fulton, Mitsch, Quesel, Völp, & Platzer, CADE 2015,
`doi:10.1007/978-3-319-21401-6_36`) and its Coq/Isabelle formalization (Bohrer,
Rahli, Vukotic, Völp, & Platzer, CPP 2017, `doi:10.1145/3018610.3018616`), four
concrete failure modes emerged:

1. **Bound-Variable Capture and Primed-Variable Substitution Bugs:** In
   `KeYmaera 3`, soundness depended on dozens of hand-coded sequent calculus
   taclets with ad-hoc free-variable (`FV`) and bound-variable (`BV`) checks.
   Subtle bugs in bound-variable renaming and skolemization allowed variable
   capture across differential operators ($x'$), motivating `KeYmaera X`'s
   replacement of taclets with Church-style Uniform Substitution (Platzer, JAR
   2017, `doi:10.1007/s10817-016-9385-1`). Even within `KeYmaera X` and its
   CPP 2017 formalization, checking admissibility of uniform substitutions on
   ODE systems required delicate side conditions where primed differential
   symbols $x'$ and post-state variables in assignment axioms $[x := \theta]\phi$
   intersected with $\text{FV}(\phi)$; an early side-condition omission in bound
   renaming was caught and patched during mechanized cross-verification.
2. **Differential Ghost (`DG` / `DA`) Finite-Time Blowup Unsoundness:** The
   Differential Ghost rule introduces an auxiliary variable $y$ governed by a
   new ODE $y' = g(x, y)$ to prove invariants of $x' = f(x)$ (such as proving
   $x > 0$ is invariant under $x' = -x$ by introducing $y' = \frac{1}{2}y$ with
   $x y^2 = 1$). If `DG` permits an arbitrary polynomial ghost ODE such as
   $y' = y^2$ with $y(0) = 1$, the ghost trajectory $y(t) = \frac{1}{1 - t}$
   diverges to $+\infty$ at finite time $t = 1$. Because the semantics of the
   combined system $[x' = f(x), y' = y^2 \,\&\, H]\phi$ quantifies only over
   time intervals $[0, \tau]$ on which *both* $x(t)$ and $y(t)$ exist in
   $\mathbb{R}$, adding $y' = y^2$ silently truncates all system trajectories at
   $t < 1$, allowing the prover to unsoundly prove safety properties that are
   violated at $t \ge 1$! Soundness requires restricting `DG` to ghosts that are
   affinely linear in $y$ ($y' = a(x)y + b(x)$), guaranteeing global solution
   existence on the full time interval of $x(t)$ by Picard-Lindelöf.
3. **External CAS (`Mathematica` / `Z3`) Symbolic ODE Integration Singularities
   and Branch Cuts:** Early versions of `KeYmaera 3` trusted symbolic ODE
   solutions returned by `Mathematica`'s `DSolve` and algebraic simplifications
   without re-checking domain-of-definition side conditions. `DSolve` routinely
   divides by symbolic parameters (assuming $a \ne 0$), drops singular equilibrium
   solutions, or applies complex logarithm/square-root branch-cut identities
   that fail over $\mathbb{R}$, producing unsound proofs until `KeYmaera X`
   replaced trusted external ODE solving with syntactic Differential Invariant
   (`dI`) and Darboux (`dbx`) proof certificates checked inside the kernel.
4. **Evolution-Domain Constraint (`& H`) Vacuity ("Time-Stop Cheating"):** In
   $\text{dL}$, the evolution domain constraint $H(x)$ in $[x' = f(x) \,\&\, H]\phi$
   is an *assumption* (similar to a `while` guard), not an obligation: the
   continuous semantics simply stops evolving at the instant $x(t)$ leaves $H$.
   A pervasive modeling failure documented in CPS courses and industrial case
   studies (Platzer, *Logical Foundations of Cyber-Physical Systems*, 2018)
   occurs when an engineer models a discrete controller with a guard or places a
   safety property inside `& H` so that trajectories entering an unsafe physical
   state cannot continue evolving in the model—rendering $[x'=f(x)\,\&\,H]\phi$
   vacuously true while the physical plant crashes!
5. **`VeriPhy` Continuous-to-Discrete Actuator Saturation & Inter-Sample Gap:**
   `VeriPhy` (Bohrer, Tan, Jeannin, Mitsch, & Platzer, PLDI 2018,
   `doi:10.1145/3192366.3192406`) compiles verified `KeYmaera X` models to
   verified CakeML controller monitors. However, when a `KeYmaera X` model
   idealizes actuation as instantaneous at sample times $t_k$ or omits fixed-point
   sensor quantization and physical actuator slew limits, the runtime monitor
   repeatedly triggers fallback abort actions in physical rover tests whenever
   unmodeled inter-sample drift violates the idealized continuous monitor guard.

#### 1.2 `Flow*`, `SpaceEx`, `CORA`, and `dReal`: Floating-Point LP Unsoundness, Wrapping-Effect Explosion, and $\delta$-Satisfiability Falsifications

Hybrid reachability solvers compute over-approximations of continuous trajectory
tubes (flowpipes) across discrete mode switches. Annual `ARCH-COMP` evaluations
(Althoff et al. / Geretti et al., EPiC Series in Computing,
`doi:10.29007/5791`) and tool postmortems have documented four recurring failure
modes:

1. **`SpaceEx` Unverified IEEE-754 Support-Function and `GLPK` Simplex Pivoting:**
   `SpaceEx` (Frehse et al., CAV 2011, `doi:10.1007/978-3-642-22110-1_30`)
   represents reachable sets of linear hybrid automata using template polyhedra
   and support functions evaluated via floating-point linear programming (`GLPK`
   simplex solver) and matrix exponentials $e^{A\delta}$. Because `GLPK` uses
   standard `double` (`IEEE-754` `binary64`) arithmetic with heuristic pivot
   tolerances ($\approx 10^{-7}$), ill-conditioned grazing transitions against a
   switching guard hyperplane $c^T x = d$ can under-approximate the support
   function or miss a mode transition entirely, causing `SpaceEx` to report
   `SAFE` on trajectories that actually cross the unsafe boundary in exact
   rational arithmetic.
2. **`Flow*` and `CORA` Taylor-Model Wrapping Effect and Picard Iteration Stalls:**
   `Flow*` (Chen, Ábrahám, & Sankaranarayanan, CAV 2013,
   `doi:10.1007/978-3-642-39799-8_18`) encloses nonlinear ODE flows using
   Taylor polynomials $p(x_0, t)$ plus an interval remainder box $I = [-\epsilon,
   +\epsilon]^n$ computed via `MPFR` multiple-precision intervals. When a
   nonlinear flow rotates or shears in state space (e.g., Lotka-Volterra, Van der
   Pol, or coupled 6-DoF rigid-body attitude kinematics) or crosses a transverse
   switching guard where multiple flowpipe segments are aggregated, enclosing a
   rotated polynomial tube inside an axis-aligned or preconditioned interval box
   induces the **wrapping effect**: the interval remainder $I$ grows
   exponentially at each step until the Picard-Lindelöf contraction operator
   fails to contract within the maximum remainder bound, aborting verification
   with `Cannot find a valid remainder`. Conversely, non-verified settings in
   `CORA` (Althoff, ARCH 2015) that truncate high-order Lagrangian remainder
   terms for scalability can lose conservative enclosure on stiff nonlinear terms.
3. **`dReal` $\delta$-Completeness Misinterpretation ($\delta$-SAT vs. UNSAT
   Boundary Escapes):** `dReal` (Gao, Kong, & Clarke, CADE 2013,
   `doi:10.1007/978-3-642-38574-2_14`) solves nonlinear real formulas over
   transcendental functions ($\sin, \cos, \exp$) using interval constraint
   propagation (`realpaver` / `ibex`). While `UNSAT` is sound (Provided `MPFR`
   outward rounding is respected everywhere), `dReal` can never prove a tight
   algebraic equality invariant $V(x) = 0$ or a zero-margin barrier inequality
   $\dot{h}(x) \ge 0$ at an equilibrium point where $\dot{h}(0) = 0$: the
   negated verification condition $\exists x,\, \dot{h}(x) < 0$ is trivially
   $\delta$-satisfiable within any $\delta > 0$ ball around the equilibrium
   ($|\dot{h}(0)| = 0 \le \delta$), causing `dReal` to return spurious
   $\delta$-counterexamples on every tight Lyapunov or barrier certificate unless
   the user strictly inflates the barrier margin by $> \delta$.

#### 1.3 Architectural Lessons for Anneal's 4 Primitives (CPS & Hybrid Systems)

- **`ProductiveOn` & `InhabitedPre` eliminate Differential Ghost blowup and `& H`
  time-stop vacuity:** In Anneal, a continuous or hybrid plant is a
  `SmallStepMachine` packaged via `EventualBehaviorOf`. Because `ReachesPrefix`
  maps any state with no outgoing transition (`noStep`) or an empty choice set
  (`emptyChoice`) to `.stuck` (`isSafe = False`), an evolution domain `& H` or a
  finite-time blowup ghost $y' = y^2$ that ceases to have a valid continuation
  at $t = 1$ steps immediately to `.stuck`, refuting `WellFormedOn pre` and
  `ProductiveOn pre prog`! You cannot prove safety in Anneal by truncating time.
- **`BehaviorCodec` (`decodeOut = none`) + Certifying Checkers in `theory/`
  eliminate CAS and floating-point solver trust:** Rather than trusting
  `Mathematica`, `GLPK`, or floating-point SDP solvers inside `trusted/`,
  untethered numerical tools synthesize candidate Taylor models or rational
  $LDL^T$ Sum-of-Squares (SOS) certificates outside the TCB, and a verified Lean
  checker proves `Abstracts L_cbf L_plant codec v s` inside `theory/`. Any
  floating-point `NaN`, interval overflow, or remainder contraction failure
  evaluates `decodeOut` to `none` (`False`).
- **`EventualBehaviorOf` + `StepResult.externalCall` bridge continuous ODEs and
  discrete ZOH sampling:** `StepResult.externalCall` at each ADC/DAC sample tick
  enforces `boundaryInv` (checking that the computed digital control $u_k$ lies
  within physical actuator saturation limits and fixed-point error bounds)
  before the continuous plant demonically evolves over inter-sample disturbances
  $d(t) \in \mathcal{D}$ for $\Delta t$ seconds.

---

### 2. Robotics, Avionics, Spacecraft, and Industrial Control Postmortems

`Basis: normative + documentation + source + derived`

#### 2.1 Ariane 5 Flight 501 (June 4, 1996): Unchecked Precondition Reuse, Unhandled Overflow, and Diagnostic-as-Flight-Data Codec Failure

Thirty-seven seconds after liftoff on June 4, 1996, the maiden flight of the
Ariane 5 launcher (`V88` / Flight 501) veered sharply off course and
self-destructed (`ESA/CNES Inquiry Board Report`, chaired by Jacques-Louis
Lions, July 19, 1996). The technical root cause comprised three compounding
verification and interface failures in the Inertial Reference System (`SRI 1`
and `SRI 2`, running identical Ada software reused from Ariane 4):

1. **Violated Environmental Precondition (`InhabitedPre` / `WellFormedOn pre`
   mismatch):** The SRI horizontal alignment task continued running for 40
   seconds after liftoff (a hold-countdown requirement specific to Ariane 4's
   ground restart sequence, serving zero functional purpose on Ariane 5 after
   liftoff). Ariane 5's steeper initial trajectory produced a horizontal velocity
   bias (`BH`, *Bias Horizontal*) more than five times higher than Ariane 4's
   maximum envelope.
2. **Selective Omission of Overflow Protection Based on Unverified Physics
   Assumptions:** During Ariane 4 design, engineers analyzed seven Ada numeric
   variables converted from 64-bit floating-point to 16-bit signed integer
   (`-32,768` to `+32,767`). To keep worst-case SRI processor load below 80%,
   explicit Ada exception guards were placed on four variables, while three—including
   `BH`—were left unprotected on the informal physical assumption that `BH`
   could never exceed `16#7FFF#` (`32,767`). At $T + 36.7\text{ s}$, `BH`
   exceeded `32,767`, raising an unhandled Ada `Operand_Error` exception that
   halted both the active (`SRI 2`) and hot-standby (`SRI 1`) units within 72
   milliseconds.
3. **Fail-Open `BehaviorCodec` at the OBC Databus:** Upon halting, `SRI 2`
   transmitted a post-mortem diagnostic memory dump (`16-bit` error bit pattern)
   over the `1553` flight databus on the exact message channel reserved for
   attitude angles. The On-Board Computer (`OBC`) lacked a disjoint validity tag
   (`decodeOut = none`) and decoded the diagnostic bit pattern as an extreme
   $> 20^\circ$ nozzle-gimbal deflection command, causing aerodynamic structural
   breakup.

#### 2.2 Mars Climate Orbiter (September 23, 1999) and Mars Polar Lander (December 3, 1999): Unit-Codec Mismatch and Unreset Sensor-Transient Latch

NASA lost two Mars spacecraft in 71 days due to boundary specification mismatches
documented in primary mishap board reports:

1. **Mars Climate Orbiter (`NASA MCO Mishap Investigation Board Phase I Report`,
   Arthur Stephenson et al., November 10, 1999):** During the 9-month cruise to
   Mars, periodic Angular Momentum Desaturation (`AMD`) thruster firings dumped
   reaction-wheel momentum. The Ground Software Interface Specification (`SIS`)
   mandated that the `SM_FORCES` ("Small Forces") file produced by Lockheed
   Martin's spacecraft operations team report total impulse in SI units of
   **Newton-seconds ($\text{N}\cdot\text{s}$)** for consumption by JPL's orbit
   determination software. Instead, `SM_FORCES` computed thrust using the
   imperial thruster performance equation in **pound-force seconds
   ($\text{lbf}\cdot\text{s}$)** without multiplying by the conversion factor
   $4.4482216152605\text{ N/lbf}$. Because the file transferred bare floating-point
   numbers with no unit/schema witness in the codec, navigation underestimated
   AMD delta-$v$ by $4.45\times$, placing the periapsis at $57\text{ km}$
   altitude instead of the planned $226\text{ km}$ and destroying the orbiter in
   the Martian atmosphere.
2. **Mars Polar Lander (`JPL Special Review Board Report`, Thomas Young et al.,
   `JPL D-18709`, March 28, 2000):** Each of MPL's three landing legs carried a
   Hall-effect magnetic touchdown sensor. Mechanical shock during leg deployment
   at $\sim 1{,}500\text{ m}$ altitude was known to generate spurious transient
   contact signals lasting several milliseconds. The flight software polled the
   touchdown sensors at $100\text{ Hz}$ ($10\text{ ms}$ period) and required two
   consecutive `TRUE` samples ($20\text{ ms}$) to filter noise, storing the
   result in a persistent software latch variable. Crucially, the leg-deployment
   transient lasted $> 20\text{ ms}$, setting the touchdown latch while the
   spacecraft was still at $1{,}500\text{ m}$—and **when the descent-engine
   shutdown monitor was enabled at $40\text{ m}$ altitude, it failed to clear or
   re-verify the stale pre-existing latch**, immediately cutting off the descent
   engines at $40\text{ m}$ above the surface.

#### 2.3 Boeing 737 MAX MCAS (2018–2019) and Patriot Missile Dhahran (February 25, 1991): Single-Sensor Authority Escape and 24-Bit Fixed-Point Drift

1. **Boeing 737 MAX Maneuvering Characteristics Augmentation System (`NTSB
   Safety Recommendation Report ASR-19-01`, September 19, 2019; `KNKT.18.10.35.04`,
   October 25, 2019):** On Lion Air Flight 610 (October 29, 2018) and Ethiopian
   Airlines Flight 302 (March 10, 2019), a single miscalibrated Angle-of-Attack
   (`AoA`) vane fed false high-AoA readings to the active Flight Control
   Computer (`FCC`). Although the aircraft possessed two independent `AoA` vanes,
   MCAS read only the single on-side sensor without a cross-channel comparator
   (`AoA Disagree` was not wired as an inhibit). Furthermore, during low-speed
   flight testing, Boeing increased MCAS horizontal-stabilizer authority fourfold
   from $0.6^\circ$ (the value analyzed in the initial System Safety Assessment /
   `FHA`) to $2.5^\circ$ per activation cycle, and allowed MCAS to re-trigger
   every $5\text{ seconds}$ after manual electric trim cutout—quickly reaching
   full $4.6^\circ$ nose-down stabilizer jackscrew authority and exceeding
   elevator control authority.
2. **Patriot Missile Battery at Dhahran (`GAO Report GAO/IMTEC-92-26`, February
   4, 1992):** On February 25, 1991, a Patriot air-defense battery in Dhahran,
   Saudi Arabia failed to track an incoming Iraqi Al-Hussein Scud missile,
   resulting in 28 fatalities. The Patriot Weapons Control Computer tracked time
   in tenths of a second ($0.1\text{ s}$) as an integer counter, and converted
   that counter to floating-point seconds by multiplying by the 24-bit fixed-point
   binary approximation of $1/10$:
   $$0.1_{10} = 0.0001100110011001100110011001100\dots_2 \approx \text{0x00019999} \times 2^{-20}$$
   The 24-bit truncation underestimated $0.1\text{ s}$ by $\frac{1}{10} -
   \frac{209{,}715}{2{,}097{,}152} = 9.536743 \times 10^{-8}\text{ s}$ per tick.
   Moreover, a software patch added floating-point conversion subroutines in some
   call sites while leaving an older unpatched 24-bit conversion at a subtracted
   reference site! After $100\text{ hours}$ ($3.6 \times 10^6$ ticks) of
   continuous operation, the clock error reached $0.3433\text{ seconds}$. At the
   Scud's closing velocity of $1{,}676\text{ m/s}$, the radar range-gate prediction
   drifted by $687\text{ meters}$—outside the range gate—causing the system to
   reject the radar return as spurious clutter.

#### 2.4 Therac-25 (1985–1987), Industrial PLC Scan-Cycle Races, and the Robotics "Freezing Robot" / CBF Infeasibility Problem

1. **Therac-25 Linear Accelerator (`Leveson & Turner, IEEE Computer 26(7):18–41,
   July 1993`, `doi:10.1109/MC.1993.274940`):** Between June 1985 and January
   1987, six massive radiation overdoses (up to $25{,}000\text{ rads}$ instead of
   $200\text{ rads}$) occurred on the AECL Therac-25 PDP-11 assembly control
   software (`reused from Therac-6/20`, where physical electromechanical
   interlocks had masked the software bugs). Two distinct software failures
   caused the overdoses:
   - **Data-Entry / Magnet-Setting Task Race (`Datent` vs. `Hand`):** If an
     operator typed `X` (25 MeV X-ray mode, high beam current) and edited it to
     `E` (electron mode, low beam current) within an $8\text{ second}$ window
     while bending magnets were setting, the magnet routine (`Ptime`) missed the
     edit because a shared synchronization variable `Tphase` was not reset unless
     the cursor sat on the command line, leaving the beam at $25\text{ MeV}$
     X-ray current without the tungsten target in place.
   - **`Class3` 8-Bit Housekeeping Counter Wraparound (Tyler/Yakima Bug):** In
     field-light mode, the `Fcheck` routine incremented a 1-byte flag `Class3`
     on every pass to indicate an unverified collimator/turntable state (`Class3 != 0`
     blocked the beam). Every $256\text{th}$ pass ($\approx 4.2\text{ seconds}$),
     `Class3` overflowed (`255 + 1 = 0` in 8-bit arithmetic); if the operator
     pressed `SET` during that exact $16\text{ ms}$ tick, the software saw
     `Class3 == 0` (all checks passed!) and fired the unattenuated electron beam
     with the mirror instead of the scanner in the beam path.
2. **Industrial PLC Scan-Cycle Asynchronous I/O Tearing and Timer Edge Escapes
   (`IEC 61131-3` / `PLCverif`, Darvas et al., ICALEPCS 2015):** In industrial
   PLCs (Siemens S7, Allen-Bradley ControlLogix), safety interlock proofs often
   assume atomic "Read Inputs $\to$ Execute Logic $\to$ Write Outputs" scan
   cycles. On modern multi-core PLCs (e.g., ControlLogix asynchronous I/O update),
   fieldbus I/O buffers update *asynchronously* mid-scan: if a safety rung reads
   `Valve_Closed` twice in the same scan (`IF Valve_Closed AND NOT Valve_Closed`),
   a mid-scan sensor transition makes both true or both false, violating standard
   propositional tautologies! Similarly, calling an `IEC 61131-3` on-delay timer
   function block (`TON`) inside a conditional `IF` branch prevents the timer
   from seeing the falling edge (`IN := FALSE`), leaving `TON.Q` permanently
   latched `TRUE` on the next activation.
3. **Robotics "Freezing Robot Problem" and CBF-QP Actuator Infeasibility:**
   - **Freezing Robot Problem (Trautman & Krause, IROS 2010,
     `doi:10.1109/IROS.2010.5654369`; Fraichard & Asama, 2004 Inevitable
     Collision States):** When a mobile robot models surrounding pedestrians or
     agents with growing uncertainty forward-reachability cones, once obstacle
     density exceeds a threshold, **every** forward velocity vector intersects a
     predicted uncertainty cone. A planner verified only for partial-correctness
     safety (`defined = True`, no collision) halts in place ($\dot{q} = 0$) or
     rejects all trajectories, deadlocking permanently.
   - **Control Barrier Function Quadratic Program (`CBF-QP`) Infeasibility under
     Torque Saturation (Ames et al., IEEE TAC 2017,
     `doi:10.1109/TAC.2016.2638961`; Xiao & Belta, IEEE TAC 2022):** Standard
     CBF safety filters solve $\min_{u \in [u_{\min}, u_{\max}]} \|u - u_{\text{nom}}\|^2$
     subject to $\nabla h(x)\cdot(f(x) + g(x)u) + \alpha(h(x)) \ge 0$. Under
     bounded actuator torque $u \in [u_{\min}, u_{\max}]$ and relative degree
     $\ge 2$ kinematics (where $\nabla h(x) g(x) = 0$ on boundary manifolds),
     states inside $\mathcal{C} = \{x \mid h(x) \ge 0\}$ with high approach
     velocity have **no feasible control input $u$** satisfying both the CBF and
     torque bounds—causing the embedded OSQP/QP solver to return `INFEASIBLE` at
     runtime!

#### 2.5 Architectural Lessons for Anneal's 4 Primitives (Robotics, Aerospace & PLCs)

- **`BehaviorCodec` (`decodeOut = none`) prevents Ariane 5 diagnostic-as-data,
  MCO unit mismatches, and Therac-25 `Class3` wraparound:**
  - In Anneal, `BehaviorCodec L_sri L_obc` requires `decodeOut` to check frame
    tags and physical units: a diagnostic dump frame on `1553` maps to
    `decodeOut = none` (`False`), forcing the OBC to treat unvoted/diagnostic
    frames as contract failures rather than valid gimbal commands.
  - Typed dimensional units in `L_nav.Query` and `L_smForces.Out` (`NewtonSec` vs.
    `LbfSec`) cannot compose via `Compiles.comp` unless their `BehaviorCodec`
    proves `decodeOut_encodeOut` with the exact scaling constant.
  - Under `PartialBehaviorCodec`, mapping an unbounded counter in `L_spec` to an
    8-bit byte (`UInt8`) in `L_pdp11` requires proving that `Class3` never wraps
    from `255` to `0` (`0` is reserved exclusively for `.verifiedOk`); unguarded
    modular wraparound violates `encodeOut_of_decodeOut`.
- **`VerificationResultOn` (`pre` vs. `specs`) + `ProductiveOn` & `InhabitedPre`
  prevent Ariane 5 trajectory-reuse escapes and the Freezing Robot / CBF-QP
  infeasibility trap:**
  - Reusing an Ariane 4 library module (`sri_align`) inside an Ariane 5 whole-program
    crate requires discharging `sri_align`'s safety precondition `pre_ariane4`
    against Ariane 5's trajectory query distribution (`WellFormedOn pre`). Because
    Ariane 5's horizontal velocity violates `pre_ariane4`, the crate theorem
    fails to typecheck in Lean until the alignment task is disabled at liftoff
    or the saturation guard is restored.
  - `ProductiveOn pre prog` (`TotalStep` + `InhabitedDemonic`) directly rules out
    both CBF-QP infeasibility (an empty feasible control set $U_{\text{safe}}(x) = \emptyset$
    triggers `ReachesPrefix.emptyChoice` $\to$ `.stuck`) and the Freezing Robot
    Problem (when `SemObs` tracks waypoint progress via `EventualBehaviorOf`).
- **`StepResult.externalCall` + Positive `TrustPolicy` waivers prevent MPL
  stale-latch, 737 MAX single-sensor, and PLC mid-scan tearing escapes:**
  - Modelling sensor reads as `StepResult.externalCall boundaryInv branches`
    requires `boundaryInv` to verify that touchdown latches were cleared at mode
    entry (MPL) and that dual-channel AoA sensors agree within comparator
    tolerance (`|AoA_L - AoA_R| < 5.5°`, 737 MAX) before acting on sensor
    transitions.
  - The assumption `.atMostOneAoASensorFaulted` or `.aeroStabilizerAuthorityMax0_6Deg`
    is recorded as a positive `TrustPolicy` waiver tag—so increasing MCAS
    authority to $2.5^\circ$ immediately breaks the safety theorem rather than
    silently invalidating an external document.

---

### 3. Digital Logic, EDA, RTL/Gate Equivalence (LEC), CDC, and HLS Synthesis Failures

`Basis: normative + documentation + source + execution + derived`

#### 3.1 Intel Pentium `FDIV` Bug (1994): Hand-Proof Containment Boundary Omission in SRT Radix-4 PLA Table

In October 1994, Thomas Nicely discovered that the Intel P5 Pentium floating-point
unit returned corrupted quotients starting at the fifth significant decimal digit
(for example, $4195835.0 / 3145727.0 = 1.333739068902037589$ instead of
$1.333820449136241002$), ultimately costing Intel \$475 million to replace
affected processors (Pratt, *IEEE Trans. Computers* 44(1):161–162, 1995,
`doi:10.1109/12.368006`; Coe et al., *IEEE Comp. Sci. & Eng.* 2(1):18–32, 1995;
Harrison, *Formal Methods in System Design* 16(1):11–34, 2000,
`doi:10.1023/A:1008712907154`):

1. **Technical Root Cause:** The Pentium `FDIV` unit used a Sweeney-Robertson-Tocher
   (`SRT`) radix-4 recurrence $w_{j+1} = 4(w_j - q_j d)$, selecting each quotient
   digit $q_j \in \{-2, -1, 0, +1, +2\}$ via a Programmable Logic Array (`PLA`)
   lookup table indexed by a 7-bit truncated estimate of the shifted partial
   remainder $4w_j$ and a 4-bit truncated divisor $d$. Because radix-4 SRT
   redundancy ($\rho = 2/3$) requires every remainder to stay within the
   containment interval $|w_{j+1}| \le \frac{2}{3}d$, engineers wrote a script
   to populate the 2,048-entry PLA table based on an informal hand proof of the
   reachable $(4w_j, d)$ region.
2. **The Boundary Precondition Mismatch:** The script writer assumed that the
   upper boundary of the containment region was never entered and therefore set
   **five reachable table cells** in the $q_j = +2$ boundary row (at divisor
   indices $1, 4, 7, 10, 13$ of $[1, 2)$) to $0$ ("don't care") to minimize PLA
   transistor count. While that boundary was indeed unreachable from the steady-state
   interior for exact real remainders, **one-sided two's-complement truncation
   asymmetry** during the initial iterations drove specific rare divisor/dividend
   bit patterns onto those five boundary cells! Selecting $q_j = 0$ instead of
   $+2$ caused an immediate $2 \times 4^{-j}$ residual loss that later iterations
   could never recover because $|w_{j+1}|$ exceeded $\frac{2}{3}d$.

#### 3.2 RTL-to-Gate `X`-Optimism / `X`-Pessimism Escapes and UPF Power-Gating Corruption

In `IEEE 1364` (`Verilog`) and `IEEE 1800` (`SystemVerilog`), 4-valued logic
(`0`, `1`, `X` unknown/uninitialized/metastable, `Z` high-impedance) contains a
notorious semantic discrepancy between behavioral RTL simulation and synthesized
2-state silicon gates (Turpin, SNUG Boston 2003, *"The Dangers of Living with an
X (bugs hidden in your Verilog)"*; Litterick, SNUG 2012):

1. **`X`-Optimism in Behavioral `if`/`case` Constructs:** In standard Verilog
   RTL simulation:
   ```verilog
   if (sel) out = a;
   else     out = b;
   ```
   When `sel` evaluates to `1'bx` (due to an uninitialized non-reset register,
   out-of-bounds memory read, or powered-down UPF block), the `if` condition fails
   and RTL simulation deterministically executes the `else` branch (`out = b`).
   If `a == 1'b1` and `b == 1'b0`, RTL simulation sees a clean `1'b0` (`X` is
   erased!). In synthesized gate-level silicon (`out = (sel & a) | (~sel & b)`),
   or if a logic synthesizer (`Design Compiler` / `Genus` / `Yosys`) optimizes
   downstream logic under a `casez`/`full_case`/`parallel_case` don't-care
   directive, a physical `1` on `sel` produces `out = 1`, diverging from RTL
   simulation and causing post-reset state-machine lockup.
2. **Logical Equivalence Checking (`LEC`) Blindness to Don't-Care and UPF
   Power-Shutoff States:** Combinational LEC tools (`Synopsys Formality`,
   `Cadence Conformal`, `Yosys equiv_check`) verify RTL against gate-level
   netlists on the boolean subspace $\{0, 1\}^n$ and treat explicit `1'bx`
   assignments in RTL as synthesis *don't-cares* (any boolean function refines
   `X`). When an engineer unintentionally propagates `X` from an un-isolated
   Unified Power Format (`UPF`) shutoff domain or an un-reset pipeline register,
   LEC reports `SUCCEEDED (Equivalent)` even when the gate-level netlist ties a
   control line permanently high during power-domain wake-up!

#### 3.3 Clock-Domain Crossing (CDC) Reconvergence and Multi-Bit Bus Correlation Escapes

When signals cross asynchronous clock domains ($f_{\text{src}} \not\sim f_{\text{dst}}$),
a 2-stage flip-flop (`2-FF`) synchronizer prevents raw metastability from
entering destination logic with high Mean Time Between Failures (`MTBF`), but
passes take either $1$ or $2$ destination clock cycles to settle when transitions
fall inside the setup/hold aperture $[t_{\text{setup}}, t_{\text{hold}}]$
(Cummings, SNUG 2001 & 2008):

1. **Structural CDC Checker Escape via Reconvergent Synchronized Paths:**
   Structural CDC lint tools verify that every topological path crossing a clock
   boundary traverses a recognized `2-FF` synchronizer cell. However, if two
   logically correlated signals $(b_1, b_0)$ (or two status flags `pkt_valid` and
   `pkt_error`) each pass through their *own* legally instantiated `2-FF`
   synchronizer and reconverge at an `AND`/`XOR` gate in the destination domain,
   independent 1-cycle metastability skew allows `(0, 0) -> (1, 1)` in the source
   domain to transiently appear as `(0, 1)` or `(1, 0)` in the destination
   domain—violating one-hot or mutual-exclusion invariants despite 100%
   structural CDC compliance!
2. **Non-Power-of-Two Gray-Code FIFO Pointer Corruption:** Asynchronous FIFOs use
   Gray-coded read/write pointers so only 1 bit changes per increment. When an
   engineer parametrizes a FIFO with a non-power-of-two depth (e.g., depth $6$)
   and wraps the standard binary-to-Gray counter from index $5$ (`111_2`) back to
   $0$ (`000_2`), **three bits change simultaneously** on wrap-around, causing
   spurious FIFO empty/full flags and silent packet drops or overwrites in silicon.

#### 3.4 RTL and HLS Compiler Miscompilations: `Verismith`, `VeriCert`, and `TransFuzz` (`MiRTL` Confused-Deputy Gadgets)

Systematic fuzzing and formal verification of open-source and commercial hardware
compilers have exposed widespread silent miscompilations:

1. **`Verismith` Behavioral Verilog Fuzzing (`Herklotz, Pollard, Ramanathan, &
   Wickerson, ACM/SIGDA FPGA 2020`, `doi:10.1145/3373087.3375310`):** Using
   `Verismith` to generate deterministic, `X`-free behavioral Verilog and
   cross-checking synthesized netlists across `Yosys`, `Xilinx Vivado`, `XST`,
   and `Intel Quartus Prime` uncovered **11 distinct silent mis-synthesis bugs**
   (plus dozens of crashes). Concrete root causes in `Yosys` included:
   - `peepopt` / `wreduce` passes dropping sign-extension bits on nested ternary
     (`?:`) and shift expressions when operands mixed signed and unsigned widths;
   - `alumacc` and `share` passes merging arithmetic units with incompatible bit
     truncation widths; and
   - `Vivado` synthesis mis-optimizing nested signed multiplication and reduction
     operators inside sequential `always @(posedge clk)` blocks.
2. **`TransFuzz` and `MiRTL` Confused-Deputy Synthesis Trojans (`Solt & Razavi,
   USENIX Security 2024`, ISBN `978-1-939133-44-1`):** Using cell-level
   differential fuzzing (`TransFuzz`), Solt and Razavi discovered **31 new bugs
   (25 CVEs)** across `Yosys`, `Verilator`, `CXXRTL`, and `Icarus Verilog`,
   including **20 silent translation bugs**. They demonstrated that an attacker
   can embed a **Mistranslation RTL (`MiRTL`) gadget** inside the `CVA6` RISC-V
   processor: a combinational expression over signed/unsigned shifts and logical
   reductions that evaluates identically to constant `1'b0` in RTL simulation
   (`Verilator` / `Icarus Verilog`) and formal model checking, but is silently
   miscompiled by `Yosys` (`opt_expr` / `techmap`) into a triggerable `1'b1`
   wire that leaks supervisor privilege in synthesized silicon!
3. **Commercial HLS Miscompilations and `VeriCert` (`Herklotz, Kong, & Wickerson,
   FCCM 2021`; `Herklotz, Pollard, Ramanathan, & Wickerson, OOPSLA 2021`,
   `doi:10.1145/3485509`):** Fuzzing C-to-Verilog High-Level Synthesis tools
   (`Xilinx Vivado HLS`, `Intel HLS`, `LegUp`, `Bambu`) with `Csmith` programs
   exposed dozens of wrong-code miscompilations where aggressive pipeline modulo
   scheduling (`#pragma HLS pipeline II=1`) reordered load/store operations across
   aliased RAM ports or read uninitialized pipeline stage registers before valid
   data arrived. `VeriCert` (built on `CompCert` in Coq) proved that sound C-to-RTL
   HLS requires a machine-checked stutter-trace simulation between untimed C
   small steps and multi-cycle FSM-scheduled Verilog datapaths.

#### 3.5 Architectural Lessons for Anneal's 4 Primitives (Digital Logic, EDA & HLS)

- **`BehaviorCodec` (`decodeOut = none`) prevents `X`-Optimism and `FDIV`
  Containment-Boundary Escapes:**
  - In Anneal's 4-valued hardware instantiation (`L_rtl.Out` carrying `{0, 1, X, Z}`),
    `encodeOut` maps pure boolean architectural values to `{0, 1}`, while
    `decodeOut` maps any output vector containing `X` or `Z` to `none`! Under
    `PartialBehaviorCodec`, `Compiles L_isa L_rtl codec spec rtl` is **refuted**
    whenever an uninitialized register or un-isolated UPF domain can propagate
    `X` to an observable output or architectural state—eliminating LEC's
    `X`-don't-care soundness hole!
  - In SRT division (`FDIV`), the containment invariant $|w_j| \le \frac{2}{3}d$
    is part of `L_srt.sem`'s step contract (`defined`); checking all 2,048 table
    cells via Lean kernel `decide` (`rfl`) over `BitVec` widths eliminates
    unverified hand-proof boundary omissions.
- **`EventualBehaviorOf` + Proof-Gated Compilation (`Compiles`) eliminate `MiRTL`
  Confused-Deputy Gadgets and HLS Pipeline Hazards:**
  - `MiRTL` attacks succeed because RTL verification runs on Simulator A's
    semantics (`Verilator`) while silicon is produced by Synthesizer B (`Yosys`)
    with no proof linking the two. In Anneal, `Compiler.Verified` requires a
    machine-checked `Compiles L_rtl L_gate codec rtl gate` certificate (e.g., an
    `LRAT` SAT miter proof checked in Lean) for the exact emitted netlist,
    making `MiRTL` mistranslation impossible.
  - `EventualBehaviorOf` natively expresses $1 \to k$ HLS modulo-scheduled
    pipelines and `valid`/`ready` stall handshakes without lockstep cycle
    counters, while `ProductiveOn` prohibits pipeline deadlock (`stall = true`
    forever).
- **`StepResult.externalCall` catches CDC Reconvergence & Non-Power-of-Two Gray
  Codes:**
  - Rather than checking `2-FF` synchronizers purely structurally, modeling a
    multi-bit CDC boundary with `StepResult.externalCall boundaryInv branches`
    requires `boundaryInv` to verify that consecutive source words differ in at
    most 1 bit (`popcount (w_prev ^^^ w_curr) ≤ 1`), while `branches` demonically
    skews each bit's arrival by $1$ or $2$ destination cycles—immediately
    exposing reconvergent bus skew and non-power-of-two Gray-code wrap faults!

---

### 4. Quantum Circuit Compiler Miscompilations and Fault-Tolerant Decoder Failures

`Basis: normative + documentation + source + execution + derived`

#### 4.1 `QDiff` and `MorphQ`: Miscompilations in `Qiskit`, `TKET`, `Cirq`, and `PyZX`

Quantum transpilers (`IBM Qiskit`, `Quantinuum TKET`, `Google Cirq`, and the
`ZX-calculus` optimizer `PyZX`) apply deep chains of unitary matrix synthesis,
Kak/Cartan $SU(4)$ decompositions, commutation cancellation, and `SABRE`
heuristic `SWAP` routing. Automated differential testing via `QDiff` (Wang et al.,
ASE 2021, `doi:10.1109/ASE51524.2021.9678792`) and metamorphic testing via
`MorphQ` (Paltenghi & Pradel, ICSE 2022, `doi:10.1145/3510003.3510221`) uncovered
dozens of confirmed miscompilations and crashes:

1. **Global-Phase-to-Relative-Phase Escalation Under Controlled Gates (`Qiskit`
   & `Cirq`):** For a top-level closed quantum circuit, a global phase $e^{i\phi} U$
   is physically unobservable because measurement probabilities satisfy
   $|\langle x | e^{i\phi} U | \psi \rangle|^2 = |\langle x | U | \psi \rangle|^2$.
   Consequently, 1-qubit Euler decomposition passes (`Optimize1qGatesDecomposition`,
   `U3` / `ZYZ` synthesis) and `PyZX` spider-fusion passes routinely drop or
   approximate global phase scalars $e^{i\phi}$. However, when a compiler pass
   (`control()` promotion, sub-circuit inlining, or Quantum Phase Estimation)
   embeds that optimized subcircuit $e^{i\phi} U$ as a **controlled unitary**
   $\Lambda(e^{i\phi} U) = |0\rangle\langle 0| \otimes I + |1\rangle\langle 1|
   \otimes (e^{i\phi} U)$, the discarded global phase $e^{i\phi}$ becomes a
   **relative phase kickback** $R_z(\phi)$ on the control qubit—completely
   corrupting interference outcomes in QPE, Grover, and HHL algorithms!
2. **`SABRE` / `StochasticSwap` Qubit Routing Permutation Desynchronization:**
   When compiling an $n$-qubit circuit onto a restricted coupling graph (such as
   IBM heavy-hex), routing passes insert physical `SWAP` gates that permute which
   logical qubit resides on which physical wire ($\pi_t : Q_{\text{log}} \to
   Q_{\text{phys}}$). `QDiff` and `MorphQ` exposed bugs in `Qiskit` and `Cirq`
   where mid-circuit measurement, reset, or conditional `c_if` operations were
   applied to the initial logical qubit index rather than the post-`SWAP` routed
   physical qubit index $\pi_t(q)$, or where final classical bit measurement
   remapping was dropped when exporting to `OpenQASM 2.0`/`3.0`.
3. **`PyZX` Graph-Rewrite Scalar, Phase-Teleportation, and Boundary-Order Bugs:**
   In `PyZX` (Kissinger & van de Wetering, QPL 2019), circuits are converted to
   `ZX`-diagrams, simplified via spider fusion, local complementation, and
   pivoting, and extracted back to circuits via Gaussian elimination over $\mathbb{F}_2$.
   Historical bugs in `PyZX` included:
   - Un-normalized $\pi/4$ Clifford+$T$ scalar tracking when eliminating interior
     spiders during phase teleportation;
   - Circuit extraction (`extract_circuit`) failing to terminate (hitting a
     causal-flow / gflow deadlock when a non-unitary rewrite corrupted the
     biadjacency matrix) or permuting output boundary wires without emitting
     trailing `SWAP` corrections; and
   - Dropping non-zero post-selection scalars in measurement-based rewrites.

#### 4.2 Fault-Tolerant Surface-Code Threshold Collapse Under Correlated Cosmic-Ray Bursts and the Decoder Backlog Catastrophe

1. **Correlated Cosmic-Ray Phonon and Leakage Bursts Violating Independent-Noise
   Thresholds (`Wilen et al., Nature 594:369–373, 2021`,
   `doi:10.1038/s41586-021-03557-5`; `McEwen et al., Nature Physics 18:107–111,
   2022`, `doi:10.1038/s41567-021-01432-8`):** The foundational surface-code
   threshold theorem proves that logical error rates decay exponentially as
   $P_L \sim (p / p_{\text{th}})^{(d+1)/2}$ **under the premise that physical
   qubit errors are spatially and temporally uncorrelated (or strictly local)**.
   On Google's 2D Sycamore superconducting processor, McEwen et al. observed
   that a single cosmic-ray or background gamma-ray impact on the silicon
   substrate generates high-energy phonons that break Cooper pairs into
   quasiparticles across a millimeter-scale footprint ($\ge 10$–$25$ qubits
   simultaneously) for $> 10\text{ ms}$, while multi-photon drive transitions
   pump transmons out of the $\{|0\rangle, |1\rangle\}$ computational subspace
   into the $|2\rangle$ leakage state. Standard Minimum-Weight Perfect Matching
   (`MWPM`) and `Union-Find` decoders blinded by the independent-Pauli premise
   mis-pair syndrome defects across the burst diameter, causing the logical error
   rate to spike by orders of magnitude regardless of code distance $d$!
2. **Real-Time Syndrome Decoder Backlog Catastrophe (`Terhal, Rev. Mod. Phys.
   87:307–346, 2015`, `doi:10.1103/RevModPhys.87.307`):** While Clifford gates
   can be tracked offline via software Pauli-frame updates, executing a
   fault-tolerant non-Clifford $T$ gate via magic-state teleportation requires a
   conditional $S$ gate whose branch depends on the decoded logical measurement
   of all preceding syndrome rounds. If the syndrome generator produces data at
   rate $r_{\text{gen}}$ ($1\text{ round / }\mu\text{s}$ in superconducting
   qubits) and the decoder executes at rate $r_{\text{dec}} < r_{\text{gen}}$ (or
   suffers variable-latency `MWPM` blossoms on high-weight syndromes), the
   undecoded syndrome backlog after $k$ sequential $T$-gate layers grows
   **exponentially** as $(r_{\text{gen}} / r_{\text{dec}})^k$, stalling the
   quantum processor until decoherence destroys the logical state.

#### 4.3 Architectural Lessons for Anneal's 4 Primitives (Quantum Computing)

- **`Language SemObs` vs. `Out` in `BehaviorCodec` prevents Global-Phase-to-Relative-Phase
  Escalation:**
  - In Anneal, `L_subcircuit.Out` retains the **exact** unitary matrix $U \in U(2^n)$
    (including global phase $e^{i\phi}$) so compositional gate constructors like
    `Controlled(U)` are well-defined on `Out`, while `SemObs` (`obs : Out → SemObs`)
    projects top-level closed-circuit outcomes to the projective measurement
    distribution $P(m) = |\langle m | U | \psi \rangle|^2$ (quotienting out
    global phase *only* at the top-level observation projection `obs`, never
    inside open subcircuit `Out`!). Any pass that drops $e^{i\phi}$ inside a
    controlled context violates `Compiles` on `Out`.
- **`ProductiveOn` & `InhabitedPre` prevent Post-Selection Cheating and `PyZX`
  Extraction Deadlocks:**
  - A quantum channel or `ZX` rewrite must be trace-preserving (`Tr(E(ρ)) = 1`),
    corresponding to `ProductiveOn` (every valid input state yields an inhabited
    probability distribution of outcomes). Post-selecting on a probability-zero
    ancilla outcome (`Tr = 0`) steps to `.stuck` (`emptyChoice`), which
    `ProductiveOn` and `WellFormedOn` immediately reject.
- **`VerificationResult` Positive Waivers + Anneal-Verified Rust WCET prevent
  Correlated-Noise Blindness and Decoder Backlog:**
  - Rather than embedding independent depolarizing noise as an unguarded left-hand
    implication premise `hNoise : IndependentDepolarizing p → ...` (which becomes
    `False` during a cosmic-ray burst and would vacuously validate a broken
    decoder via `False.elim`), `.independentPauliNoiseBelow1Pct` and
    `.leakageResetActive` are explicit positive `TrustPolicy` waivers.
  - Implementing the `Union-Find` syndrome decoder in zero-allocation Rust
    verified by Anneal (`MirSem → ArmSem / X86Sem`) proves both syndrome
    correction correctness and a **hard upper bound on `steps : Nat` (WCET)**
    per syndrome round, mechanically ruling out the Terhal backlog catastrophe!

---

### 5. Analog/Mixed-Signal (SPICE), Silicon Photonics, and Programmable Metamaterial Escapes

`Basis: normative + documentation + source + derived`

#### 5.1 Analog/Mixed-Signal (`SPICE`) Discretization Artifacts, `Gmin` Hacks, and Zero-Current Bandgap Startup Lockup

Analog and mixed-signal (AMS) verification relies on differential-algebraic
equation (DAE) solvers (`SPICE2`, Nagel, Memorandum `UCB/ERL M520`, May 1975;
`Spectre`, Kundert, *The Designer's Guide to SPICE and Spectre*, 1995) solving
$C(v)\dot{v} + i(v) = u(t)$. Three classic simulation escapes repeatedly cause
silicon respins:

1. **Trapezoidal Integration Ringing (`trap`) vs. Gear-2 (`BDF2`) Artificial
   Numerical Damping:**
   - The second-order **Trapezoidal (`trap`)** rule is A-stable and preserves the
     imaginary axis ($j\omega$), making it accurate for high-$Q$ LC oscillators,
     but it is not L-stable: stiff eigenvalue steps on switching nodes produce
     point-to-point sawtooth numerical oscillation (`trap ringing`, $v_{k+1} -
     v_k \approx - (v_k - v_{k-1})$) that triggers false comparator edges in
     mixed-signal simulation.
   - Conversely, **Gear's 2nd-order Backward Differentiation Formula (`Gear-2` /
     `BDF2`)** is stiffly stable (damping high-frequency stiff modes), so designers
     routinely switch `.options method=gear` to silence `trap` ringing. However,
     `Gear-2`'s stability region extends into the **right-half complex plane**
     ($\text{Re}(s) > 0$), introducing **artificial positive numerical damping**!
     As documented by Kundert (1995), a Low-Dropout (`LDO`) regulator, Phase-Locked
     Loop (`PLL`), or high-speed op-amp with negative phase margin (physically
     unstable poles in the right-half plane near the imaginary axis) appears
     completely stable and well-damped under `Gear-2` transient simulation, only
     to oscillate violently on the silicon bench!
2. **`Gmin` Stepping and `cshunt` Convergence Hacks Masking Floating Nodes:**
   When Newton-Raphson fails to converge on a high-impedance CMOS node (such as
   a dynamic logic storage node or an un-driven power-gated well), `SPICE`
   inserts a virtual conductance `Gmin` (default $10^{-12}\text{ }\Omega^{-1}$)
   from every node to ground (or a shunt capacitance `cshunt`). On ultra-low-power
   subthreshold ($< 1\text{ nA}$) or retention circuits, a $1\text{ pA}$ virtual
   `Gmin` bleed current exceeds the real physical transistor leakage by $10\times$,
   discharging floating lockup states in simulation that persist indefinitely in
   silicon.
3. **Bandgap Reference and Self-Biased Cascode Zero-Current Degenerate Startup
   Lockup:** Precision bandgap voltage references (Widlar, 1971; Brokaw, 1974)
   and supply-independent constant-$g_m$ bias generators solve a nonlinear fixed-point
   equation $I_{\text{out}} = f(I_{\text{in}})$ that possesses **two stable DC
   equilibria**: the desired operating point ($I_0 > 0, V_{\text{BG}} \approx
   1.2\text{ V}$) and the parasitic **zero-current degenerate point** ($I = 0,
   V = 0$). Standard `.op` DC Newton-Raphson seeded near nominal bias converges
   to the desired operating point, and fast linear $V_{\text{dd}}$ ramp transient
   simulations ($dV_{\text{dd}}/dt = 1\text{ V/}\mu\text{s}$) inject capacitive
   displacement current $C \, dV_{\text{dd}}/dt$ that kicks the circuit out of
   the zero-current basin. Under a slow brownout recovery ramp ($1\text{ V/s}$)
   at $-40^\circ\text{C}$ (slow-slow corner `SS`), the capacitive kick falls
   below the subthreshold startup transistor threshold, trapping the chip in the
   $0\text{ A}$ dead state.

#### 5.2 Silicon Photonics MZI Mesh Coverage Holes and Thermo-Optic Crosstalk

Programmable photonic processors decompose an $N \times N$ unitary matrix $U \in
U(N)$ into a planar mesh of $\frac{N(N-1)}{2}$ Mach-Zehnder Interferometers
(`MZIs`) using Reck (1994) or Clements (Optica 2016,
`doi:10.1364/OPTICA.3.001460`) factorizations, assuming each MZI consists of two
ideal 50:50 directional couplers ($T = R = 1/2$) and two independent thermo-optic
phase shifters $(\theta, \phi)$:

1. **Non-50:50 Beam-Splitter Unitary Coverage Holes (`Bandyopadhyay, Hamerly, &
   Englund, Optica 8(10):1247–1255, 2021`, `doi:10.1364/OPTICA.424052`):**
   Wafer-scale waveguide lithography variations of $\pm 2\text{ nm}$ shift the
   evanescent coupling gap of a directional coupler away from $50:50$ by
   $\delta = \alpha - \pi/4 \ne 0$. When the two beam splitters in an MZI have
   splitting angles $\alpha_1, \alpha_2 \ne \pi/4$, the internal phase shifter
   $\theta$ can no longer sweep the MZI cross-port reflectivity $r$ down to zero:
   $$r_{\min} = \sin|\alpha_1 - \alpha_2| > 0, \qquad t_{\max} = \cos(\alpha_1 + \alpha_2 - \pi/2) < 1$$
   Consequently, an entire spherical cap of Givens rotations around the identity
   and swap transformations becomes **physically unreachable**! Compiling an optical
   neural network or quantum walk matrix $U$ via standard Clements angles $(\theta,
   \phi)$ hits the forbidden extinction zone, causing layer errors to accumulate
   exponentially across mesh depth $N$ (dropping classification fidelity from
   $> 95\%$ to $< 40\%$ on 64-mode meshes; Shen et al., *Nature Photonics* 11:441–446,
   2017, `doi:10.1038/nphoton.2017.93`).
2. **Thermo-Optic Mutual Crosstalk (`K_thermal`) and Heater Rail Clipping:**
   Because silicon has high thermal conductivity ($k_{\text{Si}} \approx 148\text{ W/(m}\cdot\text{K)}$),
   dissipating electrical power $P_j = V_j^2 / R$ in micro-heater $j$ raises the
   waveguide temperature of neighboring MZIs via the mutual thermal resistance
   matrix $\Delta \theta = K_{\text{thermal}} \mathbf{P}$. A compiler that treats
   phase shifters as orthogonal independent registers suffers coherent multi-path
   phase errors, while naive matrix inversion $\mathbf{P} = K_{\text{thermal}}^{-1}
   \theta_{\text{target}}$ frequently demands **negative heater power ($P_j < 0$)**
   or exceeds the maximum heater burn-out voltage $V_{\max}$!

#### 5.3 Programmable Metamaterial, MEMS Pull-In, and Origami Snap-Through Escapes

1. **MEMS Electrostatic Actuator Saddle-Node Pull-In Instability (`Nathanson,
   Newell, Wickstrom, & Davis, IEEE Trans. Electron Devices 14(3):117–133, 1967`,
   `doi:10.1109/T-ED.1967.15912`):** In a parallel-plate MEMS mirror or capacitive
   switch with initial gap $d_0$ and spring stiffness $k$, applying voltage $V$
   creates an equilibrium between linear mechanical restoration $k x$ and
   inverse-square electrostatic attraction $\frac{\varepsilon A V^2}{2(d_0 - x)^2}$.
   Linearized small-signal models used in control synthesis treat the actuator as
   stable across $x \in [0, d_0)$, missing the **saddle-node bifurcation at
   one-third of the gap** ($x_{\text{PI}} = \frac{1}{3}d_0$, pull-in voltage
   $V_{\text{PI}} = \sqrt{\frac{8 k d_0^3}{27 \varepsilon A}}$) where the
   electrostatic stiffness exceeds $k$ and the movable plate slams irreversibly
   into the bottom electrode (`stiction`).
2. **Rigid-Origami / Auxetic Metamaterial Pop-Through Bistability and Global
   Self-Intersection (`Silverberg et al., Science 345(6197):647–650, 2014`,
   `doi:10.1126/science.1252876`; `Waitukaitis et al., PRL 114:055503, 2015`):**
   Kinematic origami compilers verify local Kawasaki-Justin flat-foldability
   ($\sum (-1)^i \alpha_i = 0$) and single-vertex spherical trigonometry around
   each crease vertex. In multi-vertex Miura-ori and degree-4 deployable space
   structures, two escapes occur:
   - **Parasitic Multi-Stable "Pop-Through" Defects:** Non-monotonic crease
     folding angles create spurious local energy minima (Silverberg et al.
     "pop-through defects") where a panel snaps into an inverted mountain-valley
     assignment and locks the deployment mechanism.
   - **Global Non-Local Panel Self-Intersection:** Satisfying local vertex
     kinematics does not prevent distant facets from passing through each other
     in $\mathbb{R}^3$ along the folding trajectory.

#### 5.4 Architectural Lessons for Anneal's 4 Primitives (Analog, Photonics & Metamaterials)

- **`ProductiveOn` & `InhabitedPre` expose Bandgap Startup Lockup, MZI Extinction
  Coverage Holes, and Negative Heater Power:**
  - In Anneal, an analog startup verifier defines `InhabitedPre` over all valid
    power-on ramp rates $dV_{\text{dd}}/dt \in [r_{\min}, r_{\max}]$ and PVT
    corners, and requires `ProductiveOn` to reach the productive normal operating
    basin $[V_{\text{BG,min}}, V_{\text{BG,max}}]$ across every demonic trajectory
    branch—refuting circuits that can remain trapped in the $0\text{ A}$ fixed
    point.
  - In photonic MZI compilation (`Compiles L_unitary L_imperfectMzi`), when beam
    splitters have fabrication error $\delta \ne 0$, any target unitary $U$ that
    requires a reflectivity $r < r_{\min}$ or negative heater power $P_j < 0$
    produces an empty realizable angle set (`ReachesPrefix.emptyChoice` $\to$
    `.stuck`), refuting `ProductiveOn`! This forces the compiler either to scope
    `InhabitedPre` to the certified reachable submanifold $U_{\text{reach}}(N)$
    or to target a 3-coupler / double-MZI architecture (Bandyopadhyay et al.,
    2021) where `ProductiveOn` holds over all of $U(N)$.
- **`BehaviorCodec` (`decodeOut = none`) enforces Mixed-Signal Noise Margins and
  MEMS Pull-In Safety Envelopes:**
  - At an analog-to-digital boundary, `decodeOut : Voltage → Option Bool` maps
    $V \ge V_{IH}$ to `some true`, $V \le V_{IL}$ to `some false`, and any
    intermediate voltage $V \in (V_{IL}, V_{IH})$ at a clock sample edge to
    `none` (`False`).
  - Similarly, in MEMS actuation and origami deployment, `Partial.ub` (`defined =
    False`) triggers whenever $x(t) \ge \frac{1}{3}d_0 - \epsilon_{\text{margin}}$,
    crease strain exceeds plastic yield, or non-adjacent facets intersect in
    $\mathbb{R}^3$.

---

### 6. Cross-Domain Failure-to-Primitive Synthesis Matrix

`Basis: derived`

| # | Historical Incident / Tool Failure | Domain | Primary Failure Category | Technical Root Cause | Anneal `trusted/` Primitive That Prevents It |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1** | **`KeYmaera 3` Taclet & `Mathematica` `DSolve` Bugs** (Fulton et al., CADE 2015) | CPS / Hybrid Provers | (1) Soundness bug in prover/CAS | Scattered taclet `FV`/`BV` capture bugs; unverified symbolic division by zero / branch cuts in external `DSolve` | Small `trusted/lean/` kernel (`Refinement.lean`, `StepResult.lean` with zero theorems) + certificate checking in `theory/` |
| **2** | **Differential Ghost (`DG`) $y' = y^2$ Finite-Time Blowup** (Platzer, JAR 2017) | CPS / Hybrid Provers | (2) Vacuity / time-truncation bug | Non-Lipschitz ghost ODE $y' = y^2$ blows up at $t = 1/y_0$, truncating joint trajectories and making post-blowup safety vacuously true | **`ProductiveOn` & `InhabitedPre`** (`ReachesPrefix.noStep` / `emptyChoice` steps to `.stuck` when a trajectory ceases to exist) |
| **3** | **Evolution Domain `& H` "Time-Stop" Vacuity** (Platzer, LFCPS 2018) | CPS / Hybrid Modeling | (2) "Proved the wrong spec" vacuity | Putting safety obligations inside the evolution domain assumption `& H` stops time before unsafe states are entered | **`Partial.defined` vs. `InhabitedPre`** (safety invariants are obligations in `defined` / `post`, never trajectory-pruning guards) |
| **4** | **`SpaceEx` `GLPK` Floating-Point LP Grazing Escape** (Frehse et al., CAV 2011) | Hybrid Reachability | (1) Solver floating-point unsoundness | `IEEE-754` simplex pivot tolerances under-approximate support functions near grazing switching hyperplanes | **`Abstracts L_v L_src`** with exact rational / interval certificates (`decodeOut = none` on uncertified FP bounds) |
| **5** | **`Flow*` / `CORA` Taylor-Model Wrapping Effect** (Chen et al., CAV 2013) | Hybrid Reachability | (3) Wrapping-effect / usability wall | Enclosing rotated nonlinear flowpipes in axis-aligned interval boxes causes exponential remainder blowup | Compositional **`Abstracts`** via algebraic SOS Control Barrier Functions (`L_cbf`) avoiding long-horizon Picard wrapping |
| **6** | **Ariane 5 Flight 501 `SRI` Overflow & Databus Crash** (Lions Report, 1996) | Aerospace / Launchers | (2) Precondition reuse + codec failure | Reused Ariane 4 `BH` velocity precondition without re-proving on Ariane 5; `OBC` decoded `1553` diagnostic dump as gimbal angle | **`VerificationResultOn` (`WellFormedOn pre`)** forces re-proving `pre` on Ariane 5 + **`BehaviorCodec`** (`decodeOut = none` on diagnostic frames) |
| **7** | **Mars Climate Orbiter `SM_FORCES` Unit Mismatch** (NASA MCO MIB, 1999) | Spacecraft Navigation | (2) Interface unit-codec mismatch | Ground file emitted impulse in $\text{lbf}\cdot\text{s}$ instead of SI $\text{N}\cdot\text{s}$ ($4.45\times$ error) across untyped file boundary | **`BehaviorCodec L₁ L₂`** (`decodeQuery_encodeQuery` & `decodeOut_encodeOut` require machine-checked dimensional scaling) |
| **8** | **Mars Polar Lander Hall-Effect Touchdown Transient** (JPL D-18709, 2000) | Spacecraft Entry/Descent | (2) Unreset state invariant across mode switch | Leg-deployment transient latched touchdown flag at $1{,}500\text{ m}$; $40\text{ m}$ monitor read stale latch and killed engines | **`StepResult.externalCall` (`boundaryInv`)** requires proving mode-entry latch-reset invariant before enabling monitor |
| **9** | **Boeing 737 MAX MCAS Single-Sensor & Authority Escape** (NTSB ASR-19-01, 2019) | Avionics Flight Control | (2) Single-fault vulnerability + ODD drift | Single `AoA` sensor drove repetitive $2.5^\circ$ stabilizer trim (4$\times$ the $0.6^\circ$ FHA assumption) without comparator gate | **`StepResult.externalCall`** (demonic 1-sensor fault branch) + **Positive `TrustPolicy` waivers** (`.maxTrimAuthority0_6Deg`) |
| **10** | **Patriot Missile Dhahran 24-Bit Fixed-Point Drift** (GAO/IMTEC-92-26, 1992) | Air-Defense Radar | (2) Unbounded horizon quantization drift | 24-bit truncation of $0.1\text{ s}$ drifted $0.343\text{ s}$ ($687\text{ m}$) over $100\text{ h}$ continuous operation | **`Compiles L_real L_fixedPt`** (`BehaviorCodec` bounds accumulated quantization error over declared `steps : Nat` horizon) |
| **11** | **Therac-25 `Datent` Race & `Class3` 8-Bit Overflow** (Leveson & Turner, 1993) | Medical Control | (1) Concurrency race & integer wrap | Shared variable race during $8\text{ s}$ magnet bend + `Class3` 8-bit counter wrapping `255 + 1 = 0` to enable beam | **`PartialBehaviorCodec`** (`encodeOut_of_decodeOut` rejects 8-bit modular wrap from nonzero fault state to `0`) |
| **12** | **PLC Mid-Scan Asynchronous I/O Tearing & `TON` Latch** (Darvas et al., 2015) | Industrial PLCs | (2) Violated atomicity assumption | Asynchronous fieldbus updates mutate input variables mid-scan; skipped `TON` blocks miss falling edges | **`EventualBehaviorOf`** + **`StepResult.externalCall`** (models exact I/O snapshot vs. mid-scan demonic mutation) |
| **13** | **Freezing Robot Problem & CBF-QP Torque Infeasibility** (Trautman 2010; Ames 2017) | Autonomous Robotics | (2) Vacuous safety / `.stuck` deadlock | Planner commands $\dot{q} = 0$ forever or CBF-QP has no solution within torque limits $[u_{\min}, u_{\max}]$ | **`ProductiveOn` & `InhabitedPre`** (`TotalStep` + `InhabitedDemonic` requires feasible control and goal progress) |
| **14** | **Intel Pentium `FDIV` SRT PLA Table Omission** (Pratt 1995; Harrison 2000) | Microprocessor Arithmetic | (2) Hand-proof boundary omission | 5 reachable boundary cells of radix-4 SRT table set to `0` instead of `+2` due to unverified containment bound | Exhaustive finite-domain `BitVec` **`Compiles` / `WellFormed`** proof checked by Lean kernel `decide` (`rfl`) |
| **15** | **Verilog `X`-Optimism & LEC Don't-Care Escapes** (Turpin, SNUG 2003) | Digital RTL / LEC | (4) 2-state vs. 4-state formalism gap | RTL `if (1'bx)` takes `else` branch; LEC treats `X` as don't-care while gate silicon locks up on uninitialized state | **`PartialBehaviorCodec`** (`decodeOut` maps 4-valued `X`/`Z` to `none`, forcing proofs of `X`-propagation freedom) |
| **16** | **CDC Multi-Bit Reconvergence & Gray-Code Skew** (Cummings, SNUG 2008) | Multi-Clock VLSI | (4) Structural checker expressiveness gap | Correlated signals passing separate `2-FF` synchronizers experience independent 1-vs-2 cycle skew at reconvergent logic | **`StepResult.externalCall`** (`boundaryInv` enforces $\le 1$-bit Gray transition; `branches` demonically skews arrival) |
| **17** | **`Verismith`, `VeriCert`, & `TransFuzz` `MiRTL` Bugs** (Herklotz 2020/2021; Solt 2024) | RTL & HLS Synthesis | (1) Compiler miscompilation (25 CVEs) | `Yosys`/`Vivado` width-extension & HLS pipeline scheduling bugs; `MiRTL` gadgets evaluate to `0` in sim but `1` in silicon | **Proof-gated `Compiles` (`Compiler.Verified`)** + **`EventualBehaviorOf`** (certifies each lowered netlist/schedule) |
| **18** | **Quantum Global-to-Relative Phase Escalation** (`QDiff` 2021; `MorphQ` 2022) | Quantum Compilers | (1) Compositional pass miscompilation | 1q optimizer drops global phase $e^{i\phi}$; subsequent `control()` pass turns $e^{i\phi}$ into observable relative phase kickback | **`Language SemObs` vs. `Out`** (`Out` preserves exact unitary $U$; `obs : Out → SemObs` quotients global phase only at top level) |
| **19** | **`SABRE` Routing & `PyZX` Extraction Bugs** (`QDiff` 2021; `MorphQ` 2022) | Quantum Compilers | (1) Permutation & non-termination bugs | Mid-circuit measurements use unrouted qubit indices; `PyZX` extraction deadlocks or permutes boundary wires | **`BehaviorCodec`** (tracks explicit qubit permutation bijection $\pi_t$) + **`ProductiveOn`** (rules out post-selection `Tr = 0`) |
| **20** | **Surface-Code Cosmic-Ray Correlated Phonon Bursts** (McEwen et al., 2022) | Quantum Error Correction | (2) Violated independent-noise premise | Substrate cosmic-ray impact creates correlated 25-qubit quasiparticle burst & $|2\rangle$ leakage, collapsing code distance | **Positive Per-Obligation Waivers (`VerificationResult`)** + **`PartialBehaviorCodec`** (`decodeOut = none` on $|2\rangle$ leakage) |
| **21** | **Real-Time Syndrome Decoder Backlog Catastrophe** (Terhal, RMP 2015) | Quantum Error Correction | (3) Real-time WCET usability wall | Decoder latency $> 1\text{ }\mu\text{s}$ per round causes exponential backlog $(r_{\text{gen}}/r_{\text{dec}})^k$ at $T$-gate layers | Anneal-verified zero-allocation Rust `Union-Find` decoder proving bounded **`ExecQuery.steps` (WCET)** |
| **22** | **`SPICE` `Gear-2` Artificial Damping & Bandgap Lockup** (Nagel 1975; Kundert 1995) | Analog / Mixed-Signal | (1) Numerical damping + (2) $0\text{ A}$ trap | `Gear-2` damps unstable RHP poles in simulation; slow cold ramp traps bandgap reference in $0\text{ A}$ equilibrium | Conservative DAE enclosure **`Abstracts L_rnm L_spice`** + **`ProductiveOn`** over all power-on ramp trajectories |
| **23** | **Photonic MZI Non-50:50 Splitter & Thermal Crosstalk** (Bandyopadhyay et al., 2021) | Silicon Photonics | (4) Unreachable unitary hole + crosstalk | Coupler error $\delta \ne 0$ prevents zero reflectivity ($r_{\min} > 0$); `K_thermal` inversion requires negative heater power | **`ProductiveOn` & `InhabitedPre`** exposes unreachable unitaries and $P_j < 0$ clipping, forcing double-MZI or scoped `pre` |
| **24** | **MEMS Pull-In Bifurcation & Origami Pop-Through** (Nathanson 1967; Silverberg 2014) | Metamaterials & MEMS | (2) Linearized model omits bifurcation | Electrostatic pull-in at $x = d_0/3$; Miura-ori crease pop-through bistability and global facet self-intersection | **`Partial.ub` (`defined = False`)** on pull-in/self-intersection + verified interval Green's function / kinematic checks |

## Boundaries

- **Stochastic continuous-time martingale and measure-theoretic guarantees
  (`not examined` / `known not to apply` to `trusted/lean/` directly):**
  `Trusted.StepResult` and `Trusted.Refinement` model nondeterminism via
  possibilistic quantifier polarity (`ChoiceKind.demonic` and
  `ChoiceKind.angelic` over `State → Prop`). While bounded-weight fault budgets
  ($f \le k$), interval noise tubes, and finite-state discrete Markov chain
  transition matrices can be encoded as deterministic state-vector evolutions
  in `theory/`, continuous-time Itô stochastic differential equations
  ($dx = f(x)dt + \sigma(x)dW_t$) and measure-theoretic martingale concentration
  inequalities are **not examined** in `trusted/lean/` and require lifting to a
  certified moment/density abstract language (`Abstracts`) in `theory/`.
- **True concurrency and weak-memory hardware races (`not examined` in sequential
  small-step machines):** The Therac-25 interrupt-driven shared-memory race and
  multi-core PLC mid-scan asynchronous I/O tearing can be modeled at the point of
  external interaction via `StepResult.externalCall` (where `branches`
  demonically mutates shared I/O buffers across scan steps). However, fine-grained
  instruction-level weak-memory interleaving (`TSO`/`ARMv8` relaxed atomics) across
  concurrent hardware threads is **not examined** by the sequential single-thread
  `MirSemantics.lean` and `X86Semantics.lean` evaluators at
  `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`.
- **Empirical fidelity of foundry PDKs, aerodynamic tables, and quantum noise
  models (`known not to apply` as mathematical theorems):** Positive
  per-obligation waivers (`VerificationResult policy waived obligations`)
  structurally prevent an empirical modeling error (such as a cosmic-ray phonon
  burst violating independent depolarizing noise, or a wind-tunnel lookup table
  error) from causing logical explosion (`False.elim`) in the Lean proof. They do
  **not** prove that the physical hardware satisfies the waived empirical premise;
  validating a `TrustPolicy` waiver remains an empirical systems-engineering and
  hardware-characterization responsibility outside the deductive prover.
- **Commercial closed-source EDA and avionics source code (`unsupported` for
  direct source inspection):** For proprietary tools (`Synopsys Formality`,
  `Xilinx Vivado`, `Boeing 737 MAX FCC`, `Ariane 5 SRI`), findings rely on
  published black-box differential fuzzing reproducers (`Verismith`, `QDiff`,
  `MorphQ`) and official statutory accident investigation reports (`ESA/CNES`,
  `NASA`, `JPL`, `NTSB`, `GAO`) rather than direct inspection of proprietary
  source trees.

## Evidence

### 1. Primary Anneal Repository and Reference Corpus Sources (`source` + `execution`)

- **Anneal Core Refinement and Small-Step Semantics:**
  - Repository: `joshlf/anneal`
  - Revisions examined:
    - `24367bd1a8c784f2578535954f9915e24894a56f` (`main`),
    - `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted-core`), and
    - `4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`).
  - Files and symbols:
    - `trusted/lean/Trusted/Refinement.lean:208-299` (`Preorder`, `Partial`,
      `Partial.pure`, `Partial.ub`, `instPreorderPartial`, `Monotone`,
      `Behavior`),
    - `trusted/lean/Trusted/Refinement.lean:306-422` (`Language`,
      `Language.SpecOn`, `Language.WellFormedOn`, `Language.WellFormed`,
      `Compiles`, `Abstracts`, `Compiler`, `Compiler.SoundOn`,
      `Compiler.Verified`),
    - `trusted/lean/Trusted/Refinement.lean:426-480` (`TrustedAssumption`,
      `TrustPolicy`, `AllHold`, `VerificationResultOn`, `VerificationResult`),
    - `trusted/lean/Trusted/StepResult.lean:62-147` (`ChoiceKind`,
      `TerminationKind`, `FailureKind`, `StepResult`, `PrefixOutcome`,
      `PrefixOutcome.isSafe`, `ExecQuery`, `ExecOut`, `SmallStepMachine`), and
    - `trusted/lean/Trusted/StepResult.lean:157-216` (`ReachesPrefix`,
      `BehaviorOf`, `SmallStepMachine.toLanguage`).
- **Mechanized Hardening Proofs on the `reference` Branch
  (`df55c524a051d59e7dd35564f282b30d29133392`):**
  - `reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean`
    (`PartialBehaviorCodec`, `EventualBehaviorOf`, `eventual_wellFormed_iff_prefix_wellFormed`),
  - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/StructuralExternalCallAndCanaries.lean`
    (`StepResult.externalCall`, `ReachesPrefix.externalCallFail`,
    `ReachesPrefix.externalCallOk`, `open_world_callback_composition_sound`), and
  - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/support/ProofGatedCompilationAndTrustPolicy.lean`
    (`ScopedVerificationResult`, `global_antecedent_omission_explodes_crate`,
    `proof_gated_compilation_eliminates_ir_from_tcb`).

### 2. Primary Literature and Official Investigation Reports (`normative` + `documentation`)

- **CPS, Hybrid Systems, and Reachability Solvers:**
  - Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Völp, and André
    Platzer, *"KeYmaera X: An aXiomatic Tactical Theorem Prover for Hybrid
    Systems"*, CADE-25 (2015), LNCS 9195, pp. 527–538,
    `doi:10.1007/978-3-319-21401-6_36`.
  - Brandon Bohrer, Vincent Rahli, Ivana Vukotic, Marcus Völp, and André Platzer,
    *"Formally Verified Differential Dynamic Logic"*, CPP 2017, pp. 208–221,
    `doi:10.1145/3018610.3018616`.
  - Brandon Bohrer, Yong Kiam Tan, Stefan Mitsch, Magnus O. Myreen, and André
    Platzer, *"VeriPhy: Verified Controller Executables from Verified
    Cyber-Physical System Models"*, PLDI 2018, pp. 617–630,
    `doi:10.1145/3192366.3192406`.
  - André Platzer, *"A Complete Uniform Substitution Calculus for Differential
    Dynamic Logic"*, Journal of Automated Reasoning 59(2):219–265 (2017),
    `doi:10.1007/s10817-016-9385-1`.
  - Goran Frehse et al., *"SpaceEx: Scalable Verification of Hybrid Systems"*,
    CAV 2011, LNCS 6806, pp. 379–395, `doi:10.1007/978-3-642-22110-1_30`.
  - Xin Chen, Erika Ábrahám, and Sriram Sankaranarayanan, *"Flow\*: An Analyzer
    for Non-Linear Hybrid Systems"*, CAV 2013, LNCS 8044, pp. 258–263,
    `doi:10.1007/978-3-642-39799-8_18`.
  - Sicun Gao, Soonho Kong, and Edmund M. Clarke, *"dReal: An SMT Solver for
    Nonlinear Theories over the Reals"*, CADE-24 (2013), LNCS 7898, pp. 208–214,
    `doi:10.1007/978-3-642-38574-2_14`.
- **Robotics, Aerospace, Defense, Medical, and Industrial PLC Postmortems:**
  - Jacques-Louis Lions et al., *"Ariane 5: Flight 501 Failure — Report by the
    Inquiry Board"*, ESA/CNES, Paris, July 19, 1996.
  - Arthur G. Stephenson et al., *"Mars Climate Orbiter Mishap Investigation
    Board — Phase I Report"*, NASA, November 10, 1999.
  - Thomas Young et al., *"Report on the Loss of the Mars Polar Lander and Deep
    Space 2 Missions"*, JPL Special Review Board Report `JPL D-18709`, NASA/JPL,
    March 28, 2000.
  - National Transportation Safety Board, *"Assumptions Used in the Safety
    Assessment Process and the Effects of Multiple Alerts and Indications on
    Pilot Performance"*, Safety Recommendation Report `ASR-19-01`, September 19,
    2019; Komite Nasional Keselamatan Transportasi, Final Report
    `KNKT.18.10.35.04`, October 25, 2019.
  - United States General Accounting Office, *"Patriot Missile Defense: Software
    Problem Led to System Failure at Dhahran, Saudi Arabia"*, Report
    `GAO/IMTEC-92-26`, February 4, 1992.
  - Nancy G. Leveson and Clark S. Turner, *"An Investigation of the Therac-25
    Accidents"*, IEEE Computer 26(7):18–41, July 1993,
    `doi:10.1109/MC.1993.274940`.
  - Peter Trautman and Andreas Krause, *"Unfreezing the Robot: Navigation in
    Dense, Interacting Crowds"*, IEEE/RSJ IROS 2010, pp. 797–803,
    `doi:10.1109/IROS.2010.5654369`.
  - Aaron D. Ames, Xiangru Xu, Jessy W. Grizzle, and Paulo Tabuada, *"Control
    Barrier Function Based Quadratic Programs for Safety Critical Systems"*,
    IEEE Trans. Automatic Control 62(8):3861–3876, 2017,
    `doi:10.1109/TAC.2016.2638961`.
- **Digital VLSI, EDA, CDC, and HLS Synthesis:**
  - Vaughan Pratt, *"Anatomy of the Pentium Bug"*, IEEE Trans. Computers
    44(1):161–162 (1995), `doi:10.1109/12.368006`; John Harrison, *"Formal
    Verification of Floating Point Trigonometric Functions"* / SRT division,
    Formal Methods in System Design 16(1):11–34 (2000),
    `doi:10.1023/A:1008712907154`.
  - Mike Turpin, *"The Dangers of Living with an X (bugs hidden in your
    Verilog)"*, Synopsys Users Group (`SNUG`) Boston, 2003.
  - Clifford E. Cummings, *"Clock Domain Crossing (CDC) Design & Verification
    Techniques Using SystemVerilog"*, SNUG Boston, 2008.
  - Yann Herklotz, James D. Pollard, Nadesh Ramanathan, and John Wickerson,
    *"Finding and Understanding Bugs in FPGA Synthesis Tools"*, ACM/SIGDA FPGA
    2020, pp. 277–287, `doi:10.1145/3373087.3375310`.
  - Yann Herklotz, James D. Pollard, Nadesh Ramanathan, and John Wickerson,
    *"Formal Verification of High-Level Synthesis"*, Proc. ACM Program. Lang. 5
    (OOPSLA 2021), Article 117, `doi:10.1145/3485509`.
  - Flavien Solt and Kaveh Razavi, *"Lost in Translation: Enabling Confused
    Deputy Attacks on EDA Software with TransFuzz"*, 33rd USENIX Security
    Symposium (2024), ISBN `978-1-939133-44-1`.
- **Quantum Compilation and Fault-Tolerant Decoding:**
  - Jiyuan Wang et al., *"QDiff: Differential Testing of Quantum Software
    Stacks"*, 36th IEEE/ACM ASE 2021, pp. 692–704,
    `doi:10.1109/ASE51524.2021.9678792`.
  - Matteo Paltenghi and Michael Pradel, *"MorphQ: Metamorphic Testing of the
    Qiskit Quantum Computing Platform"*, 44th ACM/IEEE ICSE 2022, pp. 2413–2424,
    `doi:10.1145/3510003.3510221`.
  - Chris D. Wilen et al., *"Correlated Charge Noise and Relaxation Errors in
    Superconducting Qubits"*, Nature 594:369–373 (2021),
    `doi:10.1038/s41586-021-03557-5`.
  - Matt McEwen et al., *"Resolving Catastrophic Error Bursts from Cosmic Rays
    in Large Arrays of Superconducting Qubits"*, Nature Physics 18:107–111
    (2022), `doi:10.1038/s41567-021-01432-8`.
  - Barbara M. Terhal, *"Quantum Error Correction for Quantum Memories"*,
    Reviews of Modern Physics 87(2):307–346 (2015),
    `doi:10.1103/RevModPhys.87.307`.
- **Analog SPICE, Silicon Photonics, and Programmable Metamaterials:**
  - Laurence W. Nagel, *"SPICE2: A Computer Program to Simulate Semiconductor
    Circuits"*, Memorandum No. `UCB/ERL M520`, University of California,
    Berkeley, May 1975; Kenneth S. Kundert, *The Designer's Guide to SPICE and
    Spectre*, Kluwer Academic Publishers, 1995.
  - William R. Clements et al., *"Optimal Design for Universal Multiport
    Interferometers"*, Optica 3(12):1460–1465 (2016),
    `doi:10.1364/OPTICA.3.001460`.
  - Saumil Bandyopadhyay, Ryan Hamerly, and Dirk Englund, *"Hardware Error
    Correction for Programmable Photonics"*, Optica 8(10):1247–1255 (2021),
    `doi:10.1364/OPTICA.424052`.
  - Harvey C. Nathanson, William E. Newell, Robert A. Wickstrom, and J. R. Davis,
    *"The Resonant Gate Transistor"*, IEEE Trans. Electron Devices 14(3):117–133
    (1967), `doi:10.1109/T-ED.1967.15912`.
  - Jesse L. Silverberg et al., *"Using Origami Design Principles to Fold
    Reprogrammable Mechanical Metamaterials"*, Science 345(6197):647–650 (2014),
    `doi:10.1126/science.1252876`.

## Revalidation

To revalidate the architectural mappings between the 24 historical failure modes
and Anneal's four `trusted/` primitives after any change to `Trusted/Refinement.lean`
or `Trusted/StepResult.lean`:

1. **Re-run the mechanized anti-degeneracy, external-call framing, and scoped
   trust-policy Lean 4 probes** preserved on the `reference` branch using the
   pinned Lean 4 kernel (`leanprover/lean4:v4.34.1`, invoked with
   `-DElab.async=false -Ddebug.skipKernelTC=false`):
   - Check `reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean`
     to verify that `PartialBehaviorCodec` (`decodeOut : L₂.Out → Option L₁.Out`)
     still maps `decodeOut o₂ = none` to `False` and that `EventualBehaviorOf`
     still satisfies `eventual_wellFormed_iff_prefix_wellFormed` with zero
     axioms (`#print axioms`).
   - Check `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/StructuralExternalCallAndCanaries.lean`
     to verify that `StepResult.externalCall` and `ReachesPrefix.emptyChoice` /
     `noStep` step to `.failed` or `.stuck` (`isSafe = False`) with zero
     `Classical.choice`.
   - Check `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/support/ProofGatedCompilationAndTrustPolicy.lean`
     to verify that positive per-obligation waiver envelopes
     (`ScopedVerificationResult`) prevent a false assumption on one obligation
     from discharging sibling obligations via `False.elim`.
2. **Validate corpus metadata and formatting:**
   ```console
   python3 tools/reference.py check
   ```
   Verify that `REPORT.json` and `REPORT.md` pass all schema checks and that
   `./ci/check_todo.sh` reports zero violations.
