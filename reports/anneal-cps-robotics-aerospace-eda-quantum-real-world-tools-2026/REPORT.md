<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Real-World Verification, Synthesis, and Compilation Tools Across Cyber-Physical Systems, Robotics, Aerospace, Industrial Control, EDA/VLSI, Quantum Computing, Analog/Photonics, and Metamaterials

## Summary

Across cyber-physical systems (CPS), robotics, aerospace, industrial automation,
electronic design automation (EDA), quantum computing, analog/mixed-signal (AMS)
and silicon photonics, and programmable metamaterials, over eighty production
and research toolchains confront the same four verification and compilation
failure modes that motivated Anneal's four refined `trusted/lean/` primitives:

1. **Representation-invariant observation spines and fail-closed partial codecs
   (`Language SemObs`, `Partial`, and `BehaviorCodec`):**
   Real-world physical and hardware compilers translate between representations
   of unequal cardinality and abstraction—such as continuous differential
   equations vs. fixed-point Rust controllers (`OSQP`, `CVXGEN`, `FPTaylor`,
   `Daisy`), Lie-group $SE(3)$ kinematics vs. joint-angle vectors (`Pinocchio`,
   `Drake`, `IKFast`), synchronous dataflow vs. C/assembly (`SCADE KCG`,
   `Vélus`), 2-valued architectural ISA specs vs. 4-valued `0/1/X/Z` RTL and
   GDSII polygons (`Kôika`, `Kami`, `Yosys`, `OpenROAD`, `Magic`, `Netgen`),
   unitary Hilbert spaces vs. surface-code spacetime patches (`VOQC`, `QuiZX`,
   `Stim`, `lsqecc`), and transistor differential-algebraic equations (DAEs) vs.
   digital Real-Number Models (`SVReal`, `msdsl`). Equipping `Language SemObs`
   with `obs : Out → SemObs` and `BehaviorCodec` with partial outcome decoding
   (`decodeOut : L₂.Out → Option L₁.Out` satisfying `decodeOut_encodeOut`,
   `encodeOut_of_decodeOut`, and `obs_decodeOut`) turns out-of-band physical
   corruptions—IEEE-754 `NaN`s, non-unit quaternions, unknown `X` wires,
   unrouted GDSII opens/shorts, syndrome-uncorrectable quantum states, analog
   voltages in the forbidden threshold window $[V_{IL}, V_{IH}]$, and excessive
   optical insertion loss—into `decodeOut o₂ = none` (`False`), forcing
   refinement proofs (`Compiles`) to fail closed.
2. **Non-vacuity and progress against "freezing robot", empty-guard, and
   post-selection cheats (`ProductiveOn` and `InhabitedPre`):**
   Every domain surveyed exhibits a canonical Goodhart degeneracy when safety is
   stated purely as a negative invariant (`WellFormedOn pre`): a Control Barrier
   Function (CBF) synthesizer (`SOSTools`, `SumOfSquares.jl`) can choose an
   empty safe set $\mathcal{C} = \emptyset$; a motion planner or collision
   filter (`cuRobo`, `MoveIt 2`, `ORCA`) can command zero velocity forever (the
   "freezing robot problem"); a railway interlocking (`Prover iLock`) can hold
   all signals permanently red; a pipelined RTL or asynchronous handshake design
   (`Kôika`, `Calyx`, `ACT`, `Teak`) can assert `stall` forever; a quantum
   compiler (`PyZX`, `QuiZX`) can post-select on a probability-zero measurement
   branch ($\operatorname{Tr}(\mathcal{E}(\rho)) = 0$); an analog startup circuit
   (`Xyce`, `Ngspice`) can lock into a zero-current degenerate equilibrium; and
   a therapeutic ultrasound phased array (`k-Wave`) can turn all transducers off
   to avoid collateral tissue heating. Requiring `InhabitedPre pre`
   ($\exists q,\, \mathsf{pre}\;q$) and `Language.ProductiveOn pre prog`
   ($\forall q,\, \mathsf{pre}\;q \implies \exists h : (\mathsf{sem}\;\mathsf{prog}\;q).\mathsf{defined},\, \exists o,\, \mathsf{val}\;h\;o$)
   rules out all seven vacuity classes uniformly.
3. **Multi-rate time-scale decoupling and guarded open-world plant transitions
   (`EventualBehaviorOf` and `StepResult.externalCall`):**
   Physical and hardware systems inherently couple multi-rate execution scales:
   15 inner ADMM iterations of `OSQP` per 1 ms control sample, 5 pipelined RTL
   clock cycles or variable-latency `Calyx`/`VeriCert` schedules per ISA
   instruction, thousands of intra-scan CPU instructions per `IEC 61131-3` PLC
   I/O commit (`PLCverif`, `RuSt`, `Arcade.PLC`), and variable-round magic-state
   distillation per logical $T$ gate. `EventualBehaviorOf` (`Query := State`,
   `Out := EventualOut Obs Val`) preserves 100% of all-prefix safety
   (`eventual_wellFormed_iff_prefix_wellFormed`) with zero coinduction and zero
   `Classical.choice` while abstracting silent internal steps. At every
   actuator/sensor, clock-domain crossing (CDC), or mid-circuit syndrome
   boundary, the 4-line smart constructor
   `StepResult.externalCall boundaryInv branches` (`if boundaryInv then .choice .demonic branches else .failed .ub`)
   enforces launch invariants (actuator slew limits, passive-abort envelopes,
   Gray-code CDC stability, ancilla reset) before the environment demonically
   chooses disturbances, contact forces, metastability resolution cycles, or
   Pauli faults.
4. **Isolation of empirical physics, foundry PDK, and numerical solver axioms via
   positive per-obligation waivers (`VerificationResult`):**
   Unlike pure software verification, every physical, EDA, quantum, and
   photonic proof depends on empirical Operational Design Domain (ODD) envelopes
   and foundry models: aerodynamic lookup tables, tire friction bounds, `.lib`
   standard-cell delay corners (`OpenSTA`), foundry DRC decks (`Calibre`,
   `Magic`), BSIM compact transistor models (`Xyce`), and transmon depolarizing
   rates (`Stim`). Placing those empirical assumptions on the left of an
   implication (`AllHold (assumptions.map meaning) → ...`) allows any slight
   idealization contradiction (such as linearizing a nonlinear plant at a
   boundary query) to discharge unrelated fixed-point overflow or memory-safety
   proofs via `False.elim`. Anneal's positive per-obligation `VerificationResult`
   (`AllHold (waived.map policy.isAllowed) ∧ AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))`)
   records ODD, PDK, and untrusted-solver waivers explicitly without logical
   explosion.

---

## Applicability

This report applies to Anneal's core verification and refinement architecture
and to the ten real-world tool ecosystems indexed in `REPORT.json`:

1. **Anneal (`joshlf/anneal`)** at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`
   (`trusted-core`: `trusted/lean/Trusted/Refinement.lean` and
   `trusted/lean/Trusted/StepResult.lean`) and
   `4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`:
   `trusted/lean/Trusted/X86Semantics.lean`), together with the refined
   4-primitive architecture established in
   `reports/anneal-behavior-codec-and-progress-refinement-2026/`,
   `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/`,
   and `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/`.
2. **Lean 4 (`leanprover/lean4`)** at `v4.34.1`
   (`5045d0056413266e57c625dcd7c365b10e377c52`).
3. **Ten Real-World Physical, Hardware, Quantum, and Continuum Tool Ecosystems
   (Domains 1–10):**
   - *Domain 1 (Hybrid Control/CBFs/Reachability):* `KeYmaera X` (`5.1.1`),
     `Flow*`, `CORA`, `JuliaReach` (`ReachabilityAnalysis.jl`), `dReal4`,
     `FPTaylor`, `Daisy`, `OSQP`, `CVXGEN`, `SOSTools`/`SumOfSquares.jl`,
     `SpaceEx`, `HyPro`, `C2E2`, `DryVR`.
   - *Domain 2 (Robotics Kinematics/Planning/Swarms):* `Drake`, `Pinocchio`,
     `Crocoddyl`, `cuRobo`, `FCL`/`HPP-FCL`/`Coal`, `OMPL`, `MoveIt 2`,
     `RVO2`/`ORCA`, `IKFast`, `OCS2`, `TOWR`.
   - *Domain 3 (Aerospace/Avionics/RTA):* `Ansys SCADE Suite` (`KCG`),
     `Lustre`/`Vélus`/`Heptagon`, `Copilot`, `FRET`/`Ogma`,
     `ACAS X`/`Reluplex`/`Marabou`, `CoCoSim`, `Kind 2`, `F Prime` (`F'`),
     `cFS`, `Polyspace`, `Astrée`, `GMAT`, `Orekit`.
   - *Domain 4 (Industrial PLC/Rail/Grid):* `PLCverif`, `RuSt`
     (`plc-lang/rusty`), `MATIEC`, `OpenPLC`, `Prover iLock`/`Prover Certifier`,
     `Atelier B`/`ClearSy`, `Arcade.PLC`, `aiT WCET`, `SEL`/`IEC 61850`.
   - *Domain 5 (Digital VLSI/RTL/HLS/CDC/STA/Async):* `Yosys`/`SymbiYosys`/`ABC`,
     `Kôika`, `Kami`, `VeriCert`, `Bambu`/`LegUp`/`Vitis HLS`, `Calyx`, `CIRCT`,
     `JasperGold`/`VC Formal`/`Conformal LEC`, `SpyGlass CDC/UPF`, `OpenSTA`,
     `ACT`/`Balsa`/`Teak`.
   - *Domain 6 (Physical VLSI P&R/DRC/LVS/PEX):* `OpenROAD`, `Magic VLSI`,
     `Netgen`, `KLayout`, `Calibre`/`Pegasus`/`IC Validator`, `DREAMPlace`,
     `CuGR`.
   - *Domain 7 (Quantum Compilers & QEC):* `SQIR`/`VOQC`, `PyZX`/`QuiZX`,
     `Stim`, `PyMatching`/`Fusion Blossom`, `Qiskit SABRE`, `TKET`,
     `Enfield`/`OLSQ2`, `lsqecc`, `MQT-QCEC`, `Quipper`/`QWIRE`/`CertiQ`.
   - *Domain 8 (Analog/Mixed-Signal & Neuromorphic):*
     `SpaceEx-AMS`/`CORA-AMS`/`Ariadne`, `Xyce`/`Ngspice`,
     `SVReal`/`msdsl`/`Dragonfly`, `BAG2`/`ALIGN`/`MAGICAL`, `DELSIG`,
     `Lava`/`Brian2`/`Nengo`.
   - *Domain 9 (Silicon Photonics & Optical Meshes):* `SAX`/`Simphony`,
     `Neuroptica`/`TorchONN`/`Lightridge`, `GDSFactory`/`Nazca`,
     `Meep`/`Tidy3D`, `Strawberry Fields`/`Perceval`.
   - *Domain 10 (Metamaterials, Phased Arrays, Origami & Soft Robotics):*
     `k-Wave`, `Bempp-cl`, `MPB`, `MERLIN2`/`Origami Simulator`/`Crane`,
     `SOFA`/`DiffTaichi`, `TopOpt`/`Sugar`.

---

## Findings

### 0. Cross-Domain Architectural Synthesis: Mapping Physical & Hardware Toolchains onto Anneal's Four Trusted Primitives

`Basis: source + documentation + derived`

Across all ten domains, existing verification and synthesis tools split into
two camps: (1) **heavyweight interactive/foundational frameworks** (`KeYmaera X`,
`Vélus`, `Atelier B`, `Kôika`, `Kami`, `VeriCert`, `SQIR`/`VOQC`, `QWIRE`) that
achieve a small trusted computing base (TCB) by restricting users to a
domain-specific Coq or $\text{d}\mathcal{L}$ formalism, and (2) **high-throughput
numerical, heuristic, or SMT/SAT-driven industrial engines** (`Flow*`, `CORA`,
`OSQP`, `Pinocchio`, `cuRobo`, `Kind 2`, `Marabou`, `PLCverif`, `Yosys`/`ABC`,
`OpenROAD`, `QuiZX`, `Stim`, `PyMatching`, `SAX`, `k-Wave`) that scale to
industrial problem sizes but rely on large, unverified C++/Python/MATLAB solvers
and floating-point heuristics.

Anneal's four refined `trusted/lean/` primitives bridge these two camps by
allowing untrusted high-performance solvers in Domains 1–10 to act as
**certificate-emitting or proof-gated passes** checked inside the Lean 4 kernel:

| Anneal `trusted/lean/` Primitive | Exact Lean Signature & Laws | Universal Role Across Physical, EDA, Quantum & Continuum Toolchains (Domains 1–10) |
| :--- | :--- | :--- |
| **1. `Language SemObs`, `Partial`, & `BehaviorCodec`** | `Language (SemObs : Type)` with `obs : Out → SemObs`; `BehaviorCodec L₁ L₂` with `decodeOut : L₂.Out → Option L₁.Out`, `decodeQuery_encodeQuery`, `decodeOut_encodeOut`, `encodeOut_of_decodeOut`, `obs_decodeOut` | Separates representation-invariant physical/architectural observables (`SemObs`) from micro-state details while rejecting invalid physical/hardware states (`NaN`, non-unit $SE(3)$ poses, 4-valued `X`/`Z` wires, DRC/LVS violations, syndrome-uncorrectable quantum leakage, analog threshold violations $[V_{IL}, V_{IH}]$) via `decodeOut o₂ = none`. |
| **2. `ProductiveOn` & `InhabitedPre`** | `InhabitedPre pre := ∃ q, pre q`; `L.ProductiveOn pre prog := ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o, (L.sem prog q).val h o` | Eliminates vacuous synthesis and verification cheats: empty CBF safe sets (`SOSTools`), QP infeasibility (`OSQP`), the "freezing robot problem" (`cuRobo`, `ORCA`), permanent-red rail signals (`Prover iLock`), pipeline/handshake deadlocks (`Kôika`, `ACT`), trace-decreasing quantum post-selection (`PyZX`), analog startup lockup (`Xyce`), and zero-power phased arrays (`k-Wave`). |
| **3. `SmallStepMachine` with `EventualBehaviorOf` & `StepResult.externalCall`** | `EventualBehaviorOf` (`Query := State`, `Out := EventualOut Obs Val`); `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop) := if boundaryInv then .choice .demonic branches else .failed .ub` | Decouples multi-rate inner loops (`OSQP` ADMM iterations, PLC scan cycles, pipelined RTL stages, repeat-until-success quantum distillation) from macroscopic step transitions without coinduction, and enforces actuator/CDC/ancilla launch invariants (`boundaryInv`) before demonic environmental transitions (`branches`). |
| **4. Positive Per-Obligation `VerificationResult`** | `VerificationResult policy waived obligations := AllHold (waived.map policy.isAllowed) ∧ AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))` | Records empirical ODD assumptions (wind-tunnel tables, tire friction $\mu_{\min}$), foundry PDK rules (`.lib` corners, DRC decks, BSIM models), and unverified solver steps positively in `waived` without placing them on the left of `→` where a boundary modeling contradiction would explode unrelated proofs via `False.elim`. |

---

### 1. Domain 1: Hybrid Continuous-Discrete Control, Control Barrier Functions, and Reachability Envelopes

`Basis: source + documentation + normative + derived`

#### 1.1 Deductive Hybrid Theorem Proving: `KeYmaera X`

1. **Goals, problem domain, and target users:**
   `KeYmaera X` (`LS-Lab/KeYmaeraX-release`, v5.1.x) is an axiomatic tactical
   theorem prover for **Differential Dynamic Logic ($\text{d}\mathcal{L}$)**,
   designed by André Platzer's Logical Systems Lab (CMU / KIT) for formal
   verification of hybrid programs (discrete control transitions coupled with
   continuous ordinary differential equations $x' = f(x)\ \&\ Q(x)$) and hybrid
   games ($\text{d}\mathcal{G}\mathcal{L}$). Target users include formal methods
   researchers and safety engineers verifying train control (ETCS), airborne
   collision avoidance (`ACAS X`), and autonomous vehicle longitudinal/lateral
   envelopes.
2. **Development history, lineage, and evolution:**
   `KeYmaera X` succeeded the Java-based `KeYmaera` (built on the `KeY` prover,
   2008) and `KeYmaeraD` prototypes. Whereas original `KeYmaera` had a ~105,000
   LOC TCB intermingling calculus rules, differential invariant heuristics, and
   GUI state, `KeYmaera X` (introduced at CADE-25, 2015) replaced the rule-based
   sequent calculus with a **uniform substitution calculus** implemented in a
   Scala microkernel of ~2,000 LOC (`edu.cmu.cs.ls.keymaerax.core`).
3. **Design philosophy and architectural tradeoffs:**
   `KeYmaera X` strictly separates its tiny `core` microkernel (which knows only
   first-order real arithmetic, modal hybrid program axioms, differential
   ghosts/invariants, and uniform substitution variable-capture checks) from
   untrusted proof search implemented in the **Bellerophon** tactic language
   (`edu.cmu.cs.ls.keymaerax.bellerophon`). However, to discharge universal
   first-order real arithmetic leaves ($\text{FO}(\mathbb{R})$) via cylindrical
   algebraic decomposition (CAD), `KeYmaera X` delegates to external unverified
   procedures (`Mathematica` `Reduce`/`Resolve` or `Z3` `nlsat`).
4. **Relationship and comparisons to other tools:**
   Unlike set-propagation reachability tools (`Flow*`, `CORA`, `JuliaReach`,
   `SpaceEx`) that over-approximate reachable states over a bounded time horizon
   $t \in [0, T]$, `KeYmaera X` proves **unbounded-time inductive safety and
   liveness** ($t \in [0, \infty)$) symbolically via differential invariants
   ($\mathcal{L}_{f} I(x) \ge 0$), Differential Ghosts (Darboux polynomials),
   and Taylor-model flowpipe synthesis inside $\text{d}\mathcal{L}$ (`Pegasus`
   invariant generator).
5. **Formal theory, specification methodology, proof automation, and TCB:**
   A hybrid program $\alpha$ is verified against a modal formula
   $P(x) \to [\alpha] Q(x)$ (all runs of $\alpha$ starting in $P$ stay in $Q$)
   or $P(x) \to \langle\alpha\rangle Q(x)$ (existence of a winning run). The
   soundness of the uniform substitution calculus was mechanized in both
   Isabelle/HOL and Coq (`Bohrer et al., CPP 2017`), but the practical TCB in
   standard operation still includes the external `Mathematica`/`Z3` quantifier
   elimination oracle unless rational Sum-of-Squares (SOS) Positivstellensatz
   witnesses are checked internally.
6. **Exact mapping onto (and contrast with) Anneal's 4 `trusted/` primitives:**
   - $\text{d}\mathcal{L}$'s box modality $P \to [\alpha] Q$ corresponds to
     Anneal's `L_plant.sem α ≤ L_plant.SpecOn P Q`, while $\text{d}\mathcal{L}$'s
     diamond modality $P \to \langle\alpha\rangle \top$ (non-blocking execution
     across evolution domain constraints $x' = f(x)\ \&\ H(x)$) is the exact
     hybrid analogue of Anneal's `L_plant.ProductiveOn P α`! In $\text{d}\mathcal{L}$,
     an evolution domain constraint $H(x)$ restricts where the plant *may*
     evolve; if a user mistakenly writes a controller guard or evolution domain
     $H(x)$ that becomes false (`x' = f(x) & False`), the box modality
     $[\alpha] Q$ holds **vacuously** because all runs abort early. Requiring
     Anneal's `ProductiveOn` (and modeling physical plant boundaries via
     `StepResult.externalCall` rather than silent domain truncation) prevents
     evolution-domain vacuity. Furthermore, when `Mathematica` is used as an
     external QE oracle, Anneal's `VerificationResult` tracks `.qeOracleMathematica`
     as a positive per-obligation waiver (`ob.id ∈ waived ∨ ob.prop`) rather
     than admitting an unchecked axiom into the kernel environment.

#### 1.2 Continuous and Hybrid Reachability Analyzers: `Flow*`, `CORA`, `JuliaReach`, `SpaceEx`, `HyPro`, `C2E2`, and `DryVR`

1. **Goals, problem domain, and target users:**
   These seven tools compute conservative over-approximations (flowpipes) of the
   reachable state set $\operatorname{Reach}_{[0, T]}(\mathcal{X}_0)$ of
   continuous and hybrid dynamical systems $\dot{x} \in f(x, u, w)$ with discrete
   guard/reset transitions, serving control engineers and CPS verification
   teams (benchmarked annually in the `ARCH-COMP` Continuous and Hybrid Systems
   competition):
   - **`Flow*`** (`chenxin415/flowstar`, Xin Chen et al., CAV 2013): C++ engine
     for nonlinear ODEs and hybrid automata using **Taylor Models (TMs)**—a
     multivariate polynomial $p(x, t)$ up to order $k$ paired with a rigorous
     interval remainder $[a, b]$.
   - **`CORA`** (`TUMcps/CORA`, Matthias Althoff's group at TU Munich):
     Comprehensive MATLAB toolbox implementing **zonotopes**, **constrained
     zonotopes**, **polynomial zonotopes**, and **Taylor models** for linear,
     nonlinear, and differential-algebraic systems.
   - **`JuliaReach`** (`JuliaReach/ReachabilityAnalysis.jl` & `LazySets.jl`,
     Marcelo Forets, Christian Schilling, Sergiy Bogomolov et al.): High-performance
     Julia framework combining lazy support-function set operations (`LazySets.jl`)
     with Taylor-model integration (`TaylorModels.jl`).
   - **`SpaceEx`** (`Verimag`, Goran Frehse et al., CAV 2011) and **`HyPro`**
     (`hypro/hypro`, RWTH Aachen /Stefan Schupp et al.): C++ verification
     engines for piecewise-affine (PWA) and linear hybrid automata using
     **support functions**, **template polyhedra**, and the **LGG
     (Le Guernic–Girard)** algorithm.
   - **`C2E2`** (UIUC, Sayan Mitra's group, TACAS 2015) and **`DryVR`** (CAV
     2017): Simulation-driven verification tools that bloat numerical execution
     traces (`ODE45` / black-box simulator trajectories) into guaranteed
     reachtubes using **discrepancy functions** (local Lipschitz / Jacobian
     contraction bounds).
2. **Development history, lineage, and evolution:**
   First-generation hybrid reachability tools (`HyTech`, `d/dt`, `CheckMate`,
   1995–2003) suffered from the **wrapping effect** (exponential error blow-up
   when rotating interval boxes) and polyhedral vertex explosion in dimensions
   $n > 5$. Girard's introduction of zonotopes (HSCC 2005) and Le Guernic &
   Girard's support-function algorithm (`SpaceEx`, 2009–2011) scaled linear
   systems to $n > 100$. For nonlinear ODEs, Makino & Berz's Taylor Models were
   adapted to hybrid flowpipes by Chen, Ábrahám, and Sankaranarayanan (`Flow*`,
   2013), while Althoff introduced **polynomial zonotopes** (`CORA`, 2013–2026)
   to avoid exponential dependency blowup across non-convex nonlinear flows.
3. **Design philosophy and architectural tradeoffs:**
   - `Flow*` prioritizes rigorous interval arithmetic (`MPFR`) for Picard
     iteration contraction, trading speed for mathematical soundness on
     low-to-medium dimensional nonlinear ODEs ($n \le 15$).
   - `CORA` and `JuliaReach` prioritize algorithmic modularity and speed via
     zonotope order reduction and lazy support-function evaluation, scaling to
     high-dimensional systems but relying on IEEE-754 hardware floating-point
     in `CORA` unless interval rounding modes (`INTLAB`) are enabled.
   - `C2E2` and `DryVR` sacrifice symbolic flowpipe integration in favor of
     sensitivity-bloated simulation tubes, enabling verification of black-box
     Simulink/C++ controllers (`DryVR`) at the cost of probabilistic or
     user-supplied discrepancy axioms.
4. **Relationship and comparisons to other tools:**
   In `ARCH-COMP` (2020–2026), `CORA` and `JuliaReach` dominate linear (`AFF`)
   and high-dimensional nonlinear (`NLN`) benchmarks in execution speed, whereas
   `Flow*` and `Ariadne` provide stronger arbitrary-precision interval rigor on
   stiff nonlinear guards.
5. **Formal theory, specification methodology, proof automation, and TCB:**
   Nonlinear reachability checks whether $\forall t \in [0, T],\, \mathcal{R}(t) \cap \mathcal{U}_{\text{unsafe}} = \emptyset$.
   Soundness rests on Banach fixed-point contraction of the Picard operator
   $\Phi(x)(t) = x_0 + \int_0^t f(x(s))\,ds$ over a Taylor model enclosure
   $p(t, z) \oplus I$, plus guard-intersection enclosure when crossing switching
   surfaces $g(x) = 0$. None of `Flow*`, `CORA`, `JuliaReach`, `SpaceEx`, or
   `HyPro` emits kernel-checkable proof terms by default (though Fabian Immler
   mechanized zonotope/Runge-Kutta flowpipes in Isabelle/HOL, `Archive of Formal Proofs`).
6. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Upward Abstraction (`Abstracts L_flowpipe L_plant codec_tm v s`):** The
     flowpipe tube `v` (sequence of Taylor Models or Polynomial Zonotopes) is an
     abstract program in `L_flowpipe` that over-approximates all trajectories of
     the continuous plant `s` in `L_plant` (`L_plant.sem s ≤ codec_tm.toMorphism (L_flowpipe.sem v)`).
     Rather than trusting `CORA` or `Flow*`'s C++/MATLAB code, the untrusted
     analyzer emits the sequence of polynomial flowpipe coefficients and
     interval remainders $(p_k, I_k)$, and a verified Lean 4 checker in
     `theory/` validates Picard contraction $f(p_k \oplus I_k) \subseteq \dot{p}_k \oplus \dot{I}_k$
     using dyadic rational interval arithmetic!
   - **Preventing Zeno and Guard-Drop Cheats (`ProductiveOn`):** In hybrid
     automata, if a discrete transition guard $g(x) = 0$ is missed or an urgent
     transition has an empty reset map, the flowpipe silently vanishes.
     `ProductiveOn` requires every reachable flowpipe slice to remain inhabited
     and have dwell time $\tau_{\text{dwell}} \ge \tau_{\min} > 0$.

#### 1.3 Nonlinear Real SMT, Floating-Point Error Certifiers, and Embedded Convex/SOS Solvers: `dReal`, `FPTaylor`, `Daisy`, `OSQP`, `CVXGEN`, and `SOSTools`/`SumOfSquares.jl`

1. **Goals, problem domain, and target users:**
   - **`dReal` (`dreal/dreal4`, Sicun Gao, Soonho Kong, Edmund Clarke):**
     $\delta$-complete SMT solver over nonlinear real arithmetic plus
     transcendentals ($\sin, \cos, \exp, \arctan$), deciding whether a formula
     $\varphi$ is unsatisfiable (`unsat`) or its $\delta$-weakening $\varphi^\delta$
     is satisfiable (`delta-sat`).
   - **`FPTaylor` (`soarlab/FPTaylor`, Alexey Solovyev et al., TOPLAS 2018) and
     `Daisy` (`malyzajko/daisy`, Eva Darulova et al., TACAS 2018):** Sound
     static analyzers for IEEE-754 floating-point and fixed-point roundoff error
     using Symbolic Taylor Forms (`FPTaylor`) and affine/interval arithmetic +
     mixed-precision tuning (`Daisy`).
   - **`OSQP` (`osqp/osqp`, Bartolomeo Stellato, Goran Banjac, Paul Goulart,
     Stephen Boyd, 2020) and `CVXGEN` (Jacob Mattingley & Stephen Boyd, 2012):**
     Embedded convex Quadratic Programming (QP) solvers and C code generators.
     `OSQP` uses operator-splitting ADMM with division-free inner loops and
     explicit primal/dual infeasibility certificates; `CVXGEN` generates flat,
     branch-free primal-dual interior-point C code for fixed-dimension embedded
     MPC.
   - **`SOSTools` (Prajna, Papachristodoulou, Parrilo) and `SumOfSquares.jl`
     (`jump-dev/SumOfSquares.jl`, Benoît Legat, Pablo Parrilo et al.):**
     Formulate Control Lyapunov Functions (CLFs), Control Barrier Functions
     (CBFs), and region-of-attraction (ROA) verification as Sum-of-Squares (SOS)
     polynomial decompositions $p(x) = \sum_i q_i(x)^2 = z(x)^T Q z(x)$ solved
     via Semidefinite Programming (`Mosek`, `COSMO`, `CSDP`).
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - `SOSTools` and `SumOfSquares.jl` delegate SDP optimization to numerical
     floating-point interior-point solvers (`Mosek`); floating-point inaccuracies
     frequently yield matrices $Q$ that are only *approximately* positive
     semidefinite ($\lambda_{\min}(Q) \approx -10^{-9}$) or whose expanded
     monomial coefficients differ from $p(x)$ by $10^{-7}$, which can invalidate
     a naive SOS barrier proof near switching boundaries.
   - `FPTaylor` and `Daisy` bridges the gap between real-valued control proofs
     ($\mathbb{R}$) and target IEEE-754/fixed-point execution (`HOL Light`
     formalization in `FPTaylor`, Coq certificates in `FloVer`).
   - `OSQP` guarantees zero dynamic memory allocation (`malloc`-free) and works
     in single-precision or fixed-point arithmetic, making it the standard
     real-time QP engine for CBF-QP safety filters and MPC.
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **SOS Positivstellensatz Certificate Checking (`Abstracts`):** `SumOfSquares.jl`
     acts as an untrusted oracle that emits a rational/dyadic Gram matrix
     $Q = L D L^T$ ($D \ge 0$) and remainder bound; Lean 4 checks polynomial
     ring equality and diagonal positivity by `decide`/`rfl` in `theory/`,
     removing `Mosek` from the TCB.
   - **Certifying Embedded QP Compilation + Roundoff Bounding (`Compiles` +
     `BehaviorCodec` + `EventualBehaviorOf`):** Compiling an idealized CBF-QP or
     MPC controller into allocation-free Rust MIR (`OSQP`-in-Rust) composes a
     `EventualBehaviorOf` refinement (collapsing $K$ inner ADMM iterations into
     1 control step) with an `FPTaylor`/`Daisy`-style `BehaviorCodec` whose
     `decodeOut` rejects `NaN`/`Inf` (`decodeOut = none`) and bounds floating-point
     deviation within the CBF robustness margin $\delta$.

---

### 2. Domain 2: Robotics Kinematics, Whole-Body Optimal Control, Motion Planning, and Swarms

`Basis: source + documentation + derived`

#### 2.1 Rigid-Body Kinematics, Lie-Group Dynamics, and Whole-Body MPC: `Drake`, `Pinocchio`, `Crocoddyl`, `OCS2`, `TOWR`, and `IKFast`

1. **Goals, problem domain, and target users:**
   - **`Drake` (`RobotLocomotion/drake`, Russ Tedrake's group at MIT & Toyota
     Research Institute):** Model-based C++/Python design, multibody simulation,
     trajectory optimization, and Sums-of-Squares / Convex-Set (`GCS` — Graphs
     of Convex Sets) verification platform for manipulators, autonomous vehicles,
     and bipedal/quadruped robots.
   - **`Pinocchio` (`stack-of-tasks/pinocchio`, Justin Carpentier, Nicolas Mansard
     et al., INRIA / LAAS-CNRS):** Ultra-fast C++ library for rigid-body
     algorithms on Lie groups $SE(3)$—Forward Kinematics (FK), Recursive
     Newton-Euler Algorithm (RNEA) for inverse dynamics, Articulated-Body
     Algorithm (ABA) for forward dynamics, and exact analytical first- and
     second-order derivatives ($\partial \text{RNEA}/\partial q$,
     $\partial \text{ABA}/\partial \tau$) using code generation (`CppADCodeGen`).
   - **`Crocoddyl` (`loco-3d/crocoddyl`, Carlos Mastalli et al.) and `OCS2`
     (`leggedrobotics/ocs2`, Farbod Farshidian & Marco Hutter's RSL at ETH
     Zurich):** Real-time optimal control libraries for switched contact systems
     (quadrupeds like ANYmal and humanoids). `Crocoddyl` uses Feasibility-Driven
     Differential Dynamic Programming (`FDDP` / `Box-FDDP`) over `Pinocchio`
     analytical derivatives; `OCS2` solves continuous-time switched-mode
     hybrid optimal control problems via Sequential Linear Quadratic (`SLQ`) and
     Multiple-Shooting SQP (`SQP`) with `Pinocchio` and `HPP-FCL`.
   - **`TOWR` (`ethz-adrl/towr`, Alexander W. Winkler at ETH Zurich):**
     Nonlinear programming (NLP) trajectory optimizer (`Ipopt`) that
     simultaneously optimizes footstep locations, gait phase durations, and
     centroidal base motion using a 6-DoF Single Rigid Body Dynamics (SRBD)
     model and friction-cone constraints.
   - **`IKFast` (`rdiankov/openrave`, Rosen Diankov, CMU):** Analytical Inverse
     Kinematics compiler that symbolically solves the polynomial system of a 6-DoF
     or 7-DoF manipulator's kinematic chain using Dixon resultant / dialytic
     elimination and emits closed-form C++ code executing in ~2–5 microseconds.
2. **Development history, lineage, and evolution:**
   Roy Featherstone's Spatial Vector Algebra (`Spatial_v2`, 2008) established
   $O(N)$ recursive algorithms (`RNEA`, `ABA`, `CRBA`). Early C++ libraries
   (`KDL`, `RBDL`) lacked analytical second derivatives and Lie-group manifold
   abstractions, forcing numerical finite-differencing in optimal control.
   `Pinocchio` (2015–2026) exploited sparsity and Lie algebra $\mathfrak{se}(3)$
   identities to compute exact derivatives in a few microseconds, unlocking 100 Hz
   whole-body nonlinear MPC in `Crocoddyl` (ICRA 2020) and `OCS2` (ETH RSL) and
   Graphs of Convex Sets (`GCS`, Marcucci et al., 2023) in `Drake`.
3. **Design philosophy and architectural tradeoffs:**
   - `Pinocchio` + `Crocoddyl` / `OCS2` optimize for deterministic sub-millisecond
     C++ execution via template metaprogramming (`Eigen`) and `CppADCodeGen` JIT
     compilation, but treat contact mode sequences as pre-specified or locally
     linearized without formal verification of singularity freedom or global
     capture-point invariance.
   - `IKFast` achieves microsecond analytical IK by symbolically eliminating
     variables, but its generated C++ contains hundreds of unverified polynomial
     root-finding branches (`atan2`, `acos`, `sqrt`) susceptible to division by
     zero or `NaN` at kinematic singularities ($\det J(q) = 0$).
   - `Drake` uniquely integrates convex verification (`MakeSemidefiniteRelaxation`,
     SOS Lyapunov/ROA analysis, and `GcsTrajectoryOptimization`) alongside
     physics simulation, though its C++ solvers remain outside a formal proof
     kernel.
4. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Centroidal-to-Whole-Body Abstraction (`Abstracts L_srbd L_wholeBody codec_wb`):**
     `TOWR` and `OCS2` plan footsteps using a reduced Centroidal Momentum /
     Single Rigid Body Dynamics (`L_srbd`) model, which is tracked by whole-body
     torque control (`Pinocchio` RNEA, `L_wholeBody`). In Anneal, `Abstracts`
     formalizes this exact model reduction: proving that centroidal wrench and
     Zero-Moment Point (ZMP) / Contact Wrench Cone (CWC) margins enclose the
     full multi-body dynamics up to bounded limb-inertia coriolis error.
   - **Lie-Group $SE(3)$ and Singularity-Rejecting `BehaviorCodec`:** When
     compiling `Pinocchio` RNEA or `IKFast` into Rust MIR, `BehaviorCodec.decodeOut`
     maps output rotation matrices/quaternions and joint torques back to task
     space, returning `none` if $\|q_{\text{quat}}\|^2 - 1 > \epsilon$, if
     $\sigma_{\min}(J(q)) < \epsilon_{\text{sing}}$, or if any `atan2`/`sqrt`
     branch produces `NaN`—forcing the `IKFast` / RNEA compiler proof to guard
     all singular manifolds.
   - **Contact Complementarity via `StepResult.externalCall`:** At foot
     touchdown and liftoff transitions in `OCS2`/`Crocoddyl`,
     `StepResult.externalCall` checks `boundaryInv` (approach velocity within
     impact-absorption cone and friction-cone interior $\mu \|f_t\| < f_n$)
     before `branches` demonically transitions over terrain height and friction
     uncertainty.

#### 2.2 Collision Geometry, Sampling/GPU Motion Planning, and Swarm Reciprocal Avoidance: `FCL`/`HPP-FCL`/`Coal`, `OMPL`, `MoveIt 2`, `cuRobo`, and `RVO2`/`ORCA`

1. **Goals, problem domain, and target users:**
   - **`FCL` (`flexible-collision-library/fcl`, Jia Pan, Sachin Chitta, Dinesh
     Manocha) and `HPP-FCL` / `Coal` (`coal-library/coal`, Joseph Mirabel, Justin
     Carpentier et al., LAAS-CNRS / INRIA):** Standard C++ libraries for
     broad-phase (AABB trees) and narrow-phase collision detection, distance
     queries, and continuous collision detection (CCD) over convex meshes and
     BVHs using Gilbert-Johnson-Keerthi (`GJK`) and Expanding Polytope Algorithm
     (`EPA`). (`HPP-FCL` was officially renamed to `Coal`—Collision Detection
     Library—in 2024).
   - **`OMPL` (`ompl/ompl`, Ioan Șucan, Mark Moll, Lydia Kavraki at Rice
     University) and `MoveIt 2` (`moveit/moveit2`, PickNik Robotics):** `OMPL`
     provides asymptotically optimal sampling-based planners (`RRT*`, `PRM*`,
     `BIT*`, `FMT*`) over abstract state spaces; `MoveIt 2` wraps `OMPL`, `FCL`,
     and IK plugins into the ROS 2 manipulation stack.
   - **`cuRobo` (`NVlabs/curobo`, Balakumar Sundaralingam et al., NVIDIA, ICRA
     2023):** GPU-accelerated parallel motion generator written in CUDA/PyTorch
     that solves collision-free IK and non-convex trajectory optimization
     (`MPPI` + `L-BFGS` over signed distance fields / sphere decompositions) in
     under 30 ms—over $10\times$ faster than CPU `OMPL`/`MoveIt 2`.
   - **`RVO2` / `ORCA` (`snape/RVO2`, Jur van den Berg, Stephen J. Guy, Ming
     Lin, Dinesh Manocha, UNC Chapel Hill):** Decentralized multi-agent collision
     avoidance library implementing Optimal Reciprocal Collision Avoidance
     (`ORCA`), where each agent independently computes half-plane velocity
     constraints in 2D/3D and solves a linear program (LP) to select a
     collision-free velocity for time window $\tau$.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - **Discrete time-step tunneling in `OMPL`, `MoveIt 2`, and `cuRobo`:**
     Sampling-based planners (`OMPL`) and GPU trajectory optimizers (`cuRobo`)
     typically check collision only at discrete waypoint samples $q(t_0), q(t_1), \dots, q(t_N)$
     or approximate robot links with spheres (`cuRobo`). Thin obstacles can
     "tunnel" between consecutive time steps $t_k$ and $t_{k+1}$ unless swept-volume
     Continuous Collision Detection (CCD) or separating-hyperplane certificates
     are verified over the entire continuous interval $[t_k, t_{k+1}]$.
   - **Floating-point cycling in `GJK`/`EPA` (`FCL`/`Coal`):** In degenerately
     aligned polytopes, floating-point rounding in `GJK` simplex updates can
     cause infinite loops or false non-collision reports; `Coal` (`HPP-FCL`)
     adds convergence guards and warm-started separating axes.
   - **Deadlock / Freezing in `ORCA` (`RVO2`):** When $N$ agents meet in a
     symmetric narrow corridor or when velocity obstacles render the half-plane
     intersection empty, `ORCA` falls back to a "least-penetration" 3D LP that
     either freezes agents symmetrically ($\mathbf{v} = \mathbf{0}$) or drops
     hard collision guarantees.
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Certifying Swept-Volume Collision Checkers (`Abstracts`):** Instead of
     trusting `cuRobo`'s CUDA kernels or `OMPL`'s randomized tree search, the
     planner emits a piecewise-Bezier/spline trajectory together with a witness
     sequence of **GJK separating hyperplanes** $(\mathbf{n}_k, d_k)$ (exported
     from `Coal`) for each link-obstacle pair on $[t_k, t_{k+1}]$. A small
     verified Lean 4 checker verifies Bernstein control-point separation
     $\forall i,\, \mathbf{n}_k \cdot \mathbf{p}_{k,i}^{\text{robot}} > d_k \ge \mathbf{n}_k \cdot \mathbf{p}^{\text{obs}}$,
     proving continuous-time collision freedom (`defined = True`) with zero
     reliance on GPU floating-point determinism.
   - **Eliminating the Freezing Robot Problem (`ProductiveOn`):** In `MoveIt 2`,
     `cuRobo`, and `RVO2`/`ORCA`, safety (`defined`) requires zero collisions,
     while `ProductiveOn` (paired with `EventualBehaviorOf` reaching `.terminated`
     at $T_{\text{goal}}$) proves that the motion filter does not achieve safety
     by commanding $\dot{q} = 0$ forever or failing to find a feasible velocity
     in the `ORCA` half-plane LP.

---

### 3. Domain 3: Aerospace Avionics, Synchronous Dataflow Compilers, Runtime Assurance, and Astrodynamics

`Basis: source + documentation + normative + derived`

#### 3.1 Synchronous Dataflow Compilers and Model Checkers: `Ansys SCADE Suite`, `Lustre`, `Vélus`, `Heptagon`, `Kind 2`, and `CoCoSim`

1. **Goals, problem domain, and target users:**
   - **`Ansys SCADE Suite` & `KCG` (Esterel Technologies / Ansys):** Commercial
     synchronous model-based development environment and DO-178C Level A /
     EN 50128 SIL 4 qualified code generator (`KCG`) used in Airbus (A380, A350)
     and Boeing fly-by-wire flight controls, FADEC engine controllers, and
     nuclear protection systems.
   - **`Lustre` (Nicolas Halbwachs, Paul Caspi et al., Verimag), `Heptagon`
     (`PARKAS/heptagon`, Marc Pouzet, Gérard Berry et al., ENS Paris / INRIA),
     and `Vélus` (`INRIA/velus`, Timothy Bourke, Marc Pouzet et al., PLDI 2017–2023):**
     Synchronous dataflow languages based on streams, unit delays (`pre`, `->`),
     and hierarchical state machines (`Heptagon`), together with `Vélus`, the
     foundational Coq-verified compiler from `Lustre` (with `reset` and
     automata) down to `CompCert` `Clight` and assembly.
   - **`Kind 2` (`kind2-mc/kind2`, Cesare Tinelli's group at University of Iowa)
     and `CoCoSim` (`NASA-SW-VnV/CoCoSim`, NASA Ames):** `Kind 2` is a
     portfolio SMT-based ($k$-induction + IC3/PDR + invariant generation) model
     checker for `Lustre` with contract annotations (`assume`/`guarantee`/`mode`);
     `CoCoSim` compiles discrete Simulink/Stateflow models into `Lustre` for
     verification by `Kind 2`.
2. **Development history, lineage, and evolution:**
   Invented in the 1980s at Verimag (`Lustre`) and INRIA (`Esterel`, `Signal`),
   the **synchronous hypothesis** abstracts execution into discrete logical
   ticks where outputs are computed instantaneously and deterministically from
   inputs and previous state registers. `SCADE KCG` industrialized `Lustre` by
   achieving DO-178B/C tool qualification (`DO-330` TQL-1), eliminating manual
   unit testing of generated C code. To replace process-based qualification with
   mathematical proof, INRIA's `PARKAS` team built `Vélus` in Coq, composing
   dataflow normalization, clock-calculus lowering, and `Obc` imperative
   state-machine compilation directly with `CompCert`'s backend simulation
   theorems.
3. **Design philosophy and architectural tradeoffs:**
   - Synchronous languages forbid dynamic memory allocation, recursion, and
     unbounded loops, guaranteeing static causality (absence of algebraic loops)
     and deterministic memory footprints.
   - However, `Kind 2` and `CoCoSim` verify `Lustre` models over **unbounded
     mathematical integers ($\mathbb{Z}$) and exact reals ($\mathbb{R}$)** by
     default, whereas `SCADE KCG` and `Vélus` compile to finite-width machine
     integers (`int32`, `int64`) and IEEE-754 floats (`float32`, `float64`).
4. **Formal theory, specification methodology, proof automation, and TCB:**
   - `Vélus` proves in Coq that for every infinite input stream where the
     `Lustre` specification does not hit a runtime error, the compiled `CompCert`
     assembly step function `f_step` terminates on every tick and produces the
     exact sequence of outputs (`history_refinement`).
   - `Kind 2` checks contract-based `assume`/`guarantee` triples using SMT
     solvers (`Z3`, `cvc5`, `Yices 2`) via $k$-induction and IC3QE, and supports
     certificate generation in LFSC/Alethe.
5. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Stream-to-Imperative Step Refinement (`EventualBehaviorOf` + `Compiles`):**
     In `Vélus`, each logical tick of the declarative `Lustre` stream equation
     (`L_lustre`, 1 tick step) is realized by a finite sequence of $k$ imperative
     instructions in `Clight`/MIR/assembly (`L_mir`, $k$ micro-steps ending in
     a tick boundary observation `Obs.tickCommit`). Anneal's `EventualBehaviorOf`
     captures this tick-level refinement directly without coinductive streams,
     because universal quantification over finite prefixes in `.defined` covers
     arbitrarily many reactive ticks!
   - **Guarding Assume-Guarantee Vacuity (`ProductiveOn` & `InhabitedPre`):** In
     `Kind 2` compositional verification, if a sub-node's `assume` contract is
     self-contradictory or unrealized (`assume (x > 10 and x < 5)`), its
     `guarantee` holds vacuously. Requiring `InhabitedPre` and `ProductiveOn` on
     every synchronous node's contract prevents vacuous compositional proofs.

#### 3.2 Requirements Elicitation, Runtime Assurance Monitors, and Flight Software Frameworks: `FRET`, `Ogma`, `Copilot`, `F Prime`, `cFS`, `Polyspace`, and `Astrée`

1. **Goals, problem domain, and target users:**
   - **`FRET` (`NASA-SW-VnV/fret`), `Ogma` (`nasa/ogma`), and `Copilot`
     (`Copilot-Language/copilot`, Galois & NASA Langley):** NASA's end-to-end
     Requirements-to-Runtime-Verification (RV) pipeline. Engineers write
     structured natural-language requirements in `FRET` (`fretish` grammar:
     *scope, condition, component, shall, timing, response*), which formalizes
     them into past/future Metric Temporal Logic (`pmLTL`); `Ogma` translates
     those `FRET` specs into `Copilot` (a Haskell stream-DSL) and wraps them as
     standalone C99 monitor components for NASA's **`cFS`** (`nasa/cFS`, Core
     Flight System), **`F Prime`** (`nasa/fprime`, JPL's flight software
     framework used on the Mars Ingenuity Helicopter), or `ROS 2`.
   - **`Astrée` (AbsInt / ENS Paris, Patrick & Radhia Cousot, Blanchet et al.,
     PLDI 2003) and `Polyspace Bug Finder / Code Prover` (MathWorks):** Sound
     abstract-interpretation static analyzers for safety-critical C/C++ flight
     software that prove the absence of runtime errors (overflow, division by
     zero, out-of-bounds array access, invalid pointers, NaNs).
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - `Copilot` compiles Haskell stream specifications (`Atom` backend) into
     constant-time, constant-space C99 monitor code with zero dynamic memory,
     zero pointers, and bounded loops. However, `Copilot`'s Haskell-to-C99
     compiler is not formally verified inside a proof assistant (though NASA/Galois
     apply model checking and `What4` symbolic execution to the emitted C).
   - `Astrée` achieves zero false negatives (soundness) and near-zero false
     positives on Airbus A340/A380 fly-by-wire C code by combining the
     **octagon domain**, **relational ellipsoid domain** (crucial for second-order
     infinite-impulse-response digital filters $y_k = a_1 y_{k-1} + a_2 y_{k-2} + b_0 x_k$),
     and **floating-point linearization domain**. Its TCB is the unverified
     OCaml/C++ abstract interpreter itself.
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Ellipsoid/Octagon Abstract Domains (`Abstracts L_abs L_mir`):** Instead
     of trusting an external `Astrée` or `Polyspace` binary, `Astrée`'s ellipsoid
     and octagon post-fixpoint invariants are emitted as inductive state
     predicates in `theory/`; Anneal checks in Lean 4 that the invariant holds
     across each MIR/x86 basic block (`Abstracts`), reducing the TCB from a
     500k-LOC static analyzer to Anneal's `Trusted/Refinement.lean`.
   - **Runtime Assurance (RTA) Simplex Monitors (`StepResult.externalCall`):**
     When an unverified complex controller (or autonomy module in `F Prime` /
     `cFS`) outputs a command to a `Copilot`-style RTA safety monitor,
     `StepResult.externalCall boundaryInv branches` models the exact Simplex
     handoff: `boundaryInv` is the decidable `Copilot` monitor trigger checking
     that the command preserves the backup recovery envelope!

#### 3.3 Neural Collision Avoidance and Orbital Astrodynamics: `ACAS X` / `Reluplex` / `Marabou`, `GMAT`, and `Orekit`

1. **Goals, problem domain, and target users:**
   - **`ACAS X` (`ACAS Xu`), `Reluplex` (Guy Katz et al., CAV 2017), and
     `Marabou` (`NeuralNetworkVerification/Marabou`, Stanford / Hebrew
     University, CAV 2019 & 2024):** Next-generation airborne collision
     avoidance (`ACAS Xu`) compresses a multi-gigabyte Markov Decision Process
     (MDP) lookup table into deep ReLU neural networks (`45` networks of `6`
     hidden layers, `300` neurons). `Reluplex` and `Marabou` extend the Simplex
     LP algorithm with lazy ReLU phase-splitting (`ReLU(x) = max(0, x)`) and
     DeepPoly/Symbolic Bound Tightening (`SBT`) to formally prove geometric
     horizontal/vertical separation advisories across continuous airspace cones.
   - **`GMAT` (NASA Goddard General Mission Analysis Tool) and `Orekit`
     (`CS-SI/Orekit`, CS GROUP):** High-precision orbital mechanics and mission
     design frameworks implementing J2–J360 spherical-harmonic gravity fields,
     solar radiation pressure, atmospheric drag, and Dormand-Prince Runge-Kutta
     propagators (with Taylor-algebra automatic differentiation `Field<T>` in
     `Orekit`).
2. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Farkas Dual Certificates for `Marabou` (`Abstracts`):** `Marabou` can
     emit proof certificates (`Katz et al., TACAS 2022–2024`) consisting of a
     case-split tree over ReLU phases with Farkas dual vectors $\mathbf{y} \ge 0$
     certifying LP infeasibility at each leaf; Anneal verifies these linear
     combination certificates in `theory/` to discharge `ACAS Xu` advisory
     safety (`Abstracts`).
   - **Passive-Abort Orbit Envelopes (`ProductiveOn` + `TrustPolicy`):** Using
     `Orekit`'s `Field<TaylorAlgebra>` polynomials as Taylor-model flowpipes,
     Anneal's `ProductiveOn` certifies that at every spacecraft rendezvous burn,
     a passive drift abort trajectory exists that avoids the Keep-Out Sphere,
     while gravity-harmonic truncation (`.egm2008Degree36Truncated`) is tracked
     positively in `VerificationResult.waived`.

---

### 4. Domain 4: Industrial PLC Verification, Railway Interlocking, Worst-Case Execution Time, and Power-Grid Protection

`Basis: source + documentation + normative + derived`

#### 4.1 Industrial PLC Compilers and Model Checkers: `PLCverif`, `Arcade.PLC`, `RuSt` (`plc-lang/rusty`), `MATIEC`, and `OpenPLC`

1. **Goals, problem domain, and target users:**
   - **`PLCverif` (`plcverif-oss/cern.plcverif`, Darvas, Blanco Viñuela, Molnár
     at CERN):** Automated model-checking framework developed at CERN to verify
     Siemens `TIA Portal` (`SCL`, `STL`) and `IEC 61131-3` Structured Text
     programs controlling the Large Hadron Collider (LHC) cryogenics, personnel
     safety systems, and machine protection interlocks. Translates PLC programs
     into Control-Flow Automata (`CFA`), applies cone-of-influence and slice
     reductions, and dispatches to `nuXmv`, `Theta` (CEGAR), `CBMC`, or `ESBMC`.
   - **`Arcade.PLC` (RWTH Aachen, Biallas, Brauer, Kowalewski):** Static analysis
     and CEGAR model checker for ABB, Siemens, and `CODESYS` PLC programs using
     counterexample-guided abstraction refinement over three-valued logic.
   - **`RuSt` (`plc-lang/rusty`), `MATIEC` (`nucleron/matiec`), and `OpenPLC`
     (`thiagoralves/OpenPLC_v3`):** Industrial PLC compilers and runtimes.
     `MATIEC` compiles `IEC 61131-3` (`ST`, `IL`, `SFC`) to ANSI C for the
     `OpenPLC` cyclic scan runtime; `RuSt` (`plc-lang/rusty`) is a modern
     Rust-written `IEC 61131-3` compiler targeting LLVM IR directly.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - PLC semantics follows the **cyclic scan model**: (1) latch physical input
     image table $I_k$, (2) execute the PLC logic network deterministically to
     completion updating internal timers (`TON`, `TOF`, `TP`) and edge detectors
     (`R_TRIG`, `F_TRIG`), (3) commit physical output image table $Q_k$.
   - Both `MATIEC` and `RuSt` (`plc-lang/rusty`) are unverified compilers; bugs
     in `RET` early-exit lowering, `POINTER TO` aliasing in Structured Text
     (added in IEC 61131-3 3rd Edition), or `TIME` timer rollover can cause the
     compiled binary to diverge from the `CFA` model verified by `PLCverif`.
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Scan-Synchronous Observation Spine (`EventualBehaviorOf` + `SemObs`):**
     A single PLC scan cycle executes $10^3$–$10^5$ native CPU instructions
     before committing the output coil image $Q_k$. Under `EventualBehaviorOf`
     with `SemObs := List (InputImage × OutputImage)`, all intra-scan register
     and memory steps are silent (`Obs.tau`), and only the end-of-scan I/O latch
     is observable (`Obs.scanCommit I_k Q_k`). Thus `Compiles L_st L_mir` (and
     `L_mir → L_x86`) proves scan-for-scan equivalence between Structured Text
     and machine code while `Abstracts L_cfa L_st` binds `PLCverif`'s safety
     invariants to the exact same `L_st` semantics!

#### 4.2 Railway Interlocking, Formal B-Method Refinement, WCET, and Power-Grid Relays: `Prover iLock` / `Prover Certifier`, `Atelier B` / `ClearSy`, `aiT WCET`, and `SEL` / `IEC 61850` Checkers

1. **Goals, problem domain, and target users:**
   - **`Prover iLock` & `Prover Certifier` (Prover Technology, Gunnar Stålmarck):**
     Commercial CENELEC `EN 50128 SIL 4` railway interlocking design and
     formal verification suite used across major metro and mainline rail networks
     (NYCT, SNCF, Network Rail, Stockholm). Uses **Stålmarck's saturation
     method** and commercial SAT/SMT induction to verify route interlocking
     tables (`PiSPEC` geographic requirements), and uses **`Prover Certifier`**
     as an independent proof checker that validates the generated safety proof
     DAG (`SIL 4` diversification).
   - **`Atelier B` & `ClearSy Safety Platform` (ClearSy, Jean-Raymond Abrial):**
     Industrial toolchain for the **B-Method** (set theory + Generalized
     Substitutions + stepwise invariant refinement from abstract `MACHINE` to
     `REFINEMENT` to concrete `IMPLEMENTATION` in `B0` compilable to C/Ada),
     used in Paris Métro Line 14 (`Météor`), Roissy VAL, and CBTC train control
     globally.
   - **`aiT WCET Analyzer` (AbsInt, Ferdinand & Wilhelm):** Industry-standard
     binary-level Worst-Case Execution Time static analyzer combining
     **value/address analysis** (abstract interpretation), **microarchitectural
     pipeline + cache analysis** (must/may LRU cache abstract domains), and
     **Implicit Path Enumeration Technique (`IPET`)** via Integer Linear
     Programming (ILP) over the Control-Flow Graph.
   - **`SEL` (`RTAC` / `IEC 61850` GOOSE/SV Protection Relay Logic Checkers):**
     Substation protection relays (`Schweitzer Engineering Laboratories SEL-421`,
     `SEL-451`) execute sub-cycle phasor distance (`ANSI 21`), differential
     (`ANSI 87`), and overcurrent (`ANSI 50/51`) protection equations alongside
     `IEC 61850` Generic Object Oriented Substation Events (`GOOSE`) interlock
     trees.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - **`Prover iLock` + `Prover Certifier` is the closest industrial precedent
     in rail signaling to Anneal's architecture:** an untrusted synthesizer and
     prover (`iLock`) generates both the interlocking boolean code and a deductive
     proof log, which a small, independent `Prover Certifier` binary checks to
     satisfy `EN 50128 SIL 4` without human review of the solver!
   - **B-Method (`Atelier B`) vs. Anneal:** In the B-Method, stepwise refinement
     ($M_0 \sqsubseteq M_1 \sqsubseteq \dots \sqsubseteq M_n$) uses forward data
     refinement (`gluing invariant` $J(x_a, x_c)$) and proves non-blocking guard
     feasibility via separated proof obligations (`FIS` / `WD`). Anneal's
     `Compiles L₁ L₂ codec.toMorphism` and `Language.ProductiveOn` achieve the
     exact same refinement and non-blocking guarantees using a single partial
     behavior preorder (`Query → Partial (Out → Prop)`) inside Lean 4's
     dependent type theory, avoiding `Atelier B`'s custom theorem prover and
     unverified `B0`-to-C translator.
   - **`aiT WCET` mapping:** In Anneal, `aiT`'s `IPET` bound can be verified
     inside `theory/` by attaching a cycle-cost accumulator to `X86State` (or
     `MirState`) and checking the dual LP certificate of the `IPET` flow
     constraints over basic-block execution counts!

---

### 5. Domain 5: Digital VLSI, RTL/HLS Synthesis, Clock-Domain Crossing, Static Timing Analysis, and Asynchronous Hardware

`Basis: source + documentation + derived`

#### 5.1 Foundational Rule-Based &HLS Hardware Verification: `Kôika`, `Kami`, `VeriCert`, `Calyx`, and `CIRCT`

1. **Goals, problem domain, and target users:**
   - **`Kôika` (`mit-plv/koika`, Thomas Bourgeat, Clément Pit-Claudel, Adam
     Chlipala, Arvind at MIT PLV, PLDI 2020):** Coq-embedded rule-based hardware
     design language descending from `Bluespec SystemVerilog` (`BSV`). Replaces
     `BSV`'s heuristic, opaque rule-scheduler with explicit **Logically Atomic
     Rules** and user-controlled conflict-resolution **Ephemeral History
     Registers (EHRs)**, featuring a Coq-verified compiler to cycle-accurate RTL
     that proves the **One-Rule-At-A-Time (ORAAT)** serializability theorem.
   - **`Kami` (`mit-plv/kami`, Joonwon Choi, Muralidaran Vijayaraghavan, Benjamin
     Sherman, Adam Chlipala, Arvind at MIT PLV, ICFP 2017):** Coq framework for
     compositional specification, modular refinement (via trace inclusion on
     labeled transition systems), and synthesis of Bluespec-style hardware modules
     (used to verify pipelined RISC-V processors with caches and cache-coherence
     protocols).
   - **`VeriCert` (`ymherklotz/vericert`, Yann Herklotz, Davidert, John Wickerson
     at Imperial College London, OOPSLA 2021 / POPL 2024):** Formally verified
     High-Level Synthesis (HLS) compiler in Coq built on top of `CompCert`.
     Compiles C (`CompCert` `RTL` IR) through static scheduling (`HTG` —
     Hierarchical Task Graph), modulo loop pipelining, and register/FSM
     allocation down to synthesizable Verilog (`Verilog` AST), with a
     machine-checked simulation proof.
   - **`Calyx` (`cucapra/calyx`, Rachit Nigam, Adrian Sampson et al. at Cornell,
     ASPLOS 2021) and `CIRCT` (`llvm/circt`, LLVM / SiFive / Intel / Microsoft):**
     Next-generation intermediate representations for hardware compilers. `Calyx`
     explicitly splits hardware into structural data-path `cells`/`wires` and an
     imperative `control` schedule (`seq`, `par`, `while`, `invoke`, `static<k>`),
     compiling control down to deterministic FSMs. `CIRCT` brings MLIR dialects
     (`FIRRTL`, `HW`, `Comb`, `Seq`, `Handshake`, `Calyx`, `Arc`, `Verif`, `SMT`)
     to open-source EDA, including formal equivalence and BMC passes (`circt-lec`,
     `circt-bmc`).
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - `Kôika`, `Kami`, and `VeriCert` provide foundational Coq proofs down to an
     idealized 2-valued (`bool` / `BitVec`) RTL AST, but rely on unverified
     pretty-printers to emit Verilog text and do not model 4-valued logic
     (`0, 1, X, Z`), asynchronous Clock-Domain Crossings (CDC), or physical
     setup/hold timing slack.
   - `Calyx` and `CIRCT` enable rapid pass engineering (`static` latency
     promotion, register sharing, retiming) across MLIR dialects, and `CIRCT`'s
     `Verif`/`SMT` dialect (combined with `Lean-MLIR` semantics research) targets
     automated translation validation, though most `CIRCT` passes remain
     unverified C++ transformations.
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Latency-Insensitive & Pipelined Refinement (`EventualBehaviorOf`):**
     In `VeriCert`, `Calyx`, and `Kami`, one source transaction (e.g., a C loop
     iteration or single-cycle ISA instruction) executes across $k$ RTL clock
     cycles with variable stall/handshake delays (`go`/`done` in `Calyx`).
     Under Anneal's `EventualBehaviorOf`, intra-transaction clock ticks without
     external I/O handshakes are silent (`Obs.tau`), while committed bus/memory
     handshakes emit `Obs.io`, allowing `Compiles L_isa L_rtl` and
     `Compiles L_mir L_verilog` to compose with **zero** step-dilation arithmetic!
   - **ORAAT Rule Scheduling as Upward Abstraction (`Abstracts L_oraat L_rtl`):**
     `Kôika`'s One-Rule-At-A-Time theorem—that every single-cycle multi-rule
     schedule in `L_rtl` produces a state transition equal to some sequential
     composition of atomic rules in `L_oraat`—is literally
     `Abstracts L_oraat L_rtl codec_oraat spec_rules rtl_sched`!

#### 5.2 RTL Synthesis, Formal Property/Equivalence Checking, HLS, CDC/UPF, STA, and Asynchronous VLSI: `Yosys`/`SymbiYosys`/`ABC`, `Bambu`/`LegUp`/`Vitis HLS`, `JasperGold`/`VC Formal`/`Conformal`, `SpyGlass`, `OpenSTA`, and `ACT`/`Balsa`/`Teak`

1. **Goals, problem domain, and target users:**
   - **`Yosys` (`YosysHQ/yosys`, Claire Wolf), `SymbiYosys` (`YosysHQ/sby`), and
     `ABC` (`berkeley-abc/abc`, Alan Mishchenko & Robert Brayton at UC Berkeley):**
     The open-source RTL synthesis and formal verification backbone. `Yosys`
     elaborates Verilog/SystemVerilog into `RTLIL` and word-level cells;
     `SymbiYosys` orchestrates SystemVerilog Assertions (`SVA`: `assert`,
     `assume`, `cover`) via SMT/word-level (`btor2`, `Bitwuzla`, `Z3`, `Yices 2`)
     and bit-level (`ABC` `pdr` / `ic3`, `avy`, `aigbmc`) engines; `ABC` performs
     And-Inverter Graph (`AIG`) rewriting (`dch`, `fraigs`), sequential retiming,
     LUT/standard-cell technology mapping, and Sequential Equivalence Checking
     (`SEC`).
   - **Commercial Formal & Lint Suites (`Cadence JasperGold` / `Conformal LEC`,
     `Synopsys VC Formal` / `Formality` / `SpyGlass CDC & LP/UPF`):** Industry
     gold-standard RTL signoff engines for SVA model checking (`JasperGold`),
     combinational/sequential Logic Equivalence Checking (`Conformal LEC`),
     structural + functional Clock-Domain Crossing (`SpyGlass CDC`: 2-FF
     synchronizer recognition, Gray-code reconvergence checks, FIFO protocol
     checks), and Unified Power Format (`UPF` IEEE 1801) isolation/retention
     verification.
   - **Industrial & Academic C/C++ HLS (`Bambu` `ferrandi/PandA-bambu` at
     Politecnico di Milano, `LegUp`, and `AMD/Xilinx Vitis HLS`):** Compile
     LLVM IR with pragma directives (`#pragma HLS pipeline II=1`, `unroll`,
     `array_partition`) via System of Difference Constraints (`SDC`) linear-programming
     scheduling and Chaitin-style resource binding into RTL.
   - **Static Timing Analysis (`OpenSTA` `parallaxsw/OpenSTA`, James Cherry):**
     Gate-level timing signoff engine used in `OpenROAD` and commercial flows.
     Reads `.lib` (Liberty Non-Linear Delay Model `NLDM` / Composite Current
     Source `CCS` tables), Verilog gate netlists, `.sdc` timing constraints, and
     `.spef` RC parasitics to verify setup ($t_{\text{launch}} + d_{\text{max}} + t_{\text{setup}} \le T_{\text{clk}} + t_{\text{skew}}$)
     and hold ($t_{\text{launch}} + d_{\text{min}} \ge t_{\text{hold}} + t_{\text{skew}}$)
     slack across all topological paths.
   - **Asynchronous Clockless Hardware (`ACT` `asyncvlsi/act` by Rajit Manohar
     at Yale, `Balsa`, and `Teak` by Doug Edwards & Andrew Bardsley at
     Manchester):** Design and synthesize clockless Quasi-Delay-Insensitive
     (`QDI`) and micropipeline circuits using Communicating Hardware Processes
     (`CHP`), Production Rule Sets (`PRS`: pull-up/pull-down CMOS transistor
     guards), and token-flow handshake networks (`Balsa`/`Teak`).
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - **X-Optimism and 4-Valued Logic (`0, 1, X, Z`):** `ABC` and standard boolean
     SAT/AIG equivalence checkers operate in 2-valued boolean logic (`{0, 1}`),
     which can unsoundly declare two circuits equivalent when an uninitialized
     flip-flop or gated-off UPF power domain drives `X` into a reconvergent
     multiplexer (`X ^ X = 0` boolean tautology vs. `X` in 4-valued Kleene logic).
   - **Unsensitizable "False Path" Waivers in `OpenSTA`:** Designers routinely
     add `set_false_path` and `set_multicycle_path` exceptions in `.sdc` files
     to silence `OpenSTA` timing violations without a formal proof that the path
     cannot be logically sensitized—a notorious cause of silicon respins.
   - **Interference and Instability in Asynchronous `ACT` PRS:** In `ACT`, if pull-up
     and pull-down production rules $G^+ \to z \uparrow$ and $G^- \to z \downarrow$
     are ever simultaneously true ($G^+ \land G^-$), the CMOS gate short-circuits
     (`interference`); if a guard transitions back to false before the output wire
     fires, a glitch/hazard occurs (`instability`), corrupting QDI handshake
     tokens.
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **4-Valued Kleene Logic & X-Rejection via `BehaviorCodec`:** Modeling
     `L_rtl.Out` in 4-valued logic (`0, 1, X, Z`) while defining
     `BehaviorCodec.decodeOut` to return `none` whenever any observable output
     wire carries `X` or `Z` automatically forces `Compiles L_isa L_rtl` (and
     UPF power-shutoff refinement) to prove complete reset initialization,
     UPF isolation-cell clamping, and freedom from X-optimism!
   - **Certifying `Yosys`/`ABC` Synthesis & `OpenSTA` False Paths (`VerificationResult`):**
     `ABC` emits `LRAT` SAT certificates for combinational AIG miters and
     inductive latch invariants for sequential retiming, checked inside Lean 4.
     Similarly, every `set_false_path` in `OpenSTA` becomes a first-class
     `Obligation` in `VerificationResult`: either proved logically unsensitizable
     via an `LRAT` certificate in `theory/` (`ob.prop`) or audited explicitly in
     `waived` under `TrustPolicy`!
   - **Asynchronous `ACT` Non-Interference & Deadlock Freedom (`Partial.ub` + `ProductiveOn`):**
     In `ACT` Production Rule Sets, short-circuit interference ($G^+ \land G^-$)
     and non-monotonic instability step to `Partial.ub` (`defined = False`),
     while `ProductiveOn` proves that the `CHP`/`Teak` handshake network is
     deadlock-free and completes every token transaction.

---

### 6. Domain 6: Physical VLSI Place-and-Route, DRC/LVS Verification, and Parasitic Extraction

`Basis: source + documentation + derived`

#### 6.1 Autonomous RTL-to-GDSII Place-and-Route and GPU Physical Design: `OpenROAD`, `DREAMPlace`, and `CuGR`

1. **Goals, problem domain, and target users:**
   - **`OpenROAD` (`The-OpenROAD-Project/OpenROAD`, Andrew Kahng at UCSD, DARPA
     IDEA program):** Integrated, autonomous ("No-Human-In-Loop") open-source
     RTL-to-GDSII physical design toolchain built atop the unified `OpenDB`
     database (`LEF`/`DEF`/`ODB`). Orchestrates floorplanning (`TritonFPlan`),
     analytical electrostatics global placement (`RePlAce`) and legalization
     (`OpenDP`), Clock-Tree Synthesis (`TritonCTS`), gate sizing and buffer
     insertion (`Resizer` + `OpenSTA`), global routing (`FastRoute`), detailed
     routing (`TritonRoute`), and parasitic extraction (`OpenRCX`).
   - **`DREAMPlace` (`limbo018/DREAMPlace`, Yibo Lin & David Z. Pan at UT Austin /
     Peking University, DAC 2019):** GPU-accelerated global placement engine
     that casts analytical VLSI placement ($\min \sum \text{WL}(e) + \lambda \|\rho(x,y) - \rho_{\text{target}}\|^2$,
     using weighted-average wirelength and Bell-shaped electrostatic density)
     as a neural-network training problem in PyTorch/CUDA, achieving $30\times$–$40\times$
     speedups over multi-threaded CPU placers (`RePlAce`) on million-cell designs.
   - **`CuGR` (`cuhk-eda/CuGR` / `CuGR 2.0`, Evangeline F. Y. Young's group at
     CUHK, ICCAD 2020):** GPU-accelerated 3D VLSI global router using
     fine-grained CUDA pattern routing, maze routing over congestion-negotiated
     G-cell graphs, and layer assignment.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - Placement (`RePlAce`, `DREAMPlace`) and routing (`CuGR`, `TritonRoute`)
     solve NP-hard combinatorial and non-convex continuous optimization problems
     using floating-point GPU kernels (`DREAMPlace`), multi-threaded rip-up-and-reroute
     heuristics (`TritonRoute`), and randomized tie-breaking.
   - However, **checking** whether a completed placement and routed `DEF`/`GDSII`
     layout is legal (cells sit on valid standard-cell rows without overlap,
     every net's routed wire-and-via Steiner tree connects all pins of that net,
     and no two distinct nets intersect in 3D layer space) is a fast, deterministic
     polynomial-time geometric problem!
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Topological-to-Geometric Refinement (`Compiles L_netlist L_layout codec_pdk`):**
     `OpenROAD`, `DREAMPlace`, and `CuGR` sit completely outside the TCB as
     untrusted layout synthesizers. In Anneal, `L_netlist.Prog` is the gate-level
     hypergraph netlist and `L_layout.Prog` is the placed-and-routed polygon
     layout. A small, verified Lean 4 checker in `theory/` verifies cell
     non-overlap and row alignment (legalization) and checks that the union-find
     equipotential components of `L_layout` form a strict bijection (`BehaviorCodec`)
     with the hyperedges of `L_netlist`.
   - **Ruling Out Open-Pin Deletion Cheats (`ProductiveOn`):** If a detailed
     router (`TritonRoute`) resolves congestion by leaving a net unrouted (open
     circuit) or deleting a standard cell, `L_layout` steps to `Partial.ub` or
     fails `ProductiveOn`, guaranteeing 100% routed connectivity.

#### 6.2 Physical Verification (DRC, LVS, and Layout Engines): `Magic VLSI`, `Netgen`, `KLayout`, and `Calibre` / `Pegasus` / `IC Validator`

1. **Goals, problem domain, and target users:**
   - **`Magic VLSI` (`RTimothyEdwards/magic`, originally John Ousterhout et al.
     at UC Berkeley 1983, maintained by Tim Edwards / Open Circuit Design):**
     Open-source VLSI layout editor, continuous incremental **Design Rule
     Checker (DRC)**, and transistor/RC parasitic extractor (`ext2spice`,
     `ext2sim`) using the **corner-stitching** spatial data structure (where
     both solid material tiles and empty-space tiles are explicitly linked at
     their four corners, enabling $O(1)$ neighbor lookup).
   - **`Netgen` (`RTimothyEdwards/netgen`, Tim Edwards):** Open-source **Layout
     Versus Schematic (LVS)** netlist comparator that proves graph isomorphism
     between the extracted physical SPICE netlist from `Magic` and the golden
     synthesized Verilog/SPICE schematic using iterative vertex/net signature
     refinement (partitioning nodes by device types, pin degrees, and neighbor
     hashes, with explicit symmetry breaking for swappable NAND/NOR inputs and
     parallel fingered MOSFETs).
   - **`KLayout` (`KLayout/klayout`, Matthias Köfferlein):** High-performance
     C++/Ruby/Python GDSII and OASIS mask layout viewer, hierarchical boolean
     polygon processor, and scriptable DRC/LVS signoff engine used in `SkyWater
     SKY130`, `GF180MCU`, and `IHP SG13G2` open PDK tapeouts.
   - **Commercial Signoff Suites (`Siemens Calibre nmDRC / nmLVS / xRC`,
     `Cadence Pegasus`, `Synopsys IC Validator`):** Foundry-golden hierarchical
     tapeout signoff engines required by TSMC, Intel, and Samsung for advanced
     FinFET/GAA nodes (`N7`, `N5`, `N3`, `N2`), executing Standard Verification
     Rule Format (`SVRF` / `TVF`) rule decks with tens of thousands of multi-patterning,
     via-enclosure, density, and antenna checks.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - `Magic`'s corner-stitched Manhattan tile plane makes local width/spacing
     DRC checks instantaneous, whereas `KLayout` and `Calibre` use hierarchical
     **Bentley-Ottmann scanline plane-sweep** algorithms over arbitrary-angle
     polygons to scale to multi-billion-transistor GDSII hierarchies.
   - In `Netgen` and `Calibre nmLVS`, graph isomorphism (`Automorphism` /
     Weisfeiler-Lehman partition refinement) can encounter symmetric ambiguity
     on crossbar arrays or parallel transistor fingers, where heuristic tie-breaking
     can mask swapped differential pairs if port labels are missing.
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **LVS Bijection Witness as `BehaviorCodec`:** Instead of trusting `Netgen`'s
     partition-refinement C code, `Netgen` emits the concrete vertex bijection
     $\pi_{\text{nodes}} : V_{\text{layout}} \stackrel{\sim}{\to} V_{\text{schem}}$
     and device bijection $\pi_{\text{dev}} : E_{\text{layout}} \stackrel{\sim}{\to} E_{\text{schem}}$!
     In Anneal, that bijection is directly a `BehaviorCodec` (`decodeOut_encodeOut`
     and `encodeOut_of_decodeOut`), which the Lean 4 kernel checks in $O(|V| + |E|)$
     time!
   - **Scanline DRC & Foundry PDK Waivers (`Partial.ub` + `VerificationResult`):**
     Foundry DRC rules (minimum width $w_{\min}$, spacing $s_{\min}$, enclosure,
     and gate-oxide antenna ratio) define `L_layout.sem`'s well-definedness
     predicate (`defined`), while empirical lithographic process windows (e.g.,
     `.sky130DrcDeckRev1_0`, `.tsmcN3EuvOpticalProximityModel`) are recorded
     positively as `TrustPolicy` waivers in `VerificationResult`.

---

### 7. Domain 7: Quantum Compilers, ZX-Calculus Rewriting, Lattice Surgery, and Real-Time Syndrome Decoding

`Basis: source + documentation + derived`

#### 7.1 Foundational & Automated Quantum Circuit Verifiers: `SQIR` / `VOQC`, `Quipper`, `QWIRE`, `CertiQ`, and `MQT-QCEC`

1. **Goals, problem domain, and target users:**
   - **`SQIR` & `VOQC` (`inQWIRE/SQIR`, Kesha Hietala, Robert Rand, Shih-Han
     Hung, Xiaodi Wu, Michael Hicks at UMD / UChicago, POPL 2021):** `SQIR`
     (Small Quantum Intermediate Representation) is a Coq-embedded quantum
     circuit language with concrete unitary matrix semantics (`UnitarySem` over
     complex $2^n \times 2^n$ matrices via Kraken/Coquelicot) and density-matrix
     superoperator semantics; `VOQC` (Verified Optimizer for Quantum Circuits)
     is a Coq-verified quantum circuit optimizer built on `SQIR` (implementing
     Nam et al.'s `not_propagation`, `hadamard_reduction`, `cancel_single_qubit_gates`,
     `cancel_two_qubit_gates`, and Clifford+$T$ rotation merging, extracted to
     OCaml/Python).
   - **`Quipper` (Peter Selinger, Benoît Valiron et al., PLDI 2013) and `QWIRE`
     (`inQWIRE/QWIRE`, Jennifer Paykin, Robert Rand, Steve Zdancewic at UPenn,
     POPL 2017):** `Quipper` is a scalable Haskell embedded DSL for generating
     hierarchical quantum circuits with dynamic lifting (`box`, `unbox`,
     ancilla initialization/termination assertions), while `QWIRE` embeds a
     linear-type-checked quantum circuit language inside Coq (preventing
     no-cloning violations structurally via linear wire contexts $\Gamma \vdash c : \text{Box}(W_1, W_2)$)
     with denotational superoperator semantics.
   - **`CertiQ` (run-time/compile-time SMT verifier for `Qiskit` passes, Yunong
     Shi et al., OOPSLA 2019) and `MQT-QCEC` (`cda-tum/mqt-qcec`, Lukas Burgholzer
     & Robert Wille at TU Munich):** Automated equivalence checkers for quantum
     compiler passes. `CertiQ` verifies `Qiskit` transpiler passes (`CXCancellation`,
     `CommutativeCancellation`, `Optimize1qGates`) by symbolic matrix-commutation
     invariants discharged via `Z3`; `MQT-QCEC` proves equivalence of compiled
     quantum circuits using **Quantum Decision Diagrams (`QMDD`)**, ZX-calculus
     simplification, and alternating $U_1^\dagger U_2 \to I$ reduction.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - `SQIR` abandoned `QWIRE`'s higher-order phantom/linear wire binding in
     favor of concrete integer qubit indices (`k < dim`) specifically because
     proving multi-qubit gate-commutation and qubit-mapping passes over abstract
     linear contexts in `QWIRE` caused severe Coq proof overhead; in `SQIR`,
     out-of-bounds qubit indices or duplicate two-qubit indices (`CNOT q q`) map
     to the zero matrix $\mathbf{0}_{2^n \times 2^n}$!
   - **Critical Subtlety (`SQIR` Zero-Matrix Degeneracy):** Because `SQIR` maps
     ill-formed gates (such as `CNOT q q` on the same qubit or `q >= n`) to the
     $2^n \times 2^n$ zero matrix $\mathbf{0}$, a naive equivalence check must
     separately prove `uc_well_typed` (`well-formedness`) so a compiler pass
     cannot collapse both sides to $\mathbf{0}$!
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **`Partial.ub` vs. `SQIR`'s Zero Matrix:** In Anneal, an ill-formed quantum
     gate (`CNOT q q`, out-of-bounds qubit index, or non-adjacent hardware
     coupler edge) maps directly to `Partial.ub` (`defined := False`) rather
     than a silent zero matrix $\mathbf{0}$ inside `Out`! Consequently,
     `Compiles L_qasm L_hw` automatically enforces `uc_well_typed` and hardware
     coupling constraints without side-conditions!
   - **Projective Global-Phase Equivalence via `BehaviorCodec`:** Two unitary
     circuits $U_1, U_2 \in U(2^n)$ are physically indistinguishable when
     $U_2 = e^{i\theta} U_1$. Setting `SemObs` to the projective unitary channel
     $\rho \mapsto U \rho U^\dagger$ (or measurement probability distribution)
     and quotienting global phase in `BehaviorCodec` (`obs_decodeOut`) handles
     up-to-global-phase circuit optimization (`VOQC` / `MQT-QCEC`) natively.

#### 7.2 ZX-Calculus Graph Optimizers and Hardware Layout Synthesizers: `PyZX`, `QuiZX`, `Qiskit SABRE`, `TKET`, and `Enfield` / `OLSQ2`

1. **Goals, problem domain, and target users:**
   - **`PyZX` (`zxcalc/pyzx`, Aleks Kissinger & John van de Wetering, 2019) and
     `QuiZX` (`zxcalc/quizx`, Rust rewrite):** Diagrammatic quantum circuit
     optimizers based on the **ZX-calculus** (green $Z$-spiders and red
     $X$-spiders with phases $\alpha \in [0, 2\pi)$ connected by regular and
     Hadamard edges). Reduce ZX-diagrams to **graph-like** form and apply
     **local complementation** (Clifford interior spider elimination),
     **pivoting**, and **phase gadget fusion** to drastically reduce non-Clifford
     $T$-gate counts, followed by **gflow (generalized flow)** circuit extraction.
   - **`Qiskit SABRE` (`Qiskit/qiskit`, Gushu Li, Yufei Ding, Yuan Xie, ASPLOS
     2019), `TKET` (`CQCL/tket`, Seyon Sivarajah et al. at Quantinuum), and
     `Enfield` / `OLSQ2` (`UCLA-VAST/OLSQ2`, Bochen Tan & Jason Cong at UCLA):**
     Hardware topology qubit-mapping and `SWAP`-routing compilers. `SABRE` uses
     bidirectional heuristic lookahead search; `TKET` combines phase-polynomial
     synthesis with bridge/SWAP routing; `OLSQ2` formulates Depth-Optimal and
     SWAP-Optimal Layout Synthesis as an incremental SMT (`Z3`/`Bitwuzla`)
     constraint problem.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - **The ZX Circuit-Extraction & Scalar Bottleneck:** While every quantum
     circuit translates trivially into a ZX-diagram, not every rewritten
     ZX-diagram can be extracted back into a unitary quantum circuit (circuit
     extraction is `#P`-hard in general unless a **gflow** invariant is
     maintained at every rewrite step)! Moreover, if a ZX rewrite rule drops a
     zero scalar factor $0 \cdot D$, it corresponds to post-selecting on an
     impossible measurement outcome (`trace = 0`).
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Preventing Post-Selection / Gflow Extraction Failure (`ProductiveOn` & `BehaviorCodec`):**
     Instead of trusting `QuiZX` or `SABRE`/`TKET`, `QuiZX` emits its sequence
     of spider-fusion, identity, bialgebra, and local-complementation rewrites,
     and `SABRE`/`OLSQ2` emits the initial qubit placement $\pi_0$ and per-layer
     `SWAP` permutations. In Anneal, `ProductiveOn` enforces trace preservation
     ($\operatorname{Tr}(\mathcal{E}(\rho)) = 1$, forbidding zero-scalar
     post-selection cheats), while `BehaviorCodec.decodeOut` maps the routed
     physical qubit wires back through the terminal permutation $\pi_{\text{final}}^{-1}$
     and returns `none` if any 2-qubit gate violates the hardware coupling graph
     $G_{\text{hw}}$.

#### 7.3 Fault-Tolerant Surface-Code Compilers and Real-Time Syndrome Decoders: `Stim`, `PyMatching`, `Fusion Blossom`, and `lsqecc`

1. **Goals, problem domain, and target users:**
   - **`Stim` (`quantumlib/Stim`, Craig Gidney at Google Quantum AI, Quantum
     2021):** Ultra-fast stabilizer circuit simulator and Detector Error Model
     (`DEM`) generator. Uses a **reverse-stabilizer reference-frame sampler**
     With AVX2/AVX-512 SIMD bit-packing to simulate millions of surface-code
     syndrome extraction rounds per second and extract hypergraph fault-to-detector
     models.
   - **`PyMatching` (`oscarhiggott/PyMatching`, Oscar Higgott & Craig Gidney,
     `Sparse Blossom` v2, 2023) and `Fusion Blossom` (`wuyue16pku/fusion-blossom`,
     Yue Wu & Lin Zhong at Yale, 2023):** High-speed Minimum-Weight Perfect
     Matching (`MWPM`) syndrome decoders for surface codes. `PyMatching v2`
     introduces the **Sparse Blossom** algorithm (growing alternating trees
     directly over the detector graph without precomputing all-pairs shortest
     paths), decoding a distance-$d=17$ surface code round in $< 1\,\mu\text{s}$;
     `Fusion Blossom` implements a lock-free parallel Rust blossom solver that
     partitions spacetime syndrome blocks across cores and fuses boundary trees.
   - **`lsqecc` (`latticesurgery-com/lattice-surgery-compiler`, George Watkins,
     Alexandru Paler et al.):** Compiles logical Clifford+$T$ circuits into
     Litinski's **Game of Surface Codes** planar **Lattice Surgery** instructions
     (multi-patch $XX/ZZ$ merges, splits, patch rotations, and magic-state
     distillation factory routing buses).
2. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Gottesman-Knill Tableau as Exact Upward Abstraction (`Abstracts L_stim L_hilbert`):**
     For Clifford stabilizer circuits with Pauli noise channels, `Stim`'s
     $O(n^2)$ binary symplectic tableau (`L_stim`) is a sound and exact upward
     abstraction of the $2^n \times 2^n$ density-matrix Hilbert space (`L_hilbert`)!
   - **Hard-Real-Time Rust Syndrome Decoding (`Fusion Blossom` in Anneal):**
     `Fusion Blossom` is already written in Rust! Verifying a zero-allocation
     Rust `Sparse Blossom` or `Union-Find` decoder in Anneal proves **both**
     algebraic syndrome correction ($\forall e$ with $|e| \le \lfloor(d-1)/2\rfloor$,
     $\partial(\text{decode}(\partial e)) = \partial e$ and $e \oplus \text{decode}(\partial e) \in \mathcal{S}$)
     **and** deterministic sub-microsecond WCET (`defined` requires completing
     within the $1\,\mu\text{s}$ superconducting cycle budget to prevent the
     Terhal-DiVincenzo decoding backlog)!

---

### 8. Domain 8: Analog/Mixed-Signal Verification, Real-Number Modeling, Layout Generators, and Neuromorphic Computing

`Basis: source + documentation + derived`

#### 8.1 Analog/Mixed-Signal (AMS) Reachability, SPICE Simulators, and Real-Number Model Compilers: `SpaceEx-AMS` / `CORA-AMS` / `Ariadne`, `Xyce` / `Ngspice`, `SVReal` / `msdsl` / `Dragonfly`, and `DELSIG`

1. **Goals, problem domain, and target users:**
   - **`SpaceEx-AMS` / `CORA-AMS` and `Ariadne` (`ariadne-cps/ariadne`, Pieter
     Collins, Luca Geretti, Tiziano Villa et al.):** Rigorous formal verification
     tools for analog and mixed-signal circuits (tunnel-diode oscillators,
     charge-pump Phase-Locked Loops, $\Delta\Sigma$ modulators, DC-DC buck
     converters). `Ariadne` implements **Computable Analysis** in C++ (exact
     real numbers, validated Taylor function patches, and rigorous lower/upper
     reachability approximations over hybrid differential inclusions).
   - **`Xyce` (`Xyce/Xyce`, Sandia National Laboratories) and `Ngspice`
     (`ngspice/ngspice`):** Open-source transistor-level SPICE circuit simulators
     solving nonlinear Differential-Algebraic Equations (DAEs:
     $\frac{d}{dt} q(x(t)) + f(x(t)) = b(t)$ via Modified Nodal Analysis `MNA`,
     Newton-Raphson iteration, and Gear/Trapezoidal integration with `BSIM4` /
     `BSIM-CMG` / `PSP` compact MOSFET models; `Xyce` scales to millions of
     devices via `Trilinos` MPI parallel solvers).
   - **`msdsl` (`sgherbst/msdsl`), `SVReal` (`sgherbst/svreal`), and `Dragonfly`
     (Steven Herbst & Mark Horowitz at Stanford, DAC/ICCAD 2018–2022):**
     Mixed-Signal Domain-Specific Language (`msdsl`) and synthesizable
     SystemVerilog Real-Number Modeling (`SVReal`) compilers. Automatically
     extract piecewise-polynomial spline approximations and fixed-point digital
     emulation models (`svreal` fixed-point `real` macros) from analog SPICE
     subcircuits so analog front-ends can run at megahertz speeds on FPGAs
     or inside digital RTL simulators (`Verilator`, `VCS`, `Xcelium`).
   - **`DELSIG` (Richard Schreier's Delta-Sigma Toolbox for MATLAB / `python-delsig`):**
     The industry-standard synthesis and stability analysis toolkit for
     continuous-time and discrete-time $\Delta\Sigma$ Analog-to-Digital
     Converters (synthesizing Noise Transfer Functions `NTF` via Lee's rule of
     thumb $\|H_\infty\| < 1.5$, dynamic-range scaling, and loop-filter CIFB/CIFF
     topologies).
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - `DELSIG`'s Lee criterion ($\|H_\infty\| < 1.5$) is a *heuristic* that does
     not guarantee non-overload stability for high-order ($\ge 3$rd order) single-bit
     $\Delta\Sigma$ modulators: rare low-frequency input sequences can still drive
     internal integrators into rail clipping saturation and chaotic oscillation!
   - `msdsl` and `SVReal` accelerate mixed-signal verification by $10^3\times$–$10^5\times$
     compared to `Xyce`/`Ngspice`, but their spline/fixed-point Real-Number
     Models drop high-order nonlinearities unless enclosed by rigorous interval
     error bounds.
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Sound Real-Number Modeling via `Abstracts` (`Abstracts L_svreal L_spice codec_ams`):**
     An `msdsl`/`SVReal` behavioral macro-model endowed with conservative
     interval spline remainders (`L_svreal`) is proved in Anneal to
     over-approximate the transistor DAE (`L_spice`) across all PVT corners,
     transferring full-chip SoC mixed-signal verification guarantees back to the
     analog circuit!
   - **Threshold-Window `decodeOut = none` at the ADC/Digital Boundary:**
     `BehaviorCodec.decodeOut` maps continuous analog voltages $V \in \mathbb{R}$
     at digital sample strobes to `some true` ($V \ge V_{IH}$), `some false`
     ($V \le V_{IL}$), and **`none` whenever $V \in (V_{IL}, V_{IH})$** (the
     forbidden indeterminate threshold window)!
   - **Ruling Out Parasitic Zero-Current Startup Lockup (`ProductiveOn`):**
     Self-biased bandgap references and oscillators simulated in `Xyce` often
     possess a degenerate zero-current DC equilibrium; `ProductiveOn` over power-on
     ramp queries forces the startup circuit to exit the degenerate basin.

#### 8.2 Automated Analog Layout Generators and Neuromorphic Compilers: `BAG2`, `ALIGN`, `MAGICAL`, `Lava`, `Brian2`, and `Nengo`

1. **Goals, problem domain, and target users:**
   - **`BAG2` (`ucb-art/BAG_framework`, Elad Alon, Bora Nikolić, Vladimir
     Stojanović at UC Berkeley), `ALIGN` (`ALIGN-analoglayout/ALIGN-public`,
     Sachin Sapatnekar et al. at UMN / Intel, DARPA IDEA), and `MAGICAL`
     (`magical-eda/MAGICAL`, David Z. Pan's group at UT Austin):** Automated
     analog IC layout synthesis frameworks. `BAG2` codifies expert analog layout
     generators in Python parameterized across PDKs; `ALIGN` and `MAGICAL`
     automatically detect differential-pair, current-mirror, and common-centroid
     symmetry constraints from raw SPICE netlists and perform symmetry-constrained
     analog placement and routing.
   - **`Lava` (`lava-nc/lava`, Intel Labs for `Loihi 2` neuromorphic chips),
     `Brian2` (`brian-team/brian2`, Marcel Stimberg, Romain Brette, Dan Goodman),
     and `Nengo` (`nengo/nengo`, Chris Eliasmith's group at Waterloo / ABR):**
     Spiking Neural Network (SNN) and neuromorphic compilation frameworks.
     `Brian2` compiles symbolic membrane differential equations into C++/Cython/CUDA;
     `Nengo` implements the **Neural Engineering Framework (NEF)** to compile
     dynamical systems $\dot{x} = f(x)$ into populations of spiking neurons via
     optimal linear decoders; `Lava` compiles asynchronous communicating
     spiking `Processes` down to fixed-point `Loihi 2` neurocores communicating
     over Address-Event Representation (`AER`) packet meshes.
2. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Symmetry-Preserving Analog Layout (`Compiles` + `BehaviorCodec`):** In
     `ALIGN` and `MAGICAL`, differential-pair mismatch ($C_{p,1} \neq C_{p,2}$)
     destroys common-mode rejection ratio (CMRR). Encoding reflection symmetry
     $\sigma(P_1) = P_2$ into `L_analogLayout`'s `defined` predicate ensures
     any asymmetric route emitted by an untrusted placer fails `Compiles`!
   - **NEF Dynamical Abstraction (`Abstracts`) and `Lava` Fixed-Point/AER
     Compilation (`Compiles`):** `Nengo`'s NEF theorem—that a population of $N$
     spiking Leaky-Integrate-and-Fire neurons implements a continuous ODE
     $\dot{x} = A x + B u$ up to synaptic filter noise $\epsilon(N)$—maps to
     `Abstracts L_ode L_snn`, while compiling `Lava` floating-point SNN models
     into 8-bit `Loihi 2` fixed-point neurocores with non-dropping `AER` packet
     routing maps directly to `Compiles L_lavaSpec L_loihiHw`.

---

### 9. Domain 9: Silicon Photonics, Programmable Optical Interferometer Meshes, and Photonic Quantum Simulators

`Basis: source + documentation + derived`

#### 9.1 Scattering-Matrix Circuit Simulators, Optical Neural Network Compilers, and Photonic PDK Layout: `SAX`, `Simphony`, `Neuroptica`, `TorchONN`, `Lightridge`, `GDSFactory`, and `Nazca`

1. **Goals, problem domain, and target users:**
   - **`SAX` (`flaport/sax`, Floris Laporte) and `Simphony`
     (`BYUCamachoLab/simphony`, Ryan Camacho's group at BYU):** Frequency-domain
     Scattering-Matrix ($S$-parameter) circuit simulators for Photonic
     Integrated Circuits (PICs). Given a netlist of multi-port optical components
     (waveguides, directional couplers, microring resonators, grating couplers)
     characterized by wavelength-dependent complex scattering matrices
     $S(\lambda) \in \mathbb{C}^{P \times P}$, `SAX` (built on Google `JAX` for
     GPU acceleration and automatic differentiation) and `Simphony` compute the
     composite network $S$-matrix via **Redheffer star products** / Mason-graph
     interconnect reduction.
   - **`Neuroptica` (`fancompute/neuroptica`, Shanhui Fan's group at Stanford),
     `TorchONN` (`GuGroup/TorchONN`, Jiaqi Gu & David Z. Pan), and `Lightridge`
     (`lightelligence/lightridge`):** Simulation and compilation frameworks for
     coherent Optical Neural Networks (ONNs). Compile $N \times N$ unitary/linear
     weight matrices $W = U \Sigma V^\dagger$ into triangular (**Reck et al.,
     1994**), rectangular (**Clements et al., Optica 2016**), or butterfly
     (**MZI-FFT**) meshes of thermo-optic / electro-optic Mach-Zehnder
     Interferometers (`MZIs`), modeling phase-shifter quantization, thermal
     crosstalk matrices $K_{\text{thermal}}$, and non-50:50 beam-splitter
     fabrication errors.
   - **`GDSFactory` (`gdsfactory/gdsfactory`, Joaquin Matres et al.) and `Nazca`
     (`nazca-design.org`):** Python-driven photonic layout, curvilinear routing
     (clothoid/Euler bends to minimize bend-mode transition loss, Manhattan
     waveguide bundle routing with optical path-length matching), connectivity
     pin checking, and DRC/LVS integration with `KLayout` and `SAX`.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - **Clements/Reck Decomposition Under Imperfect Beam Splitters:** The
     Clements algorithm factors any $U \in U(N)$ into $N(N-1)/2$ two-mode Givens
     rotations $T_{m,n}(\theta, \phi)$ assuming ideal 50:50 directional couplers.
     When wafer-scale waveguide width variations shift the splitting ratio to
     $50\% \pm \delta$ (e.g., $54:46$), a standard 2-coupler MZI can no longer
     reach zero cross-bar transmission ($\theta \in [2|\delta|, \pi - 2|\delta|]$),
     leaving a hole of **unreachable unitary matrices** in $U(N)$!
   - **Curvilinear Continuity vs. Manhattan Discretization in `GDSFactory`:**
     Photonic waveguides are sensitive to 1 nm sidewall roughness and curvature
     discontinuities ($\kappa(s)$ jumps at straight-to-circular-arc junctions
     excite higher-order TM/TE modes and radiative loss).
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Verified Clements Factorization & Redheffer Passivity (`Compiles L_unitary L_mziMesh`):**
     An untrusted Python compiler (`Neuroptica` / `TorchONN` / `SAX`) computes
     phase-shifter angles $(\theta_{ij}, \phi_{ij})$ and thermal-crosstalk
     pre-compensation voltages $\mathbf{V} = K_{\text{thermal}}^{-1} \boldsymbol{\theta}$;
     a Lean 4 checker in `theory/` verifies that the Redheffer star product of
     the MZI transfer matrices equals $U$ up to calibrated insertion-loss
     attenuation $\eta$ and satisfies passivity ($\|S(\lambda)\|_2 \le 1$, no
     spurious gain) and laser back-reflection limits ($|S_{ii}|^2 \le R_{\max}$).
   - **Exposing Unreachable Unitary Holes under Fabrication Error (`ProductiveOn`):**
     When directional couplers have fabrication error $\delta > 0$, requiring
     `ProductiveOn` over the declared matrix domain forces the photonic compiler
     either to restrict `InhabitedPre` to the proved reachable submanifold
     $\mathcal{U}_\delta \subset U(N)$ or to compile to a redundant 3-coupler /
     double-MZI cell (`Miller` / `Suzuki` architecture) that provably restores
     100% $U(N)$ reachability!
   - **Projective Attenuation-Normalized `BehaviorCodec`:** `decodeOut` scales
     the output complex field vector $\mathbf{E}_{\text{out}}$ by $\eta^{-1}$
     when the link insertion loss satisfies $\eta \ge \eta_{\min}$, and returns
     `none` whenever insertion loss, polarization crosstalk, or back-reflection
     violates the optical link budget.

#### 9.2 Full-Wave Electromagnetic FDTD Solvers and Photonic Quantum Frameworks: `Meep`, `Tidy3D`, `Strawberry Fields`, and `Perceval`

1. **Goals, problem domain, and target users:**
   - **`Meep` (`NanoComp/meep`, Steven G. Johnson, Ardavan Oskooi et al. at MIT)
     and `Tidy3D` (`flexcompute/tidy3d`, Shanhui Fan, Zongfu Yu et al. at
     Flexcompute):** Full-wave 3D Finite-Difference Time-Domain (`FDTD`) Maxwell
     equation solvers ($\nabla \times \mathbf{E} = -\mu \frac{\partial \mathbf{H}}{\partial t}$,
     $\nabla \times \mathbf{H} = \varepsilon \frac{\partial \mathbf{E}}{\partial t} + \mathbf{J}$)
     on staggered **Yee lattices** with Perfectly Matched Layer (`PML`) absorbing
     boundaries and adjoint-variable inverse design (`meep.adjoint` for
     topology-optimized photonic splitters and metalenses).
   - **`Strawberry Fields` (`XanaduAI/strawberryfields`, Xanadu) and `Perceval`
     (`Quandela/Perceval`, Quandela):** Photonic quantum compilation and
     simulation stacks. `Strawberry Fields` targets **Continuous-Variable (CV)**
     Gaussian boson sampling and Gottesman-Kitaev-Preskill (`GKP`) states via
     $2N \times 2N$ symplectic covariance matrices (`The Walrus`); `Perceval`
     targets **Discrete-Variable (DV)** single-photon linear optical circuits
     where multi-photon transition amplitudes are governed by matrix **permanents**
     ($\operatorname{Perm}(U_{S,T})$, computed via Ryser's / Glynn's algorithm).
2. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Multi-Fidelity Electromagnetic-to-Circuit Abstraction (`Abstracts L_sax L_meep`):**
     Component $S$-parameters extracted from 3D `Meep`/`Tidy3D` FDTD Yee-grid
     simulations carry Courant-Friedrichs-Lewy (`CFL`) dispersion and grid-truncation
     error bounds $\epsilon_{\text{FDTD}}$. In Anneal, `Abstracts` formalizes
     how a `SAX` circuit-level $S$-matrix interval model soundly encloses the
     coupled-mode behavior of the 3D Maxwell geometry, while empirical silicon
     nitride / SOI refractive-index dispersion tables (`.sellmeierSi3N4Fit`) are
     tracked positively in `VerificationResult.waived`.

---

### 10. Domain 10: Programmable Metamaterials, Phased-Array Wave-Shaping, Origami Mechanics, and Soft Robotics

`Basis: source + documentation + derived`

#### 10.1 Acoustic/Electromagnetic Wave-Field Solvers and Bandgap Photonic/Phononic Crystals: `k-Wave`, `Bempp-cl`, and `MPB`

1. **Goals, problem domain, and target users:**
   - **`k-Wave` (`ucl-bug/k-wave`, Bradley Treeby & Ben Cox at UCL / Brno):**
     Open-source MATLAB and C++/CUDA toolbox for time-domain nonlinear acoustic
     and ultrasound wave propagation in heterogeneous, absorbing biological media
     (used extensively in **High-Intensity Focused Ultrasound `HIFU` thermal
     ablation**, transcranial focused ultrasound neuromodulation, and
     photoacoustic tomography). Uses the **$k$-space pseudospectral method**
     (computing spatial gradients via 3D Fast Fourier Transforms `FFT` and
     applying an exact $k$-space propagator $\operatorname{sinc}(c_0 k \Delta t / 2)$
     to suppress numerical dispersion at 2 grid points per wavelength).
   - **`Bempp-cl` (`bempp/bempp-cl`, Timo Betcke & Matthew Scroggs at UCL):**
     OpenCL/Python **Boundary Element Method (BEM)** package solving acoustic
     Helmholtz ($\nabla^2 u + k^2 u = 0$) and electromagnetic Maxwell surface
     integral equations using Calderón preconditioning and Fast Multipole /
     Hierarchical Matrix ($\mathcal{H}$-matrix) compression.
   - **`MPB` (`NanoComp/mpb`, MIT Photonic-Bands, Steven G. Johnson & J. D.
     Joannopoulos):** Computes definite-frequency eigenstates and dispersion
     band structures $\omega_n(\mathbf{k})$ of periodic dielectric and
     metamaterial lattices by preconditioned conjugate-gradient minimization of
     the Maxwell Rayleigh quotient in a plane-wave (Bloch-Floquet) basis.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - **Safety-Critical HIFU Keep-Out Verification (`k-Wave`):** In transcranial
     or abdominal `HIFU` surgery, an array of $256$–$1024$ ultrasonic transducer
     elements focuses acoustic energy through the skull or rib cage onto a deep
     tumor. If constructive sidelobe interference occurs on the skull bone, rib
     cage, or an adjacent major blood vessel, catastrophic thermal necrosis or
     inertial cavitation occurs! Evaluating the wavefield only at discrete grid
     voxels can miss sub-wavelength interference peaks between grid nodes.
   - **Bandgap Certification (`MPB`):** `MPB` computes approximate eigenvalues
     at discrete $\mathbf{k}$-points along the irreducible Brillouin zone
     perimeter ($\Gamma - X - M - \Gamma$); without Weyl eigenvalue perturbation
     bounds and Lipschitz continuity certificates over the interior of the
     Brillouin zone, narrow band-crossings can be missed.
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **Continuous Keep-Out Volume Safety via Octree Interval Green's Functions
     (`Abstracts L_octree L_helmholtz` & `Partial.ub`):**
     In Anneal, collateral heating or cavitation in an Organ-At-Risk
     ($\exists \mathbf{r} \in \Omega_{\text{OAR}},\, |p(\mathbf{r})| > p_{\text{safe}}$)
     is `Partial.ub` (`defined = False`). An untrusted `k-Wave` or `Bempp-cl`
     inverse-design optimizer synthesizes transducer phases/amplitudes
     $\mathbf{w} \in \mathbb{C}^M$; a verified Lean 4 checker in `theory/`
     evaluates the Rayleigh-Sommerfeld / Helmholtz Green's function integral
     over an adaptive 3D interval octree covering $\Omega_{\text{OAR}}$, proving
     continuous-space safety across the entire volume!
   - **Preventing the Zero-Power Phased-Array Cheat (`ProductiveOn`):**
     As identified in Domain 10 of the architecture catalog, the trivial way to
     satisfy $\forall \mathbf{r} \in \Omega_{\text{OAR}},\, |p(\mathbf{r})| \le p_{\text{safe}}$
     is to set transducer weights to zero ($\mathbf{w} = \mathbf{0}$)! Requiring
     `ProductiveOn` alongside the `SemObs` focal-intensity target
     ($|p(\mathbf{r}_{\text{tumor}})| \ge p_{\text{therapeutic}}$) forces the
     synthesized phased array to deliver therapeutic focal energy while staying
     100% safe in all keep-out zones.

#### 10.2 Origami/Auxetic Metamaterials, Differentiable Soft Robotics, Topology Optimization, and MEMS: `MERLIN2`, `Origami Simulator`, `Crane`, `SOFA`, `DiffTaichi`, `TopOpt`, and `Sugar`

1. **Goals, problem domain, and target users:**
   - **`MERLIN2` (`paulino-group/MERLIN2`, Ke Liu & Glaucio H. Paulino at
     Georgia Tech / Princeton), `Origami Simulator` (`amandaghassaei/OrigamiSimulator`,
     Amanda Ghassaei, Erik Demaine, Neil Gershenfeld at MIT CBA), and `Crane`
     (Kai Suto, Yuta Noma, Kotaro Tanimichi, Tomohiro Tachi at U. Tokyo):**
     Nonlinear structural and kinematic simulators/compilers for rigid-foldable
     and bistable/non-rigid origami metamaterials (Miura-ori, Kresling towers,
     deployable space solar arrays). `MERLIN2` models panels via **bar-and-hinge**
     reduced-order nonlinear mechanics solved with the **Modified Generalized
     Displacement Control Method (`MGDCM`)** arc-length solver to trace
     snap-through buckling and multistable energy landscapes; `Origami Simulator`
     solves parallel GPU mass-spring-crease constraints; `Crane` compiles
     3D developable/rigid-foldable crease patterns under Kawasaki-Justin and
     Maekawa flat-foldability constraints.
   - **`SOFA` (`sofa-framework/sofa`, INRIA) and `DiffTaichi`
     (`taichi-dev/difftaichi`, Yuanming Hu et al. at MIT, ICLR 2020):**
     Soft-tissue / soft-robotics Finite Element Method (`FEM`) and Material
     Point Method (`MPM`) frameworks. `SOFA` provides real-time corotational
     and hyperelastic (`Neo-Hookean`, `Mooney-Rivlin`) FEM with Lagrange-multiplier
     contact for cable/pneumatic soft robots; `DiffTaichi` provides a
     source-to-source differentiable programming compiler emitting analytical
     forward/backward Megakernels for soft actuators.
   - **`TopOpt` (`topopt/TopOpt_in_PETSc`, Niels Aage, Ole Sigmund at DTU) and
     `Sugar` (Jason Vaughn Clark, Ningning Zhou, Kristofer S. J. Pister at UC
     Berkeley):** `TopOpt` performs giga-voxel 3D structural topology optimization
     using **SIMP (Solid Isotropic Material with Penalization)** and the
     **Method of Moving Asymptotes (`MMA`)**; `Sugar` simulates Micro-Electro-Mechanical
     Systems (`MEMS` comb-drives, electrostatic torsional micromirrors,
     gyroscopes) via Modified Nodal Analysis of coupled electromechanical beams
     and gaps.
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - **Self-Intersection & Kinematic Bifurcation in Origami (`MERLIN2`, `Crane`):**
     Bar-and-hinge models (`MERLIN2`) track local crease dihedral angles and
     panel bending without global triangle-triangle collision checks, allowing a
     simulated snap-through path to pass two panels ghost-like through each other
     in 3D space! Furthermore, at flat unfolded states ($\theta = \pi$), the
     compatibility Jacobian drops rank (mountain/valley kinematic bifurcation).
   - **Checkerboard & Zero-Width Hinge Pathologies in `TopOpt` (SIMP):**
     Unregularized SIMP topology optimization produces non-manufacturable
     checkerboard patterns or one-pixel point hinges that look stiff in coarse
     finite elements but snap immediately under real stress concentrations
     (von Mises stress $\sigma_v > \sigma_{\text{yield}}$).
   - **Electrostatic Pull-In Instability in `Sugar` (MEMS):** In electrostatic
     parallel-plate or torsional MEMS actuators ($F_{\text{elec}} = \frac{\varepsilon A V^2}{2(g_0 - x)^2}$
     vs. $F_{\text{spring}} = k x$), once displacement exceeds $x_{\text{PI}} = \frac{1}{3} g_0$
     (a saddle-node bifurcation at voltage $V_{\text{PI}} = \sqrt{\frac{8 k g_0^3}{27 \varepsilon A}}$),
     the restoring equilibrium vanishes and the plates slam together catastrophically!
3. **Exact mapping onto Anneal's 4 `trusted/` primitives:**
   - **MEMS Saddle-Node Pull-In and Structural Yield as `Partial.ub` (`defined = False`)
     + `ProductiveOn`:**
     At the MEMS saddle-node pull-in voltage $V > V_{\text{PI}}$, the static
     equilibrium relation $\frac{1}{2}\frac{\varepsilon A V^2}{(g_0 - x)^2} = k x$
     has **zero real solutions** in $[0, g_0)$! Thus in Anneal, crossing $V_{\text{PI}}$
     simultaneously violates `defined` (`Partial.ub`: snap-in contact short) and
     `ProductiveOn` (non-existence of a stable equilibrium outcome $x \in [0, g_0)$).
   - **Origami Kawasaki-Maekawa & Non-Self-Intersection Certificates (`Compiles`):**
     `Crane` or `MERLIN2` generates a folding actuation trajectory; a Lean 4
     verifier checks exact loop-closure rotation products $\prod R(\gamma_i, \rho_i) = I_3$
     at every interior vertex, verifies that panel facets remain pairwise disjoint
     via separating planes (`defined = True`), and confirms that the target
     deployed 3D shape is reached (`obs_decodeOut`).

---

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **VeriPhy / ModelPlex (CMU), Hylaa / XSpeed, Fossil 2.0 (`oxford-
  oxcav/fossil`), LyZNet, Verisig 2.0, POLAR, and TinyMPC:** Verified
  $d\mathcal{L}$-to-CakeML runtime monitors, high-dimensional hybrid
  reachability, CEGIS Lyapunov/CBF synthesizers, and embedded MPC codegen.
- **ARMOUR / RTD (`roahmlab/armour-dev`), SaRA (`Reach-SDP`), RobCoGen, IRIS-NP,
  openGJK, Coq-Robot (`affeldt-aist/robot`), and R2U2 (`r2u2.github.io`):**
  Polynomial-zonotope manipulator reachability, ISO/TS 15066 human-robot safety
  occupancy, Coq $SE(3)$ kinematics, and NASA Lunar Gateway MLTL runtime
  assurance.
- **AGREE / Resolute, NASA `DAIDALUS` / `PRECiSA`, COAST (`byuccl/coast`),
  SymPLC / VETPLC / K-ST, OVADO, and SafeCap:** AADL assume-guarantee contracts,
  PVS airborne well-clear separation, LLVM TMR radiation fault-tolerance passes,
  and formal PLC/railway route-table verifiers.
- **Google XLS (`google/xls`), Dynamatic (`dynamatic.epfl.ch`), Fika /
  SilverOak, UCLID5 / ILAng, Workcraft / Petrify, and XMAS / VeriNoC:** Verified
  DSLX-to-RTL synthesis, latency-insensitive elastic HLS, Burch-Dill ILA
  verifiers, QDI async circuit synthesis, and NoC deadlock verifiers.
- **VyZX (`inQWIRE/VyZX`), Qbricks (`qbricks.github.io`), Giallar, Quartz /
  Synthetiq, Feynman (`meamy/feynman`), and `gridsynth`:** Coq-verified ZX-
  calculus rewrites, Why3 path-sum quantum verification, SMT Qiskit transpiler
  verification, and optimal Clifford+$T$ synthesis.
- **Coho / Checkmate / LEMA (analog reachability), Ceviche / LumOpt (adjoint
  photonics), Focus / mSOUND (HIFU), and Sionna RT (6G RIS):** Projective
  polyhedral analog reachability, electromagnetic adjoint optimization, and
  acoustic/RF phased-array envelope verifiers.

## Boundaries

To prevent future agents from over-generalizing the findings in this report,
we record the following explicit scope boundaries according to `FORMAT.md`:

- **Not examined (`not examined`) — Direct execution of commercial closed-source
  EDA, avionics, and rail binaries:** Commercial proprietary tools surveyed in
  this report (`Ansys SCADE Suite KCG`, `MathWorks Polyspace`, `AbsInt Astrée`
  and `aiT WCET`, `Prover iLock`/`Prover Certifier`, `Cadence JasperGold`/`Conformal`/`Pegasus`,
  `Synopsys VC Formal`/`SpyGlass`/`IC Validator`, `Siemens Calibre`, and
  `Mathematica` QE inside `KeYmaera X`) were analyzed via their published
  normative standards (`DO-178C`/`DO-333`, `EN 50128`, `IEC 61131-3`, `IEEE 1800`
  SVA, `IEEE 1801` UPF), academic architectural papers, and public interface
  specifications rather than local binary execution.
- **Known not to apply (`known not to apply`) — Unbounded coinductive stream or
  hyperproperty preservation without `SemObs` instrumentation:** As established in
  `reports/anneal-behavior-codec-and-progress-refinement-2026/`, Anneal's
  `EventualBehaviorOf` captures all-prefix safety (`∀ n, ... out.isSafe`) and
  eventual termination (`∃ n, ... .terminated`) constructively without
  coinduction. However, general $\omega$-regular fairness properties of the form
  $\square \lozenge P$ ("infinitely often $P$" over diverging executions) or
  probabilistic quantum diamond-norm bounds ($\|\mathcal{E}_1 - \mathcal{E}_2\|_\diamond \le \epsilon$)
  do not reduce to plain boolean trace equality on `.diverges` unless quantitative
  progress counters, region-entry milestones, or approximate error budgets $\epsilon$
  are explicitly included in `Out` and `SemObs`.
- **Unsupported (`unsupported`) — Unverified floating-point SDP/LP/NLP outputs
  as direct Lean 4 proofs:** Raw IEEE-754 floating-point outputs from `Mosek`,
  `OSQP`, `Ipopt`, `Marabou`, `DREAMPlace`, or `SAX` cannot be trusted directly
  as proof witnesses in Lean 4 due to rounding residuals; they must be paired
  with a rational/dyadic or interval-arithmetic reconstruction step (e.g.,
  exact rational $LDL^T$ checking for SOS barriers, Farkas dual vectors for
  `Marabou`, or interval Picard contraction for `Flow*`/`CORA`) inside
  `theory/`, or else explicitly waived via `VerificationResult.waived`.

---

## Evidence

1. **Anneal Trusted Refinement & Small-Step Core (`source` + `execution`):**
   - Repository: `joshlf/anneal` at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`
     (`trusted/lean/Trusted/Refinement.lean:201-473`,
     `trusted/lean/Trusted/StepResult.lean:55-200`) and
     `4f45f0a391a921ced9c9dc773b9a040dbc215d14`
     (`trusted/lean/Trusted/X86Semantics.lean`).
   - Companion reference packages published at `df55c524a051d59e7dd35564f282b30d29133392`
     on `refs/heads/reference` (observed `2026-10-31`):
     - `reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean`
       (mechanizing `EventualBehaviorOf` and `PartialBehaviorCodec`),
     - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/support/ProofGatedCompilationAndTrustPolicy.lean`
       (mechanizing proof-gated cut elimination and positive per-obligation
       waiver scoping), and
     - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/StructuralExternalCallAndCanaries.lean`
       (mechanizing `StepResult.externalCall` with zero `Classical.choice`).
2. **Primary Upstream Repositories & Normative Specifications Across Domains 1–10
   (`documentation` + `normative`):**
   - *Domain 1:* `LS-Lab/KeYmaeraX-release` (`edu.cmu.cs.ls.keymaerax.core`,
     Platzer CADE 2015 / J. ACM 2017); `chenxin415/flowstar` (Chen, Ábrahám,
     Sankaranarayanan CAV 2013); `TUMcps/CORA` (Althoff ARCH-COMP 2024–2026);
     `JuliaReach/ReachabilityAnalysis.jl`; `dreal/dreal4` (Gao, Kong, Clarke
     CADE 2013); `soarlab/FPTaylor` (Solovyev et al. TOPLAS 2018);
     `malyzajko/daisy` (Darulova et al. TACAS 2018); `osqp/osqp` (Stellato et al.
     Math. Prog. Comp. 2020); `jump-dev/SumOfSquares.jl`; `hypro/hypro`.
   - *Domain 2:* `RobotLocomotion/drake` (Tedrake et al., `GcsTrajectoryOptimization`);
     `stack-of-tasks/pinocchio` (Carpentier et al. SII 2019); `loco-3d/crocoddyl`
     (Mastalli et al. ICRA 2020); `NVlabs/curobo` (Sundaralingam et al. ICRA
     2023); `coal-library/coal` (formerly `humanoid-path-planner/hpp-fcl`);
     `ompl/ompl`; `moveit/moveit2`; `snape/RVO2` (van den Berg et al. ISRR
     2009); `leggedrobotics/ocs2`; `ethz-adrl/towr` (Winkler et al. RA-L 2018).
   - *Domain 3:* `INRIA/velus` (Bourke et al. PLDI 2017 / 2020 / 2023);
     `PARKAS/heptagon`; `Copilot-Language/copilot` (Perez, Dedden, Goodloe NASA
     FM 2020); `NASA-SW-VnV/fret` & `nasa/ogma`; `NeuralNetworkVerification/Marabou`
     (Katz et al. CAV 2017 / CAV 2019 / CAV 2024); `NASA-SW-VnV/CoCoSim`;
     `kind2-mc/kind2` (Champion et al. CAV 2016); `nasa/fprime`; `nasa/cFS`;
     `CS-SI/Orekit`; RTCA `DO-178C` / `DO-333`.
   - *Domain 4:* `plcverif-oss/cern.plcverif` (Darvas et al. ICALEPCS 2019);
     `plc-lang/rusty` (`RuSt` IEC 61131-3 LLVM compiler); `nucleron/matiec`;
     `thiagoralves/OpenPLC_v3`; CENELEC `EN 50128` (`SIL 4` `Prover iLock` /
     `Prover Certifier` & `Atelier B` / `ClearSy`).
   - *Domain 5:* `YosysHQ/yosys`, `YosysHQ/sby`, & `berkeley-abc/abc`;
     `mit-plv/koika` (Bourgeat et al. PLDI 2020); `mit-plv/kami` (Choi et al.
     ICFP 2017); `ymherklotz/vericert` (Herklotz et al. OOPSLA 2021 / POPL 2024);
     `ferrandi/PandA-bambu`; `cucapra/calyx` (Nigam et al. ASPLOS 2021);
     `llvm/circt`; `parallaxsw/OpenSTA`; `asyncvlsi/act` (Manohar).
   - *Domain 6:* `The-OpenROAD-Project/OpenROAD` (Kahng et al.);
     `RTimothyEdwards/magic` & `RTimothyEdwards/netgen`; `KLayout/klayout`;
     `limbo018/DREAMPlace` (Lin et al. DAC 2019); `cuhk-eda/CuGR`.
   - *Domain 7:* `inQWIRE/SQIR` & `VOQC` (Hietala et al. POPL 2021);
     `inQWIRE/QWIRE` (Paykin et al. POPL 2017); `zxcalc/pyzx` & `zxcalc/quizx`
     (Kissinger & van de Wetering 2020); `quantumlib/Stim` (Gidney Quantum 2021);
     `oscarhiggott/PyMatching` (Higgott & Gidney 2023); `wuyue16pku/fusion-blossom`
     (Wu & Zhong 2023); `Qiskit/qiskit` (`SABRE`); `CQCL/tket`; `UCLA-VAST/OLSQ2`;
     `latticesurgery-com/lattice-surgery-compiler` (`lsqecc`); `cda-tum/mqt-qcec`.
   - *Domain 8:* `ariadne-cps/ariadne` (Collins et al.); `Xyce/Xyce`;
     `sgherbst/msdsl` & `sgherbst/svreal` (Herbst & Horowitz); `ucb-art/BAG_framework`;
     `ALIGN-analoglayout/ALIGN-public`; `magical-eda/MAGICAL`; `lava-nc/lava`;
     `brian-team/brian2`; `nengo/nengo`.
   - *Domain 9:* `flaport/sax`; `BYUCamachoLab/simphony`; `fancompute/neuroptica`;
     `GuGroup/TorchONN`; `lightelligence/lightridge`; `gdsfactory/gdsfactory`;
     `NanoComp/meep`; `flexcompute/tidy3d`; `XanaduAI/strawberryfields`;
     `Quandela/Perceval`; Clements et al. (Optica 2016).
   - *Domain 10:* `ucl-bug/k-wave` (Treeby & Cox); `bempp/bempp-cl`;
     `NanoComp/mpb`; `paulino-group/MERLIN2` (Liu & Paulino);
     `amandaghassaei/OrigamiSimulator`; `sofa-framework/sofa`;
     `taichi-dev/difftaichi` (Hu et al. ICLR 2020); `topopt/TopOpt_in_PETSc`.

---

## Revalidation

To revalidate the structural mappings and corpus invariants of this report after
changes to Anneal's `trusted/lean/` primitives or when instantiating a concrete
domain verifier in `theory/`:

1. **Validate the four `trusted/lean/` primitive mechanizations in Lean 4.34.1:**
   Run the standalone Lean 4 kernel checks preserved in the companion packages:
   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/support/ProofGatedCompilationAndTrustPolicy.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/StructuralExternalCallAndCanaries.lean
   ```
2. **Discriminating check for any new domain tool integration (Domains 1–10):**
   When wrapping any untrusted solver or compiler from Sections 1–10 as an
   Anneal `Language SemObs` and `BehaviorCodec`:
   - Check that invalid physical/hardware encodings (`NaN`, non-unit $SE(3)$
     poses, 4-valued `X`/`Z`, DRC/LVS violations, syndrome-uncorrectable states,
     forbidden voltage window $[V_{IL}, V_{IH}]$) map to `decodeOut o₂ = none`
     and satisfy `encodeOut_of_decodeOut` and `obs_decodeOut`.
   - Construct a negative canary proving that the domain's trivial Goodhart
     degenerate solution (empty CBF safe set, zero-velocity freezing robot,
     all-red railway interlocking, stalled RTL pipeline, post-selected zero-trace
     ZX diagram, zero-current analog startup, or zero-power HIFU array) is
     rejected by `InhabitedPre` + `Language.ProductiveOn`.
   - Verify that all empirical ODD and foundry PDK assumptions appear only as
     positive `Id` entries in `VerificationResult.waived` (`ob.id ∈ waived ∨ ob.prop`)
     and never on the left-hand side of an implication (`→`).
3. **Validate corpus metadata and formatting:**
   ```console
   python3 tools/reference.py check
   ```
