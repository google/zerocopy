# Real-World Verification Tools and Historical Failure Postmortems Across Cyber-Physical Systems, Robotics, Aerospace, Industrial Control, EDA/VLSI, Quantum Computing, Analog/Photonics, and Metamaterials

## Summary

### Part I — Real-World Verification, Synthesis, and Compilation Tool Landscape

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

### Part II — Historical Verification, Compiler, and Operational Failure Postmortems

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

### Part I — Real-World Verification and Compilation Tools Applicability

This report applies to Anneal's core verification and refinement architecture
and to the ten real-world tool ecosystems indexed in `REPORT.json`:

1. **Anneal (`joshlf/anneal`)** at `24367bd1a8c784f2578535954f9915e24894a56f`
   (`trusted-refinement-core`: `trusted/lean/Trusted/Refinement.lean` and
   `trusted/lean/Trusted/StepResult.lean`) and
   `5fc1139f2208b3c9cfb513573c4a731cc32bb457` (`x86-backend-pipeline`:
   `trusted/lean/Trusted/X86Semantics.lean`), together with the refined
   4-primitive architecture established in
   `support/BehaviorCodecExpressiveness.lean`,
   `support/ProofGatedCompilationAndTrustPolicy.lean`,
   and `support/StructuralExternalCallAndCanaries.lean`.
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

### Part II — Historical Verification and Operational Failures Applicability

This report applies to the design and review of Anneal's trusted refinement core
(`trusted/lean/Trusted.lean` and the inline refinement/step-result specification
in Section 0 across
`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`,
`joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457`, and
`joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`) when evaluating
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

### 0. Inline Specification of Anneal's Trusted Refinement, Codec, Progress, and Trust-Policy Primitives

`Basis: source + execution + derived`

To make this survey self-contained without depending on unmerged feature branches, we record here the exact Lean 4 (`v4.34.1`) definitions of Anneal's four foundational verification primitives—(1) the partial behavior and refinement spine (`Preorder`, `Partial`, `Behavior`, `Language`, `Language.SpecOn`), (2) the bidirectional representation and pass-polarity codecs (`BehaviorCodec`, `PartialBehaviorCodec`, `Compiles`, `Abstracts`), (3) the non-vacuity, miracle-freedom, eventual small-step progress, and external-call boundary primitives (`NonVacuousOn`, `Language.ProductiveOn`, `Language.Verified`, `StepResult`, `ReachesPrefix`, `EventualBehaviorOf`), and (4) the scoped obligation and waiver envelope (`Obligation`, `TrustPolicy`, `VerificationResult`)—matching the standalone kernel-checked mechanizations preserved in `support/BehaviorCodecExpressiveness.lean`, `support/AntiDegeneracyAndCallbackFraming.lean`, `support/StructuralExternalCallAndCanaries.lean`, and `support/ProofGatedCompilationAndTrustPolicy.lean`:

```lean
/-- Reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Constructive partiality carrier representing `B ∪ {UB}`: `defined` is
`False` (`Partial.ub`, the top element `⊤`) when the computation exhibits
undefined behavior. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Query-indexed partial behaviors: for each query, either UB or a predicate
describing the set of permitted outcomes. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Program-indexed semantic language with explicit initial-state domain `dom`. -/
structure Language where
  Prog  : Type
  Query : Type
  Out   : Type
  sem   : Prog → Behavior Query Out
  dom   : Prog → Query → Prop

def Language.SpecOn (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Behavior L.Query L.Out :=
  fun q => ⟨pre q, fun _ => post q⟩

/-- Domain-intersected precondition non-vacuity: some query is in `dom` and
satisfies `pre`. Model limits at entry empty `dom` and therefore fail closed. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn (L : Language)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog` against `(pre, post)`
within `prog`'s own domain `L.dom prog`. -/
def Language.Verified (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn (L.dom prog) pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Single-step transition outcome in a small-step operational machine,
including decidable pre-call boundary checks (`externalCall`). -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

inductive StepResult (State : Type) (Obs : Type := Empty) (Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | externalCall (boundaryInv : Bool) (next : State → Obs → Prop)
  | terminated (term : TerminationKind Val)
  | failed

/-- Named proof obligation and waiver-governed verification judgment. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

abbrev Obligation.assumed {Id : Type} (id : Id) : Obligation Id :=
  ⟨id, False⟩

structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

def NoDupIds {Id : Type} (ids : List Id) : Prop :=
  (ids.foldr
    (fun id (acc : Prop × List Id) =>
      (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1, id :: acc.2))
    (True, [])).1

def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  NoDupIds (obligations.map Obligation.id) ∧
  NoDupIds waived ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))
```

### Part I: Real-World Verification, Synthesis, and Compilation Tool Deep-Dives

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
     standalone ISO C (1999) monitor components for NASA's **`cFS`** (`nasa/cFS`, Core
     Flight System), **`F Prime`** (`nasa/fprime`, JPL's flight software
     framework used on the Mars Ingenuity Helicopter), or `ROS 2`.
   - **`Astrée` (AbsInt / ENS Paris, Patrick & Radhia Cousot, Blanchet et al.,
     PLDI 2003) and `Polyspace Bug Finder / Code Prover` (MathWorks):** Sound
     abstract-interpretation static analyzers for safety-critical C/C++ flight
     software that prove the absence of runtime errors (overflow, division by
     zero, out-of-bounds array access, invalid pointers, NaNs).
2. **Design philosophy, tradeoffs, and TCB boundaries:**
   - `Copilot` compiles Haskell stream specifications (`Atom` backend) into
     constant-time, constant-space ISO C (1999) monitor code with zero dynamic memory,
     zero pointers, and bounded loops. However, `Copilot`'s Haskell-to-C (ISO 9899:1999)
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

### Part II: Historical Verification, Compiler, and Operational Failure Postmortems

### Historical Failure Analysis 1. CPS, Hybrid Automata, and Reachability Verifier Failures

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

### Historical Failure Analysis 2. Robotics, Avionics, Spacecraft, and Industrial Control Postmortems

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

### Historical Failure Analysis 3. Digital Logic, EDA, RTL/Gate Equivalence (LEC), CDC, and HLS Synthesis Failures

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

### Historical Failure Analysis 4. Quantum Circuit Compiler Miscompilations and Fault-Tolerant Decoder Failures

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

### Historical Failure Analysis 5. Analog/Mixed-Signal (SPICE), Silicon Photonics, and Programmable Metamaterial Escapes

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

### Historical Failure Analysis 6. Cross-Domain Failure-to-Primitive Synthesis Matrix

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

### Part I — Real-World Tool Survey Boundaries

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
  `support/BehaviorCodecExpressiveness.lean`, Anneal's
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

### Part II — Historical Verification Failure Postmortem Boundaries

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
  `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457`.
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

### Part I — Real-World Tool Survey Evidence

1. **Anneal Trusted Refinement & Small-Step Core (`source` + `execution`):**
   - Repository: `joshlf/anneal` at `24367bd1a8c784f2578535954f9915e24894a56f`
     (`trusted/lean/Trusted/Refinement.lean:201-473`,
     `trusted/lean/Trusted/StepResult.lean:55-200`) and
     `5fc1139f2208b3c9cfb513573c4a731cc32bb457`
     (`trusted/lean/Trusted/X86Semantics.lean`).
   - Companion reference packages published at `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`
     on `refs/heads/reference` (observed `2026-10-31`):
     - `support/BehaviorCodecExpressiveness.lean`
       (mechanizing `EventualBehaviorOf` and `PartialBehaviorCodec`),
     - `support/ProofGatedCompilationAndTrustPolicy.lean`
       (mechanizing proof-gated cut elimination and positive per-obligation
       waiver scoping), and
     - `support/StructuralExternalCallAndCanaries.lean`
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

### Part II — Historical Verification Failure Postmortem Evidence

### 1. Primary Anneal Repository and Reference Corpus Sources (`source` + `execution`)

- **Anneal Core Refinement and Small-Step Semantics:**
  - Repository: `joshlf/anneal`
  - Revisions examined:
    - `24367bd1a8c784f2578535954f9915e24894a56f` (`trusted/lean/Trusted.lean`),
    - `5fc1139f2208b3c9cfb513573c4a731cc32bb457` (`docs/architecture.md`, `docs/design.md`, `docs/trust-model.md`), and
    - `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` (`skills/robust-code/SKILL.md`).
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
  (`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`):**
  - `support/BehaviorCodecExpressiveness.lean`
    (`PartialBehaviorCodec`, `EventualBehaviorOf`, `eventual_wellFormed_iff_prefix_wellFormed`),
  - `support/StructuralExternalCallAndCanaries.lean`
    (`StepResult.externalCall`, `ReachesPrefix.externalCallFail`,
    `ReachesPrefix.externalCallOk`, `open_world_callback_composition_sound`), and
  - `support/ProofGatedCompilationAndTrustPolicy.lean`
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

### Part I — Real-World Tool Survey Revalidation

To revalidate the structural mappings and corpus invariants of this report after
changes to Anneal's `trusted/lean/` primitives or when instantiating a concrete
domain verifier in `theory/`:

1. **Validate the four `trusted/lean/` primitive mechanizations in Lean 4.34.1:**
   Run the standalone Lean 4 kernel checks preserved in the companion packages:
   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/BehaviorCodecExpressiveness.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/ProofGatedCompilationAndTrustPolicy.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/StructuralExternalCallAndCanaries.lean
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

### Part II — Historical Verification Failure Postmortem Revalidation

To revalidate the architectural mappings between the 24 historical failure modes
and Anneal's four `trusted/` primitives after any change to `Trusted/Refinement.lean`
or `Trusted/StepResult.lean`:

1. **Re-run the mechanized anti-degeneracy, external-call framing, and scoped
   trust-policy Lean 4 probes** preserved on the `reference` branch using the
   pinned Lean 4 kernel (`leanprover/lean4:v4.34.1`, invoked with
   `-DElab.async=false -Ddebug.skipKernelTC=false`):
   - Check `support/BehaviorCodecExpressiveness.lean`
     to verify that `PartialBehaviorCodec` (`decodeOut : L₂.Out → Option L₁.Out`)
     still maps `decodeOut o₂ = none` to `False` and that `EventualBehaviorOf`
     still satisfies `eventual_wellFormed_iff_prefix_wellFormed` with zero
     axioms (`#print axioms`).
   - Check `support/StructuralExternalCallAndCanaries.lean`
     to verify that `StepResult.externalCall` and `ReachesPrefix.emptyChoice` /
     `noStep` step to `.failed` or `.stuck` (`isSafe = False`) with zero
     `Classical.choice`.
   - Check `support/ProofGatedCompilationAndTrustPolicy.lean`
     to verify that positive per-obligation waiver envelopes
     (`ScopedVerificationResult`) prevent a false assumption on one obligation
     from discharging sibling obligations via `False.elim`.
2. **Validate corpus metadata and formatting:**
   ```console
   python3 tools/reference.py check
   ```
   Verify that `REPORT.json` and `REPORT.md` pass all schema checks and that
   `./ci/check_todo.sh` reports zero violations.
