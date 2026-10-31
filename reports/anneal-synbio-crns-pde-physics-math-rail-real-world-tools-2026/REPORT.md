# Real-World Tool Deep-Dive: Synthetic Biology, CRNs, Microfluidics, Physiological Control, PDE Conservation Compilers, Mathematical Certificates, Railway Interlocking, and Scientific Epistemology on Anneal's Trusted Kernel

## Summary

Across natural-science compilers, molecular programming, cyber-physical control,
structure-preserving scientific computing, experimental mathematics, railway
signaling, and statistical epistemology, deployed verification and synthesis
tools repeatedly confront four structural failure modes that mirror compiler
verification hazards in `trusted/lean/`:

1. **Physical, biological, or epistemic breakdown disguised as nominal output
   (`Language SemObs` and `Partial.ub`):** Whether a genetic circuit saturates
   host ribosomes in `Cello`, an electrowetting droplet violates Chebyshev
   spacing in `MFSimStatic`, an IEEE-754 stencil overflows to `NaN` in `Devito`,
   or a causal query conditions on a collider in `DoWhy`, the target domain has
   states where the underlying mathematical abstraction loses physical or
   epistemic validity (`defined = False`).
2. **Representation spoofing and transient intermediate leakage (`BehaviorCodec`,
   `Compiles`, and `Abstracts`):** Multi-step DNA strand-displacement cascades
   (`Visual DSD`, `Peppercorn`), $m \times m$ supertile self-assembly blocks
   (`Xgrow`), rotary microfluidic mixers (`Puddle`), and cockpit flight-mode
   annunciators (`PVSio-web`) interleave representation-specific intermediate
   configurations with clean macro-states. Returning `decodeOut = none` on
   non-resting intermediates while enforcing `obs_decodeOut` and partial
   bijection laws (`decodeOut_encodeOut`, `encodeOut_of_decodeOut`) prevents
   transient or aliased representations from spoofing macro-level invariants.
3. **Vacuous safety via starvation, deadlocks, or empty preconditions
   (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`):** A chemical reaction network that empties a
   critical siphon (`Catalyst.jl`), an insulin controller that suspends basal
   delivery forever (`OpenAPS`), a railway interlocking that holds all signals
   red (`Prover iLock`), or a deep-space probe locked in eternal safe mode
   (`Aerie`) satisfies safety invariants vacuously (`val = ∅` or zero progress).
   Pairing `Compiles` with `ProductiveOn` and `InhabitedPre` enforces liveness
   and witness completeness, while `StepResult.externalCall` gates open-world
   disturbances, oracle calls, and custody transfers behind `boundaryInv`.
4. **Conflation of machine-checked algebra with empirical or regulatory
   modeling priors (`VerificationResult` and `TrustPolicy`):** Tools in these
   domains routinely blend exact combinatorial or algebraic proofs (stoichiometric
   mass balance, Farkas LP certificates, Reidemeister moves, `do`-calculus
   $d$-separation) with empirical priors (Turner RNA free-energy parameters,
   UVA/Padova patient cohorts, MUTCD braking kinematics, IPCC emission factors).
   Anneal's `VerificationResult policy waived obligations` isolates empirical
   priors into positively tracked obligation waivers (`ob.id ∈ waived ∨ ob.prop`)
   without introducing unsound global axioms into the Lean kernel.

## Applicability

This report applies to Anneal's four-primitive verification kernel architecture
(`Language SemObs` and `Partial`, `BehaviorCodec` / `Compiles` / `Abstracts`,
`ProductiveOn` / `InhabitedPre` / `EventualBehaviorOf` /
`StepResult.externalCall`, and `VerificationResult` / `TrustPolicy`) evaluated
as a unifying verification target and certificate-checking substrate across 16
real-world tool families (comprising over 65 concrete software systems and
standards) identified in `REPORT.json`.

The subjects in `REPORT.json` are related by **architectural interpretation and
certificate-interface reduction**: each external tool family is analyzed with
respect to its concrete input/output intermediate representations, solver backends,
and implicit trusted computing base (TCB), and its correctness obligations are
mapped onto Anneal's four `trusted/` primitives. Claims about upstream tool
internals, algorithms, and TCB boundaries reflect upstream source repositories,
published specifications, and peer-reviewed primary literature as of
`2026-10-31`. Claims about Anneal encodings (`Basis: derived`) establish how
those tool obligations instantiate Anneal's definitions without modifying
`trusted/lean/`.

## Findings

### Part I: Molecular Computing, Synthetic Biology, Microfluidics, Physiological Control, and Ecology

---

#### 1. Biocomputing Logic Synthesis and Genetic Design Automation (`Cello`, `Cello 2.0`, `GEC`, `Eugene`, `Proto BioCompiler`, `SynBioHub`/`SBOL3`, `iBioSim`, `LOICA`)

`Basis: documentation + source + derived`

##### 1.1 Goals and Primary Users
Genetic Design Automation (GDA) compilers translate discrete behavioral logic or
dynamical specifications into concrete DNA sequences encoding transcriptional
and translational regulatory networks (promoters, ribosome binding sites [RBS],
coding sequences [CDS], terminators, and small RNAs). Primary users are
synthetic biologists, metabolic engineers, and biofoundry automation engineers
designing living biosensors, therapeutic cell classifiers, and autonomous
microbial controllers in *Escherichia coli*, *Saccharomyces cerevisiae*,
*Bacteroides thetaiotaomicron*, and mammalian chassis.

##### 1.2 History and Intellectual Lineage
- **MIT Proto BioCompiler (Beal, Weiss, Densmore, 2009–2012):** Adapted the MIT
  Proto amorphous-computing spatial compiler to compile high-level dataflow
  programs into abstract transcriptional regulatory motif graphs, pioneering
  automated motif-level technology mapping and optimization before standardized
  flow-cytometry unit calibration existed.
- **Genetic Engineering of Living Cells (`GEC`, Pedersen & Phillips, Microsoft
  Research, 2009):** Introduced declarative logic-programming constraints over
  promoters, RBSs, and protein-coding bricks, compiling high-level regulatory
  specifications into mass-action/Michaelis-Menten SBML models.
- **`Eugene` (Bilitchenko, Liu, Cheung, Densmore, CIDAR Lab, 2011–2016):**
  Created a domain-specific constraint language (`Part`, `Device`, `Rule`
  combinators such as `BEFORE`, `CONTAINS`, `NOTMORETHAN`, `WITH`) to prune
  combinatorial genetic-part assembly spaces prior to wet-lab cloning.
- **`Cello` (`CIDAR-LAB/cello`, Nielsen, Der, Shin, Vaidyanathan, Densmore,
  Voigt, *Science* 2016) and `Cello 2.0` (`CIDAR-LAB/Cello-v2-core`, Jones et
  al., *Nature Protocols* 2022):** Established the industry-standard
  Verilog-to-DNA synthesis pipeline. `Cello` compiles behavioral Verilog into
  NOR/NOT gate netlists via Yosys/ABC, maps gates to orthogonal TetR/PhlF/SrpR
  repressor libraries calibrated in Relative Promoter Units (RPU) via a User
  Constraints File (UCF), and scores steady-state ON/OFF cytometry margin via
  Hill response functions:
  $$y_i = y_{i,\min} + (y_{i,\max} - y_{i,\min}) \frac{\kappa_i^{n_i}}{\kappa_i^{n_i} + x_i^{n_i}}.$$
  `Cello 2.0` generalized the UCF schema to multi-chassis environments (yeast,
  *Pseudomonas*, gut commensals), added tandem-promoter roadblocking models, and
  integrated directly with `SynBioHub` and `Eugene` landing-pad rules.
- **`SynBioHub` (`SynBioHub/synbiohub`), `SBOL3`, `iBioSim`
  (`MyersResearchGroup/iBioSim`), and `LOICA` (`RudgeLab/LOICA`):** Form the
  interoperable standards and simulation backbone. `SBOL3` (Synthetic Biology
  Open Language v3.1) provides an RDF/OWL graph data model for sequence-to-system
  hierarchy; `SynBioHub` serves as the queryable SPARQL repository; `iBioSim`
  compiles SBOL/SBML genetic models into deterministic ODE, Gillespie SSA, and
  stochastic Petri-net reachability analyses; and `LOICA` provides a Python
  object-oriented abstraction linking experimental plate-reader/Flapjack data to
  SBOL3 dynamic characterization.

##### 1.3 Design Philosophy and Tradeoffs
- **`Cello` / `Cello 2.0`:** Prioritizes static steady-state logic separation
  (maximizing $\min(\text{ON}) / \max(\text{OFF})$ RPU ratios across all $2^m$
  boolean inputs) and empirical flow-cytometry histograms over continuous-time
  transient modeling. Tradeoff: combinational simulated-annealing gate
  assignment scales quickly on small circuits ($\le 12$ gates) but ignores
  retroactivity (downstream promoter titration loading upstream transcription
  factors) and dynamic glitch hazards during sequential state transitions unless
  supplemented by `iBioSim`.
- **`Eugene`:** Purely structural and combinatorial (filtering part permutations
  via SAT/constraint propagation) without native kinetic ODE semantics.
- **`iBioSim`:** Prioritizes dynamic fidelity (Hierarchical SBML/SBOL composition,
  abstraction transformations such as quasi-steady-state enzymatic reduction,
  and LTL/stochastic property checking) at the cost of state-space explosion on
  unabstracted networks.

##### 1.4 Ecosystem Comparisons
| Tool | Primary Input | Target Output | Core Solver / Engine | Dynamic Semantics |
| :--- | :--- | :--- | :--- | :--- |
| `Cello` / `Cello 2.0` | Verilog + UCF JSON + `Eugene` rules | Assigned DNA plasmid sequence + SBOL | Yosys/ABC + Simulated Annealing / B&B | Steady-state Hill function + cytometry convolutions |
| `GEC` | Declarative part/interaction program | Parameterized SBML CRN | Prolog-style unification over brick DB | Mass-action / Michaelis-Menten ODE & Gillespie |
| `Eugene` | `.eug` structural constraint rules | Validated combinatorial part arrays | Custom constraint solver / JaCoP | None (combinatorial sequence grammar) |
| `Proto BioCompiler` | Spatial Lisp dataflow (`Proto`) | Optimized regulatory motif netlist | Motif substitution + dead-code elimination | Continuous-time Hill ODEs |
| `iBioSim` | SBOL3 + SBML + LTL properties | ODE/SSA traces, Petri-net bounds | REB2SAC abstraction + LEMA/PRISM | Continuous ODE + Gillespie CTMC + Hybrid Petri |
| `LOICA` | Python `GeneticNetwork` objects | SBOL3 + simulated fluorescence traces | SciPy ODE / stochastic integrators | Two-step transcription-translation + growth dilution |

##### 1.5 Formal Theory and Trusted Computing Base (TCB)
None of `Cello`, `GEC`, `Eugene`, or `LOICA` emits machine-checked proof
certificates. `Cello`'s TCB includes Yosys/ABC logic synthesis, custom Java/Python
Hill-function evaluation loops, floating-point cytometry histogram binning, and
unverified toxicity growth-score cutoffs ($OD_{600} \ge 0.75$). `iBioSim`
incorporates formal LTL/stochastic model checking via LEMA and `PRISM`, but its
REB2SAC reaction-abstraction passes (rapid-equilibrium and quasi-steady-state
eliminations) are unverified C++/Java transformations.

##### 1.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Bool.Prog` represents the source Verilog netlist; `L_Hill.Prog`
    represents the wired UCF gate assignment $(G, \theta)$ with Hill parameters
    $(y_{\min}, y_{\max}, \kappa, n)$, tandem-promoter roadblocking factors, and
    ribosomal burden weights $r_i$.
  - `Query` is a boolean assignment $b \in \{0,1\}^m$ (or inducer concentration
    vector $u \in \mathbb{R}_{\ge 0}^m$).
  - `Out` in `L_Hill` is the tuple $(x^*, \tau_{\text{settle}}, R_{\text{load}})$
    of steady-state promoter activities $x^* \in \mathbb{R}_{\ge 0}^V$ in RPU,
    settling time, and cellular burden.
  - `SemObs` (`obs`) projects $x^*$ to the discretized reporter boolean vector
    $\text{obs}(x^*) \in \{0,1\}^p$ via thresholds $[0, \theta_{\text{OFF}}]$
    and $[\theta_{\text{ON}}, \infty)$.
  - `Partial.ub` (`defined = False`) triggers when: (1) total ribosomal/RNAP
    burden $\sum_i r_i(x_i^*) > R_{\max}$ (the growth-collapse toxicity failure
    tracked by `Cello`'s empirical toxicity table); (2) any steady-state output
    settles in the forbidden indeterminate noise gap $(\theta_{\text{OFF}},
    \theta_{\text{ON}})$; (3) off-target repressor cross-talk violates diagonal
    dominance; or (4) a feedback latch fails to converge within $\tau_{\max}$.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `BehaviorCodec` between `L_Bool` and `L_Hill` encodes boolean inputs into
    canonical UCF low/high inducer concentrations and sets `decodeOut x = none`
    whenever the trajectory is still in a transient pre-settled state, while
    steady states in the forbidden threshold gap trigger `Partial.ub`.
    `obs_decodeOut` guarantees that thresholded RPU outputs equal the Verilog
    truth table.
  - `Compiles L_Bool L_Hill codec s t` certifies `Cello`'s technology mapping
    and gate assignment end-to-end.
  - `Abstracts L_Interval L_Hill codec v t` certifies `iBioSim`-style monotone
    interval/box enclosures $v$ over-approximating nonlinear Hill ODEs across
    parameter uncertainty boxes $\theta \in [\underline{\theta}, \overline{\theta}]$.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `InhabitedPre` and `ProductiveOn` rule out vacuous `Eugene`/`Cello` designs
    where mutually contradictory part constraints or permanently repressed gates
    yield no reachable stable fixed point.
  - `EventualBehaviorOf` collapses multi-layer transcriptional cascades ($d$
    gate-relaxation epochs) into a single synchronous clock step of `L_Bool`.
  - `StepResult.externalCall boundaryInv branches` models cell-division dilution
    pulses and sequential inducer switching in `iBioSim`/`LOICA`, where
    `boundaryInv` verifies that repressor concentrations lie inside the target
    basin of attraction before the next inducer step.
- **`VerificationResult` and `TrustPolicy`:**
  - Separates Lean-checked Boolean NOR-mapping equivalence (`Compiles`),
    `Eugene` combinatorial grammar compliance, and interval Hill margin checks
    (`Abstracts`) from empirical UCF cytometry spline fits and host-chassis
    growth-toxicity priors (`ob.id ∈ waived` under `TrustPolicy`).

---

#### 2. Abstract Chemical Reaction Networks (CRNs) and DNA Strand-Displacement (DSD) Cascades (`Visual DSD`, `Peppercorn`, `CRN++`, `Piperine`, `PRISM`, `Storm`, `Catalyst.jl`, `Feinberg CRNT`, `BioNetGen`)

`Basis: normative + source + derived`

##### 2.1 Goals and Primary Users
Molecular programmers, synthetic biologists, and quantitative systems
pharmacologists use these tools to compile imperative/declarative mathematical
programs into abstract bimolecular Chemical Reaction Networks ($A + B
\xrightarrow{k} C + D$), lower abstract CRNs into concrete toehold-mediated DNA
strand-displacement (DSD) nucleic acid cascades, and analyze deterministic
mass-action ODE stability or continuous-time Markov chain (CTMC) reachability.

##### 2.2 History and Intellectual Lineage
- **Toehold-Mediated DSD and `Visual DSD` (Lakin, Yordanov, Phillips, Cardelli,
  Microsoft Research, 2009–2016):** Formalized a process calculus for DNA
  domains (long recognition domains and short $4\text{--}8\text{ nt}$ toeholds)
  with configurable semantic hierarchy levels (`Infinite`, `Default`, `Finite`,
  `Detailed` semantics collapsing fast branch-migration steps).
- **`Peppercorn` (`DNA-and-Natural-Algorithms-Group/peppercornenumerator`,
  Badelt, Grun, Sarma, Winfree, Condon, *J. R. Soc. Interface* 2020) and
  `Piperine` (`DNA-and-Natural-Algorithms-Group/piperine`, Srinivas et al.,
  *Nucleic Acids Res.* 2017):** Replaced ad-hoc DSD enumeration with rigorous
  **condensed semantics** (partitioning detailed three-way branch migration and
  four-way exchange steps into resting macro-states vs. transient intermediates)
  and automated sequence compilation (`Piperine`) that lowers formal CRNs into
  4-domain DNA gates while calling `NUPACK` to penalize spurious secondary
  structures and bimolecular leak pathways.
- **`CRN++` (`marko-vasic/crnPlusPlus`, Vasić, Soloveichik, Khurshid, *DNA 24* /
  *Natural Computing* 2020):** Introduced an imperative programming language
  with `ld`, `add`, `sub`, `mul`, `div`, and conditional `ifge`/`cmp` modules
  synchronized by a multi-phase chemical oscillator clock, compiling into
  deterministic mass-action polynomial ODEs.
- **Stochastic Model Checkers (`PRISM`, `prismmodelchecker/prism`, Kwiatkowska,
  Norman, Parker; and `Storm`, `stormchecker/storm`, Hensel, Junges, Katoen,
  Quatmann, Volk):** Provide symbolic MTBDD and sparse-matrix CTMC/DTMC model
  checking of Continuous Stochastic Logic (CSL) properties over discrete
  molecular population networks ($\mathbb{N}^{\mathcal{S}}$).
- **`Catalyst.jl` (`SciML/Catalyst.jl`), `Feinberg CRNT Toolbox` (Feinberg,
  Ellison, Ji, Knight), and `BioNetGen` (`RuleWorld/bionetgen`, Blinov, Faeder,
  Goldstein, Hlavacek):** Provide symbolic reaction network DSLs, deficiency
  zero/one structural stability proofs ($\delta = |\mathcal{C}| - \ell -
  \operatorname{rank}(\Gamma)$), and rule-based site-graph network generation
  (`BNGL` / `NFsim`) to tame combinatorial receptor phosphorylation explosion.

##### 2.3 Design Philosophy and Tradeoffs
- **`Visual DSD` vs. `Peppercorn`:** `Visual DSD`'s early semantic levels relied
  on syntactic rules that could miss complex multi-stranded loop intermediates;
  `Peppercorn` formulates a general graph-theoretic condensation that provably
  collapses strongly connected reversible intermediate networks into effective
  rate constants between resting complex distributions.
- **`PRISM` / `Storm` vs. `Feinberg CRNT`:** `PRISM` and `Storm` verify exact
  quantitative CSL probabilities on finite state truncations $[0, M]^{\mathcal{S}}$
  (vulnerable to boundary truncation artifacts if $M$ is too small), whereas
  `Feinberg CRNT` proves global deterministic Lyapunov stability or bistability
  capacity across *all* positive rate constants $\kappa \in \mathbb{R}_{>0}^{\mathcal{R}}$
  purely from the stoichiometric matrix $\Gamma$ and linkage topology.

##### 2.4 Ecosystem Comparisons
| Tool | Level of Abstraction | Core Semantic Model | Key Verification / Synthesis Mechanism |
| :--- | :--- | :--- | :--- |
| `CRN++` | Imperative arithmetic DSL $\to$ CRN | Mass-action ODEs + chemical clock | Dual-rail subtraction & catalytic oscillator synchronization |
| `Visual DSD` | Domain-level DNA calculus | CTMC / ODE at 4 semantic levels | Rule-based strand-displacement enumeration + SMT/Z3 export |
| `Peppercorn` | Domain-level nucleic acid complexes | Condensed CTMC over resting complexes | SCC pathway condensation over reversible/irreversible transitions |
| `Piperine` | Formal CRN $\to$ nucleotide sequences | Shin-Thachuk-Winfree DSD pathway theory | Sequence optimization against `NUPACK` ensemble defect & leak |
| `PRISM` / `Storm` | Discrete state CTMC / MDP | Continuous Stochastic Logic (CSL) | MTBDD / sparse numerical linear algebra + bisimulation |
| `Catalyst.jl` | Symbolic reaction DSL in Julia | ODE / JumpProcess / SDE (`ModelingToolkit`) | Conservation laws, deficiency calculation, SciML codegen |
| `Feinberg CRNT` | Stoichiometric complex graph | Mass-action ODE equilibria | Deficiency Zero/One theorems & LP/MILP bistability witnesses |
| `BioNetGen` | Site-graph rewrite rules (`BNGL`) | Rule-based ODE / network-free `NFsim` | Canonical site-graph isomorphism & on-the-fly rule expansion |

##### 2.5 Formal Theory and Trusted Computing Base (TCB)
The theoretical foundations here are exceptionally strong: Shin–Thachuk–Winfree
**formal pathway decomposition** (bisimulation modulo resting-set clean states)
and Horn–Jackson–Feinberg **Deficiency Zero Theorem** (existence and uniqueness
of locally asymptotically stable positive equilibria within each stoichiometric
compatibility class via the entropy-like Lyapunov function $V(c) = \sum_i (c_i
(\ln c_i - \ln c_i^* - 1) + c_i^*)$). However, the deployed software tools
(`Peppercorn` in Python, `Catalyst.jl` in Julia, `Storm` in C++) execute in
unverified floating-point/integer runtimes without emitting kernel-checkable
certificates.

##### 2.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_CRN.Prog` is a formal reaction network $(\mathcal{S}, \mathcal{C},
    \mathcal{R}, \kappa)$; `L_DSD.Prog` is a domain-level DSD gate system
    (`Peppercorn`/`Visual DSD`).
  - `Query` is the initial molecular state $x_0 \in \mathbb{N}^{\mathcal{S}}$ or
    concentration vector $c_0 \in \mathbb{R}_{\ge 0}^{\mathcal{S}}$.
  - `SemObs` (`obs`) projects onto the principal signal species
    $\mathcal{S}_{\text{sig}} \subset \mathcal{S}$, erasing inert waste duplexes
    and auxiliary fuel gates.
  - `Partial.ub` (`defined = False`) captures: (1) **fuel starvation** (an
    auxiliary gate or fuel species in `Piperine`/`Visual DSD` depletes to zero
    before computation finishes); (2) **finite-time blowup** in polynomial ODEs;
    (3) **unbounded polymer leak**; or (4) **clock-phase overlap skew** in
    `CRN++` oscillator modules.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Peppercorn`'s condensed semantics and Winfree's pathway decomposition map
    directly onto `BehaviorCodec`: `decodeOut : L_DSD.Out → Option L_CRN.Out`
    returns `some x` **if and only if all reactive intermediate complexes are in
    their resting (`clean`) states**, and returns `decodeOut = none` whenever
    any partially migrated three-way/four-way branch intermediate is present.
    `obs_decodeOut` guarantees that signal-strand counts match the formal CRN.
  - `Compiles L_CRN L_DSD codec s t` certifies that the DSD cascade `t`
    faithfully implements `s` without fuel starvation or spurious pathways.
  - `Abstracts L_Petri L_CRN codec v s` certifies `Catalyst.jl` / `Feinberg CRNT`
    conservative $P$-semiflows ($y^T \Gamma = 0$, $y > 0$) and Deficiency Zero
    Lyapunov sublevel sets that bound the reachable state space of `s`.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `ProductiveOn` discharges the **critical siphon persistence obligation**:
    proving via an integer linear programming (ILP) witness that no minimal
    siphon $Z \subseteq \mathcal{S}$ can be emptied prior to reaching a valid
    terminal state, preventing kinetic deadlock in DSD gates or `CRN++` loops.
  - `EventualBehaviorOf` compresses a multi-step reversible toehold-binding +
    irreversible branch-migration sequence (`Peppercorn` condensed pathway) into
    a single macro-reaction of `L_CRN`.
  - `StepResult.externalCall boundaryInv branches` models open chemostat
    titrations or staged strand additions, where `boundaryInv` asserts that all
    transient DSD intermediates have relaxed to zero (`clean` resting state)
    before the external bolus arrives.
- **`VerificationResult` and `TrustPolicy`:**
  - Certifies stoichiometric conservation laws, deficiency conditions, siphon
    non-emptiness, and `Peppercorn` pathway equivalence in Lean, while isolating
    `Piperine`'s heuristic `NUPACK` sequence-level bimolecular leak-rate
    separation assumptions ($\text{rate}_{\text{toehold}} \gg
    \text{rate}_{\text{blunt-leak}}$) as explicit `TrustPolicy` waivers.

---

#### 3. Algorithmic Tile Self-Assembly and DNA Origami Compilers (`Xgrow`, `ISU TAS`, `caDNAno`, `DAEDALUS`)

`Basis: documentation + source + derived`

##### 3.1 Goals and Primary Users
DNA nanotechnologists and theoretical computer scientists use these tools to
design and verify self-assembling crystalline tile arrays (Wang tiles under
Winfree's abstract and kinetic Tile Assembly Models, aTAM and kTAM) and
scaffolded 2D/3D wireframe DNA origami nanostructures.

##### 3.2 History and Intellectual Lineage
- **`Xgrow` (`DNA-and-Natural-Algorithms-Group/xgrow`, Winfree, Schulman,
  Constantine, Woods, Evans, Caltech, 2003–2024):** The canonical C/X11 and
  Python simulator for Winfree's aTAM (monomer tiles attach irreversibly when
  adjacent matching glue strengths sum to $\ge \tau$) and reversible kTAM
  (forward attachment rate $k_f \propto e^{-G_{\text{mc}}}$, backward detachment
  rate $k_r \propto e^{-b \cdot G_{\text{se}}}$). Used to design and test
  Rothemund-Papadakis-Winfree Sierpinski triangles, binary counters, and
  Winfree-Bekbolatov $k \times k$ proofreading blocks.
- **`ISU TAS` (Iowa State University Tile Assembly Simulator, Patitz, Summers,
  Lutz, 2010–2016):** Added graphical 2D/3D aTAM/2HAM (Two-Handed Assembly Model)
  debugging and automated static/runtime checks for **local determinism**
  (Soloveichik–Winfree criterion for directedness/confluence).
- **`caDNAno` (`cadnano/cadnano2.5`, Douglas, Marblestone, Teerapittayanon,
  Vazquez, Church, Shih, *Nucleic Acids Res.* 2009):** Revolutionized
  Rothemund-style scaffolded DNA origami by providing a square- and
  honeycomb-lattice CAD editor that routes a single-stranded M13mp18 bacteriophage
  scaffold ($7,249\text{ nt}$) against hundreds of antiparallel staple strands
  with periodic Holliday-junction crossovers.
- **`DAEDALUS` (Veneziano, Ratanalert, Zhang, Zhang, Yan, Chiu, Bathe, *Science*
  2016; `hmjeon/DAEDALUS2-pub` / `lcbb/pyDAEDALUS`):** Automated top-down
  geometric compilation from arbitrary 3D polyhedral meshes (`.ply`/`.stl`) into
  fully routed wireframe DNA origami sequences by computing an Eulerian circuit
  (via a spanning tree of the polyhedron's 1-skeleton with 2-duplex DX edges)
  for the scaffold strand and complementary crossover staples.

##### 3.3 Design Philosophy and Tradeoffs
- **`Xgrow` vs. `ISU TAS`:** `Xgrow` is engineered for high-speed Gillespie
  kinetic Monte Carlo simulation of reversible kTAM error rates (facet
  nucleation errors, growth errors) at millions of events per second in C;
  `ISU TAS` focuses on deterministic aTAM/2HAM formal directedness and theorem
  prototyping.
- **`caDNAno` vs. `DAEDALUS`:** `caDNAno` gives manual, lattice-constrained B-form
  helical control ($10.5\text{ bp/turn}$) for dense brick-like bundles, whereas
  `DAEDALUS` is a fully automatic mesh-to-sequence compiler for open 3D
  polyhedral frames where Eulerian scaffold routing is guaranteed by doubling
  every graph edge into a 2-helix DX bundle.

##### 3.4 Ecosystem Comparisons
| Tool | Assembly Paradigm | Input Specification | Output Artifact | Core Correctness Criterion |
| :--- | :--- | :--- | :--- | :--- |
| `Xgrow` | aTAM / reversible kTAM | `.tile` glue matrix + seed + $(G_{\text{mc}}, G_{\text{se}})$ | Terminal crystal / defect statistics | Kinetic error rate & proofreading block completion |
| `ISU TAS` | aTAM / 2HAM / Staged | Tile set XML + seed configuration | Terminal assembly + determinism trace | Local determinism (unique terminal assembly) |
| `caDNAno` | Lattice scaffolded origami | Helical slice & crossover JSON | Staple oligonucleotide CSV sequences | Antiparallel Watson-Crick pairing + crossover pitch |
| `DAEDALUS` | Wireframe polyhedral origami | 3D polyhedral mesh (`.ply`/`.obj`) | Scaffold Eulerian route + staple sequences | Spanning-tree Eulerian single-scaffold tour + DX edge lengths |

##### 3.5 Formal Theory and Trusted Computing Base (TCB)
In aTAM, **Soloveichik and Winfree's Local Determinism Theorem** proves that if
every tile attachment along an assembly sequence binds via glues of total
strength exactly $\tau$ (or a fixed subset of input sides independent of
assembly order) and no two distinct tile types can bind at the same site, then
the tile system is **directed (confluent)**: every maximal assembly sequence
terminates in the exact same unique terminal assembly $\mathcal{A}_{\text{term}}$.
In `DAEDALUS`, graph theory guarantees that doubling every edge of a connected
planar/polyhedral graph creates an Eulerian graph whose A-trail / spanning-tree
boundary tour routes the scaffold without knots. Neither tool checks these
certificates in a theorem prover.

##### 3.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Shape.Prog` is a target 2D coordinate set $X \subseteq \mathbb{Z}^2$ or
    3D polyhedral graph $G = (V, E)$; `L_aTAM.Prog` is a tile system $(T, \sigma,
    g, \tau)$ (`Xgrow`/`ISU TAS`) or scaffold-staple routing map (`DAEDALUS`/
    `caDNAno`).
  - `SemObs` (`obs`) is the geometric support $\operatorname{dom}(\alpha)
    \subseteq \mathbb{Z}^2$ (for `Xgrow`/`ISU TAS`) or the folded topological
    edge-duplex graph (for `DAEDALUS`), erasing internal glue/sequence labels.
  - `Partial.ub` (`defined = False`) triggers on: (1) a **glue mismatch** or
    nondeterministic site collision in aTAM (`ISU TAS`); (2) **unbounded
    growth** when a finite shape was specified; or (3) in `caDNAno`/`DAEDALUS`,
    an **antiparallel polarity violation**, Watson-Crick base-pair mismatch,
    nick collision, or non-Eulerian disconnected scaffold loop.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - In intrinsic universality and $k \times k$ proofreading block replacement
    (`Xgrow`), `decodeOut : L_micro.Out → Option L_macro.Out` inspects each
    $k \times k$ supertile block: if any block is partially assembled,
    `decodeOut = none`; when all touched blocks are complete, it maps each block
    to its macro-tile (`obs_decodeOut` preserves scaled shape geometry).
  - `Compiles L_Shape L_aTAM codec s t` certifies that a tile set `t` or
    `DAEDALUS` spanning-tree routing compiles the target shape `s` without
    mismatches or topological defects.
  - `Abstracts L_Window L_aTAM codec v t` uses $2 \times 2$ sliding-window Wang
    constraints or local-determinism DAGs `v` to over-approximate all reachable
    assemblies of `t`.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `ProductiveOn` rules out **geometric/kinetic traps (canyons)** where surrounding
    tiles enclose an empty site whose exposed glues sum to $< \tau$, starving growth
    before $\mathcal{A}_{\text{term}}$ is completed.
  - `EventualBehaviorOf` collapses the $k^2$ micro-tile attachments inside a
    proofreading block into a single macro-tile attachment step.
  - `StepResult.externalCall boundaryInv branches` models **2HAM / staged multi-pot
    self-assembly** (`ISU TAS`), where `boundaryInv` verifies that each pot has
    reached its unique terminal sub-assembly before robotic buffer mixing.
- **`VerificationResult` and `TrustPolicy`:**
  - Checks Soloveichik–Winfree local determinism (`ISU TAS`) and `DAEDALUS`
    Eulerian spanning-tree tour validity constructively in Lean, while tracking
    `Xgrow`'s reversible kTAM thermodynamic parameters $(G_{\text{mc}},
    G_{\text{se}})$ and B-DNA helical twist strain tolerances ($10.5\text{ bp/turn}$)
    in `waived` under `TrustPolicy`.

---

#### 4. Digital Microfluidics and Electrowetting Lab-on-a-Chip Compilers (`Puddle`, `BioCoder`, `MFSimStatic`, `BioStream`/`AquaCore`, `OpenDrop`)

`Basis: documentation + source + derived`

##### 4.1 Goals and Primary Users
Biofoundry engineers, clinical diagnostic chip designers, and microfluidic CAD
researchers use these systems to compile high-level biochemical assay protocols
(PCR, ELISA, next-generation sequencing library prep, automated cloning) into
cycle-accurate 2D electrode actuation schedules on Electrowetting-on-Dielectric
(EWOD) digital microfluidic (DMF) grids or valve-actuated continuous-flow chips.

##### 4.2 History and Intellectual Lineage
- **`BioCoder` (Ananthanarayanan & Thies, Microsoft Research India,
  *Bioinformatics* 2010) and `BioStream` / `AquaCore` (Thies et al., MIT / MSR,
  *ISCA* 2007):** Introduced a C++ fluidic DSL (`BioCoder`) and instruction-set
  architecture (`AquaCore`) that abstract biochemical protocols away from vessel
  sizes, compiling sample dilution graphs via bit-scanning/DMRW algorithms onto
  programmable valve-based microfluidic chips.
- **`MFSimStatic` (`UCRMicrofluidics/MFSimStatic`, Grissom, Curtis, Windh,
  Phung, Kumar, Zimmermann, O'Neal, Mitchler, Brisk, UC Riverside, *IEEE TCAD*
  2015–2020):** Established the standard open-source C++ synthesis and static
  simulation framework for digital microfluidic biochips, implementing list
  scheduling, path-based/roy-maze/A* droplet routing, pin-constrained broadcast
  electrode addressing, and wash-droplet contamination scrubbing.
- **`Puddle` (`uwmisl/puddle`, Willsey, Stephenson, Takahashi, Vaid, Nguyen,
  Piszczek, Betts, Newman, Joshi, Karin, Zeigler, Ceze, Seelig, UW MISL, *ASPLOS*
  2019):** Created a dynamic, Python-embedded microfluidic operating system and
  runtime for the `PurpleDrop` EWOD platform with closed-loop capacitive/optical
  error recovery and dynamic droplet placement (avoiding brittle ahead-of-time
  static schedules when droplet splits fail).
- **`OpenDrop` (`GaudiLabs/OpenDrop`, Urs Gaudenz, GaudiLabs, 2015–2024):**
  Standardized open-source hardware and firmware for high-voltage AC/DC EWOD
  electrode matrices (`16x8` / `14x8` gold/ITO dielectric arrays) with visual
  JSON/Fluxels frame schedules.

##### 4.3 Design Philosophy and Tradeoffs
- **Static Ahead-of-Time Synthesis (`MFSimStatic`) vs. Dynamic OS Runtime
  (`Puddle`):** `MFSimStatic` compiles the entire assay DAG offline into a fixed
  $(x, y, t)$ schedule using ILP/A* routing, enabling tight pin-sharing
  compression on low-pin-count PCBs, but a single physical droplet slip or
  incomplete split invalidates the schedule. `Puddle` allocates virtual droplet
  handles dynamically at runtime using a spatial reservation allocator and
  closed-loop camera feedback, trading peak electrode packing density for fault
  tolerance.
- **Continuous-Flow Valve ISA (`BioStream`/`AquaCore`) vs. Discrete EWOD Grid
  (`MFSimStatic`/`Puddle`/`OpenDrop`):** `AquaCore` routes fluids through fixed
  peristaltic channels and rotary mixers, whereas EWOD routes discrete droplets
  across an arbitrary 2D grid subject to strict Chebyshev spacing invariants.

##### 4.4 Ecosystem Comparisons
| Tool | Chip Architecture | Input Language | Scheduling & Routing Model | Contamination & Error Handling |
| :--- | :--- | :--- | :--- | :--- |
| `Puddle` | EWOD (`PurpleDrop`) | Python monadic/async fluidic API | Dynamic spatial allocator + A* routing | Closed-loop computer vision + auto wash |
| `BioCoder` | Agnostic / DMF & Flow | C++ assay protocol DSL | Time-constrained DAG export to `MFSimStatic` | Explicit wash-step insertion in DAG |
| `MFSimStatic` | EWOD (Direct & Broadcast) | `.cfg` assay DAG + chip arch | List/FDLS + Roy-Maze / ILP compaction + Pin mapper | Residue tracking + dedicated wash-droplet paths |
| `BioStream`/`AquaCore` | Multilayer PDMS valves | `BioStream` C-like dilution DSL | Bit-scanning dilution tree + ISA scheduler | Channel flush phases between incompatible fluids |
| `OpenDrop` | DIY EWOD (`14x8` grid) | Frame-by-frame electrode bitmaps | Manual / GUI path drawing + microcontroller loop | None (raw open-loop high-voltage actuation) |

##### 4.5 Formal Theory and Trusted Computing Base (TCB)
In EWOD digital microfluidics, physical correctness rests on three discrete
spatiotemporal invariants at every clock tick $t \in \{0, \dots, T\}$:
1. **Static Fluidic Spacing:** For any two distinct droplets $d_i \ne d_j$ not
   scheduled to merge at $t$, their grid centers $(x_i^t, y_i^t)$ satisfy the
   $3 \times 3$ halo exclusion $\|p_i^t - p_j^t\|_\infty \ge 2$.
2. **Dynamic Slip Spacing:** During transition $t \to t+1$, neither $\|p_i^{t+1}
   - p_j^t\|_\infty \le 1$ nor $\|p_i^t - p_j^{t+1}\|_\infty \le 1$ may occur,
   preventing trailing-meniscus coalescence.
3. **Residue Scrubbing:** If cell $c$ was last visited by reagent class $R_a$,
   no droplet of incompatible class $R_b$ may step on $c$ before a designated
   wash droplet $w \in \mathcal{W}$ traverses $c$.
`MFSimStatic` and `Puddle` check these properties dynamically or in C++/Rust
simulators, not in a formal proof kernel.

##### 4.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Assay.Prog` is a typed biochemical protocol DAG (`BioCoder`/`Puddle`);
    `L_EWOD.Prog` is a cycle-accurate electrode actuation matrix $E : [0, T]
    \times \text{Grid} \to \{0,1\}$ (`MFSimStatic`/`OpenDrop`).
  - `SemObs` (`obs`) projects onto the final target sample volumes, dilution
    concentrations, and optical assay readouts, erasing the specific $(x,y)$
    electrode coordinates and rotary mixer paths.
  - `Partial.ub` (`defined = False`) triggers on: (1) **unintended droplet
    coalescence** ($\|p_i^t - p_j^t\|_\infty \le 1$ or dynamic slip violation);
    (2) **cross-contamination** (stepping onto an unwashed dirty electrode);
    (3) **broadcast pin interference** (energizing a shared pin in `MFSimStatic`
    that inadvertently tugs a parked droplet); or (4) **volume underflow** below
    the EWOD necking-split minimum.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `decodeOut : L_EWOD.Out → Option L_Assay.Out` returns `none` while droplets
    are mid-transit or mid-rotary-mixing loop, and decodes completed assay epochs
    to their algebraic dilution tree outputs (`obs_decodeOut` preserves exact
    volumetric stoichiometry).
  - `Compiles L_Assay L_EWOD codec s t` certifies `MFSimStatic` or `Puddle`
    compilation from assay DAG `s` to electrode schedule `t`.
  - `Abstracts L_Cylinder L_EWOD codec v t` certifies 3D space-time bounding-box
    reservations $[x_1, x_2] \times [y_1, y_2] \times [t_1, t_2]$ used for
    modular non-interference across concurrent sub-assays.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `ProductiveOn` proves absence of **fluidic routing gridlock** (where parked
    storage droplets block all Chebyshev-safe corridors) and guarantees assay
    completion before droplet evaporation deadlines.
  - `EventualBehaviorOf` compresses a 500-cycle $2 \times 3$ rotary mixing loop
    in `L_EWOD` into a single atomic `mix(d1, d2)` node in `L_Assay`.
  - `StepResult.externalCall boundaryInv branches` models `Puddle`'s closed-loop
    optical/capacitive sensor feedback after a `split` or thermal cycle:
    `boundaryInv` verifies all droplets are parked in safe holding cells at
    Chebyshev distance $\ge 2$ before branching on whether the split succeeded
    or requires re-coalescence and retry.
- **`VerificationResult` and `TrustPolicy`:**
  - Discharges Chebyshev static/dynamic spacing, broadcast-pin non-interference,
    wash-path residue safety, and `BioStream` bit-scanning dilution arithmetic in
    Lean, while recording empirical fluid-homogenization cycle counts and maximum
    wash-droplet capacity in `waived` under `TrustPolicy`.

---

#### 5. Constraint-Based Flux Balance Analysis and Stoichiometric Network Optimization (`COBRApy`, `MEMOTE`, `CellNetAnalyzer`/`StrainDesign`, `eQuilibrator`, `QSopt_ex`)

`Basis: normative + source + derived`

##### 5.1 Goals and Primary Users
Metabolic engineers, systems biologists, and industrial bioprocess designers use
these tools to reconstruct genome-scale metabolic models (GEMs) of thousands of
intracellular reactions, audit stoichiometric mass and charge conservation,
compute steady-state growth and chemical production envelopes ($S \cdot v = 0$),
and synthesize growth-coupled gene-knockout interventions (`OptKnock`,
`RobustKnock`, Minimal Cut Sets).

##### 5.2 History and Intellectual Lineage
- **`COBRApy` (`opencobra/cobrapy`, Ebrahim, Lerman, Palsson, Hyduke, *BMC Syst.
  Biol.* 2013):** The Python successor to the MATLAB COBRA Toolbox from Bernhard
  Palsson's group at UC San Diego, standardizing SBML `fbc` (Flux Balance
  Constraints) parsing, Flux Balance Analysis (FBA), Flux Variability Analysis
  (FVA), Parsimonious FBA (pFBA), and loopless FBA (`ll-FBA`) via `optlang`
  interfaces to GLPK, CPLEX, and Gurobi.
- **`MEMOTE` (`opencobra/memote`, Lieven et al., *Nature Biotechnology* 2020):**
  Introduced automated continuous-integration unit testing (`pytest`-based) for
  metabolic reconstructions, testing elemental mass balance, proton/charge
  balance, unconserved metabolic moieties, unbounded flux loops, and biomass
  precursor completeness.
- **`CellNetAnalyzer` and `StrainDesign` (`klamt-lab/straindesign`, Klamt, von
  Kamp, Schneider, Max Planck Institute Magdeburg, *PLoS Comput. Biol.* 2022):**
  Pioneered Elementary Flux Mode (EFM) and Constrained Minimal Cut Set (cMCS)
  enumeration via Farkas dual polyhedral transformations, unifying bilevel
  strain-design algorithms (`OptKnock`, `RobustKnock`, `OptCouple`, `MCS`) in
  a single MILP framework.
- **`eQuilibrator` (`elad.noor/equilibrator-api`, Flamholz, Noor, Bar-Even,
  Milo, *Nucleic Acids Res.* 2012; Beber et al., 2022):** Computes component-contribution
  estimates of standard transformed reaction Gibbs free energies $\Delta_r G'^\circ$
  adjusted for intracellular pH, ionic strength, and $\text{pMg}$, enabling
  Thermodynamic Flux Balance Analysis (TFA).
- **`QSopt_ex` (`jonls/qsopt-ex`, Applegate, Cook, Dash, Espinoza, *INFORMS J.
  Comput.* 2007):** Exact rational simplex solver built on GMP (`mpq_t`) using
  precision-boosting LU factorizations and exact rational dual certificates,
  adapted by multiscale FBA researchers (`Ma & Telmer`, `Chindelevitch et al.`,
  `ExactFBA`) to eliminate floating-point mass leaks.

##### 5.3 Design Philosophy and Tradeoffs
- **Floating-Point LP (`COBRApy` + Gurobi/GLPK) vs. Exact Rational LP
  (`QSopt_ex`):** Standard double-precision simplex solvers use feasibility
  tolerances ($\approx 10^{-6}\text{--}10^{-9}$) that allow ill-conditioned
  macromolecular synthesis reactions (such as cofactor-coupled lipid or cell-wall
  biosynthesis with $10^{-5}$ stoichiometric coefficients) to leak mass and
  generate positive biomass growth from zero nutrient uptake. `QSopt_ex`
  computes exact rational primal and dual solutions ($S v^* = 0$ over $\mathbb{Q}$)
  at a $2\times\text{--}20\times$ runtime overhead via warm-started floating-point
  precision boosting.
- **Stoichiometric Cone (`COBRApy`) vs. Thermodynamic Loopless Cone
  (`eQuilibrator` + `ll-FBA`):** Purely linear constraints $S v = 0$ permit
  Type-III internal flux cycles ($A \to B \to C \to A$) that circulate arbitrary
  flux without thermodynamic driving force; coupling `eQuilibrator` chemical
  potentials adds binary MILP sign constraints $v_j \cdot \Delta_r G'_j < 0$.

##### 5.4 Ecosystem Comparisons
| Tool | Primary Role | Mathematical Core | Solver Backend | Key Soundness Hazard Addressed |
| :--- | :--- | :--- | :--- | :--- |
| `COBRApy` | FBA / FVA / pFBA / gene deletions | Polyhedral cone $S v = 0, \underline{v} \le v \le \overline{v}$ | GLPK / Gurobi / CPLEX / HiGHS | Rapid genome-scale phenotype prediction |
| `MEMOTE` | GEM quality-assurance test suite | Stoichiometric matrix nullspace & atomic balance | `COBRApy` + `pytest` checks | Elemental/charge imbalance & Erroneous Energy-Generating Cycles |
| `StrainDesign` | Bilevel knockout & cMCS synthesis | Farkas dual polyhedron & MILP cut sets | CPLEX / Gurobi / SCIP / GLPK | Growth-coupled minimum chemical yield under all growth optima |
| `eQuilibrator` | Biochemical thermodynamics | Component contribution $\Delta_r G'^\circ + R T \ln Q$ | Bayesian linear regression + covariance | Elimination of Second-Law-violating internal futile cycles |
| `QSopt_ex` | Exact rational LP certification | Exact rational simplex over $\mathbb{Q}$ (`mpq_t`) | Incremental precision-scaling + GMP | Floating-point feasibility leaks ($10^{-7}$ fake biomass) |

##### 5.5 Formal Theory and Trusted Computing Base (TCB)
Every FBA, FVA, and cMCS claim reduces to **Farkas' Lemma and Strong Linear
Programming Duality over $\mathbb{Q}$**:
- A flux bound $c^T v \le \beta$ holds across the entire feasible cone $\{v \mid
  S v = 0, \underline{v} \le v \le \overline{v}\}$ if and only if there exist
  exact rational dual multipliers $(y, \lambda^+, \lambda^-)$ extracted from
  `QSopt_ex` checking $S^T y + \lambda^+ - \lambda^- = c$ and $\lambda^{+T}
  \overline{v} - \lambda^{-T} \underline{v} \le \beta$.
- `MEMOTE`'s atomic conservation check reduces to exact integer matrix
  multiplication $E_{\text{elem}} \cdot S_{\text{int}} = 0$.

##### 5.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_GEM.Prog` is the metabolic network reconstruction $(S, \underline{v},
    \overline{v}, E_{\text{elem}}, z_{\text{charge}}, K)$ with gene-knockout set
    $K \subseteq \mathcal{R}$.
  - `Query` is the extracellular media uptake bound vector $u_{\text{media}}$.
  - `Out` is a steady-state flux distribution $v \in \mathbb{Q}^{|\mathcal{R}|}$.
  - `SemObs` (`obs`) projects $v$ onto macroscopic physiological rates
    $(v_{\text{biomass}}, v_{\text{target}}, v_{\text{ATPM}})$.
  - `Partial.ub` (`defined = False`) triggers on: (1) **atomic/charge imbalance**
    ($E_{\text{elem}} \cdot S_{\text{int}} \ne 0$, caught by `MEMOTE`); (2)
    **Type-III thermodynamic futile cycles** violating `eQuilibrator`/Gordan's
    theorem ($\exists c \in \ker(S_{\text{int}}) \setminus \{0\}$ aligned with
    $v$); or (3) **non-viable lethality** ($v_{\text{ATPM}} < \theta_{\text{maint}}$).
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `decodeOut : L_GEM.Out → Option L_Core.Out` maps genome-scale flux vectors
    to lumped core pathway fluxes, returning `none` on transient unbalanced
    states ($S v \ne 0$).
  - `Compiles L_YieldSpec L_GEM codec s t` certifies `StrainDesign`'s
    `RobustKnock`/`cMCS` intervention: every high-growth steady state in the
    engineered strain `t` achieves minimum product yield $v_{\text{target}} \ge
    \gamma_{\min}$ (`obs_decodeOut`) without elemental or thermodynamic `Partial.ub`.
  - `Abstracts L_Cone L_Kinetic codec v s` captures FBA's foundational physical
    abstraction: the linear steady-state polyhedral cone $v$ soundly
    over-approximates all fixed points of the underlying nonlinear Michaelis-Menten
    ODE network `s` without requiring unknown $K_m$ parameters.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `InhabitedPre` and `ProductiveOn` eliminate the #1 metabolic curation and
    knockout-synthesis bug—**zero-flux / blocked-biomass vacuity**—by requiring
    an exact rational witness vector $v^* \in \mathbb{Q}^{|\mathcal{R}|}$ checked
    via `QSopt_ex` that satisfies $S v^* = 0$, $v^*_{\text{biomass}} \ge
    \mu_{\min} > 0$, and loopless chemical potentials $\mu^* \in \mathbb{Q}^{|\mathcal{M}|}$.
  - `StepResult.externalCall boundaryInv branches` models **Dynamic FBA (dFBA)**
    bioreactor steps, where `boundaryInv` asserts intracellular pseudo-steady
    state ($S v = 0$) before the external bioreactor ODE step updates
    extracellular substrate concentrations $u_{\text{media}}(t + \Delta t)$.
- **`VerificationResult` and `TrustPolicy`:**
  - Checks `MEMOTE` atomic balance ($E_{\text{elem}} S_{\text{int}} = 0$),
    `QSopt_ex` primal/dual Farkas certificates (`Rat` arithmetic in Lean), and
    `StrainDesign` cut-set hitting properties in the kernel, while isolating
    `eQuilibrator`'s group-contribution standard formation energy priors
    ($\Delta_f G'^\circ \pm \sigma$) as explicit `TrustPolicy` waivers.

---

#### 6. Closed-Loop Physiological Control Systems (`UVA/Padova` T1DMS / `simglucose`, `OpenAPS` `oref0`/`oref1`, `Loop`, `Flow*`)

`Basis: normative + source + derived`

##### 6.1 Goals and Primary Users
Biomedical control engineers, regulatory safety auditors, and automated insulin
delivery (AID / Artificial Pancreas) developers use these systems to design,
simulate, and formally verify closed-loop subcutaneous insulin dosing algorithms
that regulate blood glucose in Type 1 Diabetes Mellitus (T1DM) patients within
the safe clinical euglycemic range $[70, 180]\text{ mg/dL}$ while preventing
severe hypoglycemia ($< 54\text{ mg/dL}$).

##### 6.2 History and Intellectual Lineage
- **`UVA/Padova` Type 1 Diabetes Metabolic Simulator (Kovatchev, Breton, Dalla
  Man, Cobelli, UVa & University of Padova, 2008 / S2013 / S2017; open-source
  Python port `jxx123/simglucose`):** The first computer simulator accepted by
  the US FDA (in 2008) as a substitute for preclinical animal trials in
  Artificial Pancreas IDE submissions. It models a 300-patient virtual cohort
  (100 adults, 100 adolescents, 100 children) using a 13-differential-equation
  nonlinear compartmental system coupling gastrointestinal meal appearance,
  hepatic glucose balance, insulin-dependent/independent utilization,
  subcutaneous insulin kinetics $(S_1, S_2, I)$, glucagon counter-regulation, and
  interstitial Continuous Glucose Monitor (CGM) transport delay.
- **`OpenAPS` (`openaps/oref0`, Lewis, Leibrand, et al., 2015–2024):** Pioneered
  open-source reference automated insulin delivery (`oref0` temporary basal adjustment
  and `oref1` Super Micro Bolus [SMB] with Unannounced Meal [UAM] detection).
  Instead of black-box optimization, `oref0`/`oref1` explicitly computes four
  deterministic glucose prediction curves (`IOBpredBG`, `COBpredBG`, `UAMpredBG`,
  `ZTpredBG` [Zero-Temp guard]) every 5 minutes and doses against the *minimum*
  (most conservative) trajectory.
- **`Loop` (`LoopKit/Loop`, Nate Racklyeft, Pete Schwamb, Tidepool Loop):**
  iOS Automated Insulin Delivery platform whose core algorithm (`Tidepool Loop`,
  derived from `LoopKit`) achieved FDA clearance in 2023; predicts a single
  combined glucose trajectory from sum-of-effects (insulin action curve +
  carbohydrate absorption + retrospective integral-differential momentum) and
  modulates micro-boluses/temp basals subject to maximum Insulin-On-Board (IOB)
  clamps.
- **`Flow*` (Chen, Ábrahám, Sankaranarayanan, *CAV* 2013; `flowstar`):** The
  standard continuous and hybrid-automaton reachability analyzer using
  **Taylor-Model (TM) flowpipes** (polynomial approximations $p(x_0, t)$ plus a
  rigorous interval remainder $[a, b]$ over-approximating Picard iterations),
  widely used by medical cyber-physical verification groups (Sankaranarayanan,
  Chen, Kushner) to prove bounded-horizon hypoglycemia freedom of artificial
  pancreas controllers over patient parameter boxes.

##### 6.3 Design Philosophy and Tradeoffs
- **Multi-Curve Conservative Guard (`OpenAPS` `oref0`/`oref1`) vs. Unified
  Effect Superposition (`Loop`):** `OpenAPS` separates predictions under four
  competing causal hypotheses (pure insulin decay, carb absorption, unannounced
  meal, and immediate zero-insulin suspension `ZTpredBG`) and requires *all*
  relevant curves to stay above the hypoglycemia threshold before adding
  insulin. `Loop` combines all effects into a single linear-superposition
  trajectory, yielding smoother dosing curves but placing greater reliance on the
  user's entered Carb-to-Insulin Ratio (CR) and Insulin Sensitivity Factor (ISF).
- **Monte Carlo In-Silico Trials (`UVA/Padova` `simglucose`) vs. Taylor-Model
  Reachability (`Flow*`):** `simglucose` tests controllers on 30–300 discrete
  virtual parameter tuples with stochastic CGM noise, which can miss worst-case
  corner combinations of delayed subcutaneous absorption and sensor bias;
  `Flow*` encloses *all* continuous trajectories across an entire compact
  parameter box $\Theta \subset \mathbb{R}^d$, at the cost of Taylor-model
  wrapping-effect growth over long horizons ($> 12\text{ hours}$).

##### 6.4 Ecosystem Comparisons
| System | Role in AID Pipeline | Mathematical Representation | Safety Guardrail Mechanism |
| :--- | :--- | :--- | :--- |
| `UVA/Padova` (`simglucose`) | Physiological plant simulator | 13-state nonlinear compartmental ODEs | Clinical evaluation metrics (LBGI, HBGI, TIR, $G < 54$) |
| `OpenAPS` (`oref0`/`oref1`) | Embedded dosing controller | 4-curve discrete prediction + decision tree | `minPredBG`, `ZTpredBG` zero-temp floor, `max_iob` cap |
| `Loop` (`LoopKit`) | iOS dosing controller | Superposed impulse-response convolution | Retrospective momentum clamp + `maximumBasalRate` + IOB limit |
| `Flow*` | Formal hybrid reachability prover | Nonlinear ODEs + discrete mode switches | Order-$k$ Taylor models with interval Picard remainder |

##### 6.5 Formal Theory and Trusted Computing Base (TCB)
In `Flow*`, soundness of a reachability step $[t_i, t_{i+1}]$ relies on
**Banach's Fixed-Point Theorem / Schauder's Theorem applied to the Picard
integral operator**:
$$\mathcal{P}(X)(t) = X_0 + \int_0^t f(X(s))\,ds,$$
where a Taylor model $T = (p(z, t), I)$ with interval remainder $I$ is a valid
flowpipe over $[0, \delta]$ once $\mathcal{P}(p + I) \subseteq p + I$. In
`OpenAPS`, the core safety invariant is a discrete **Control Barrier Function
(CBF)** condition: even if insulin delivery is immediately set to zero at step
$k$ (`ZTpredBG`), the already-injected subcutaneous insulin depots $(S_1, S_2)$
must not drive future glucose below the safety floor $G_{\text{crit}}$.

##### 6.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Clinic.Prog` is the clinical euglycemic corridor contract;
    `L_Hybrid.Prog` couples the embedded dosing controller (`oref0`/`Loop`
    compiled via Anneal's Rust/MIR pipeline or modeled as a discrete transition
    function) with the continuous `UVA/Padova` or Bergman ODE plant.
  - `SemObs` (`obs`) extracts the clinical trajectory extrema $(\min_t G(t),
    \max_t G(t), \text{TIR})$.
  - `Partial.ub` (`defined = False`) triggers on: (1) **severe hypoglycemia**
    ($G(t) < 54\text{ mg/dL}$ at any continuous instant $t \in [0, T]$, including
    inter-sample instants between 5-minute ticks); (2) **IOB stacking overdose**
    ($\text{IOB}(t) > \text{max\_iob}$, violating `OpenAPS`'s `ZTpredBG` barrier);
    or (3) **ketoacidosis risk** from prolonged insulin suspension.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `decodeOut : L_Hybrid.Out → Option L_Clinic.Out` checks whether postprandial
    digestion and active insulin tails have settled back to basal steady state
    (returning `none` during active digestion transients while `Partial.ub`
    monitors every instant $t$).
  - `Compiles L_MathController L_RustPumpFirmware` links the verified dosing
    algorithm to its concrete embedded fixed-point implementation, and composes
    via `Compiles.trans` with the hybrid safety spec.
  - `Abstracts L_TaylorPipe L_Hybrid codec v t` directly formalizes `Flow*`: the
    sequence of Taylor-model flowpipes $v = \{(p_k, I_k)\}_{k=1}^N$ checked by
    rational interval Picard inclusion in Lean soundly over-approximates all
    continuous trajectories of the nonlinear physiological plant `t`.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `InhabitedPre` and `ProductiveOn` rule out the trivial "always-zero-insulin"
    pump (`u_k = 0`, which avoids insulin-induced hypoglycemia by leaving the
    patient in chronic hyperglycemia): `ProductiveOn` proves that from any
    elevated post-meal state $G_0 \in [180, 250]\text{ mg/dL}$ in `pre`, the
    controller actively doses insulin to restore euglycemia $[80, 140]\text{ mg/dL}$.
  - `EventualBehaviorOf` compresses the multi-compartment subcutaneous absorption
    lag ($u_k \to S_1 \to S_2 \to I \to X \to G$) into a single macro-level
    glycemic correction epoch.
  - `StepResult.externalCall boundaryInv branches` models **unannounced meal
    boluses (`UAM`) and acute exercise sensitivity shocks**: at each 5-minute
    sampling boundary, `boundaryInv` verifies `OpenAPS`'s `ZTpredBG` invariant
    ($G(t) - K_{\text{ISF}} \cdot \text{IOB}(t) \ge G_{\text{crit}}$) before
    branching over the patient's next meal or activity disturbance.
- **`VerificationResult` and `TrustPolicy`:**
  - Machine-checks the `Flow*` Picard-inclusion certificates, `ZTpredBG` CBF
    invariance, and firmware arithmetic in Lean, while recording `UVA/Padova`
    cohort physiological parameter bounds ($\theta \in \Theta_{\text{FDA}}$) and
    maximum CGM sensor lag ($\tau_{\text{CGM}} \le 15\text{ min}$) as explicit
    `TrustPolicy` waivers.

---

#### 7. Polymer and RNA Secondary-Structure Energy-Landscape Compilers (`NUPACK`, `ViennaRNA`/`Barriers`/`Treekin`, `LinearFold`/`LinearDesign`, `Multistrand`)

`Basis: normative + source + derived`

##### 7.1 Goals and Primary Users
RNA therapeutics designers (mRNA vaccine optimization), synthetic biologists
(toehold riboswitches, CRISPR guide RNAs), and nucleic acid nanotechnologists use
these compilers to predict secondary-structure Boltzmann ensembles and solve the
**inverse folding / sequence design problem**: compiling a target base-pairing
graph $M^*$ (or multi-strand complex ensemble or amino-acid sequence) into a
nucleotide sequence $t \in \{\text{A},\text{C},\text{G},\text{U}\}^N$ with high
thermodynamic specificity and trap-free folding kinetics.

##### 7.2 History and Intellectual Lineage
- **`ViennaRNA` (`ViennaRNA/ViennaRNA`, Hofacker, Fontana, Stadler, Bonhoeffer,
  Tacker, Schuster, *Monatsh. Chem.* 1994; Lorenz et al., *Algorithms Mol. Biol.*
  2011) and `Barriers` / `Treekin` (Flamm, Fontana, Hofacker, Schuster, *RNA*
  2000; Wolfinger et al., 2004):** Built the reference dynamic-programming suite
  for Zuker–Stiegler Minimum Free Energy (MFE) folding (`RNAfold`), McCaskill's
  $O(N^3)$ equilibrium partition function $Q = \sum_{M \in \Omega(t)} e^{-\Delta
  G(t,M)/RT}$, suboptimal enumeration (`RNAsubopt`), and exact kinetic barrier-tree
  construction (`Barriers` floods the discrete energy landscape to identify
  local minima and saddle points, feeding macro-state transition rates into
  `Treekin`'s master-equation solver).
- **`NUPACK` (`nupack/nupack`, Dirks, Bois, Schaeffer, Winfree, Pierce, Caltech,
  *SIAM Rev.* 2007; Fornace, Huang, Newman, Pierce, *ACS Synth. Biol.* 2023
  [`NUPACK 4`]):** Extended McCaskill's partition-function recurrences to
  **arbitrary multi-strand interacting complexes** and test-tube concentration
  equilibria, and formulated sequence design via **test-tube ensemble defect
  minimization** (optimizing nucleotide mutations via hierarchical tree
  decomposition so the equilibrium concentration of off-target base pairs across
  an entire reaction pathway is $< \epsilon$).
- **`Multistrand` (`DNA-and-Natural-Algorithms-Group/multistrand`, Schaeffer,
  Winfree, Pierce, *DNA 21* 2015):** Elementary-step Gillespie kinetic simulator
  for multi-strand nucleic acids, simulating base-pair formation/breakage at
  single-nucleotide resolution using Metropolis-Hastings / Kawasaki rates derived
  from `NUPACK` loop energies.
- **`LinearFold` (`LinearFold/LinearFold`, Huang, Zhang, Deng, Zhao, Liu,
  Hendrix, Mathews, *Bioinformatics* 2019) and `LinearDesign`
  (`LinearDesignSoftware/LinearDesign`, Zhang et al., *Nature* 2023):**
  Replaced $O(N^3)$ inside-outside CKY parsing with $5'\text{-to-}3'$ incremental
  left-to-right dynamic programming (`LinearFold`, $O(N b \log b)$ with beam size
  $b$), and reduced **mRNA codon + secondary-structure joint optimization**
  (`LinearDesign`) to an exact intersection of a Deterministic Finite Automaton
  (DFA encoding synonymous codons weighted by Codon Adaptation Index [CAI]) with
  a Stochastic Context-Free Grammar (SCFG encoding Turner folding free energy).

##### 7.3 Design Philosophy and Tradeoffs
- **Positive vs. Negative Design (`LinearDesign` vs. `NUPACK`):** `LinearDesign`
  performs *positive design* over the synonymous-codon DFA$\cap$SCFG lattice: it
  finds the mRNA sequence $t^*$ that minimizes $\Delta G(t^*, M_{\text{MFE}}(t^*))
  - \lambda \ln \text{CAI}(t^*)$ in $O(N^3)$ time (exact when beam $b = \infty$),
  producing rock-stable mRNA structures for vaccines, but does not directly
  minimize the partition-function denominator $Q(t)$ against competing folds of
  the same sequence. `NUPACK` performs *negative design* via **ensemble defect**:
  $$n(t, M^*) = N - \sum_{1 \le i < j \le N} P_{ij}(t) \cdot \mathbb{I}[(i,j) \in M^*] - \sum_{i=1}^N P_{i,\text{unpaired}}(t) \cdot \mathbb{I}[i \text{ unpaired in } M^*],$$
  explicitly driving down the Boltzmann weight of all competing off-target
  structures.
- **Coarse Macro-State Kinetics (`ViennaRNA`/`Barriers`/`Treekin`) vs.
  Trajectory Sampling (`Multistrand`):** `Barriers` deterministically enumerates
  all structures within energy band $\Delta E$ above the MFE to build an exact
  saddle-point barrier tree (exponential in $\Delta E$, tractable up to $N \approx
  100\text{ nt}$), whereas `Multistrand` samples stochastic trajectories on larger
  multi-strand complexes without guaranteeing exhaustive saddle discovery.

##### 7.4 Ecosystem Comparisons
| Tool | Primary Problem | Core Algorithm | Complexity | Thermodynamic / Kinetic Target |
| :--- | :--- | :--- | :--- | :--- |
| `NUPACK 4` | Multi-strand ensemble & inverse design | Multi-strand McCaskill DP + tree defect opt | $O(N^3)$ ($O(N^4)$ pseudoknots) | Test-tube ensemble defect $\le \epsilon$ |
| `ViennaRNA` + `Barriers` | Single/duplex folding & barrier trees | Zuker MFE + `RNAsubopt` + watershed flooding | $O(N^3)$ + $O(|\Omega_{\Delta E}|)$ | Exact local minima, saddle barriers, & `Treekin` CTMC |
| `LinearFold` | Ultra-long viral/mRNA folding | $5'\to 3'$ incremental CKY + beam pruning | $O(N b \log b)$ | Fast MFE & partition function for $N \approx 30,000\text{ nt}$ |
| `LinearDesign` | mRNA vaccine codon + MFE design | Bar-Hillel DFA $\cap$ Turner WCFG parsing | $O(N^3)$ exact ($O(N b^2)$ beam) | Joint $\Delta G_{\text{MFE}}$ stability & CAI optimality |
| `Multistrand` | Base-pair step kinetics | Gillespie SSA over elementary base-pair moves | Per-trajectory Monte Carlo | First-passage times & bimolecular DSD rate constants |

##### 7.5 Formal Theory and Trusted Computing Base (TCB)
Under the Turner 2004 nearest-neighbor loop model, the free energy $\Delta G(t,
M)$ is an exact integer linear combination of tabulated decacalorie/mol loop
parameters (hairpin, stacked pair, bulge, internal loop, multibranch loop). For
`LinearDesign`, Bar-Hillel's theorem guarantees that intersecting a regular codon
language with a context-free RNA grammar yields a context-free grammar whose
Viterbi parse in the tropical semiring $(\mathbb{Z} \cup \{+\infty\}, \min, +)$
is globally optimal when $b = \infty$. For `NUPACK` and `ViennaRNA`, McCaskill's
partition function $Q(t)$ operates in the log-sum-exp real semiring, where IEEE-754
rounding and underflow require interval arithmetic to certify ensemble defect
bounds rigorously.

##### 7.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Struct.Prog` is a target secondary structure $M^*$ (or synonymous polypeptide
    + stability contract); `L_Seq.Prog` is a primary sequence $t \in \{\text{A},
    \text{C},\text{G},\text{U}\}^N$ under Turner 2004 energy semantics and
    Flamm/`Multistrand` elementary base-pair step kinetics.
  - `SemObs` (`obs`) is the dominant folded secondary structure graph
    $M_{\text{MFE}}(t)$ and functional aptamer/CDS readouts.
  - `Partial.ub` (`defined = False`) triggers on: (1) **MFE degeneracy** ($\exists
    M' \ne M^*$ with $\Delta G(t, M') \le \Delta G(t, M^*) + \delta_{\text{gap}}$);
    (2) **ensemble defect violation** (`NUPACK` ensemble defect $> \epsilon$); or
    (3) **forbidden sequence motifs** (poly-G quadruplexes, unintended
    restriction sites, or frame-shift slippery sequences).
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - Along a `Multistrand` or `Barriers` kinetic folding trajectory $M_0 =
    \emptyset \to \dots \to M_k$, `decodeOut : L_Seq.Out → Option L_Struct.Out`
    returns `none` on transient high-energy partially zipped intermediates and
    returns `some M` only at local energy basins where all single-base-pair
    moves are uphill (`obs_decodeOut` guarantees the basin structure matches
    $M^*$).
  - `Compiles L_Struct L_Seq codec s t` certifies that sequence $t$ is a valid
    inverse fold of target $s$ (`NUPACK`/`LinearDesign`).
  - `Abstracts L_BarrierTree L_Seq codec v t` formalizes `ViennaRNA`'s `Barriers`
    watershed reduction: the macro-state barrier tree $v$ (partitioning
    $\Omega(t)$ into gradient basins separated by exact saddle energies) soundly
    abstracts the full $1.8^N$-state conformation landscape `t`.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `ProductiveOn` prevents **kinetic misfolding traps**: a sequence can have
    $M^*$ as its unique thermodynamic MFE yet become kinetically trapped for
    hours in a deep misfolded hairpin $M_{\text{trap}}$ separated from $M^*$ by a
    $+22\text{ kcal/mol}$ unzipping barrier. `ProductiveOn` requires a verified
    `Barriers`/`Findpath` folding pathway from $M_\emptyset$ to $M^*$ whose
    maximum saddle barrier stays strictly below $\Delta E_{\max}$.
  - `EventualBehaviorOf` collapses contiguous helix-stem zipping cascades into a
    single macro-helix transition in `Treekin`.
  - `StepResult.externalCall boundaryInv branches` models **cotranscriptional
    polymerase elongation** and **allosteric riboswitch ligand binding**, where
    `boundaryInv` verifies that the nascent prefix $t[1..k]$ has relaxed into its
    intended native substructure before the next nucleotide is extruded or ligand
    binds.
- **`VerificationResult` and `TrustPolicy`:**
  - Certifies Zuker tropical-semiring MFE optimality (`LinearDesign` / `RNAfold`),
    interval McCaskill ensemble defect bounds (`NUPACK`), and `Barriers` saddle
    witnesses in Lean, while isolating the empirical Turner 2004 calorimetric
    parameter table and coaxial-stacking/pseudoknot heuristics in `waived` under
    `TrustPolicy`.

---

#### 8. Ecological Food-Web, Population Genetics, and Compositional Petri-Net Systems (`Ecopath with Ecosim`, `SLiM`, `MGDrivE`, `AlgebraicPetri.jl`)

`Basis: documentation + source + derived`

##### 8.1 Goals and Primary Users
Fisheries scientists, conservation biologists, vector-borne disease modelers
(CRISPR gene-drive malaria control), and applied category theorists use these
tools to model trophic mass balance across ecosystems, simulate forward-in-time
spatial population genetics, and compose multi-species epidemiological and
ecological reaction networks.

##### 8.2 History and Intellectual Lineage
- **`Ecopath with Ecosim` and `Ecospace` (`EwE`, Polovina 1984; Christensen,
  Walters, Pauly, *Ecol. Model.* 2000–2024):** The global standard for marine and
  aquatic ecosystem management. `Ecopath` enforces static trophic mass balance
  across $S$ functional guilds:
  $$P_i \cdot EE_i = Y_i + B_i \cdot M2_i + E_i + BA_i, \qquad M2_i = \sum_{j=1}^S \frac{B_j \cdot (Q/B)_j \cdot DC_{ji}}{B_i},$$
  requiring every guild's Ecotrophic Efficiency $EE_i \in [0, 1]$ (no guild can
  have more biomass consumed/harvested than it produces). `Ecosim` lifts static
  `Ecopath` snapshots into foraging-arena Lotka-Volterra-style ODEs, and
  `Ecospace` distributes them over 2D Marine Protected Area (MPA) grids.
- **`SLiM` (`MesserLab/SLiM`, Haller & Messer, Cornell, *Mol. Biol. Evol.*
  2017–2023 [`SLiM 4`]):** Genetically explicit forward-in-time evolutionary and
  ecological simulator driven by an integrated scripting language (`Eidos`),
  tracking individual chromosomes, mutations, recombination maps, continuous 2D
  spatial interactions, and multispecies Lotka-Volterra competition/predation.
- **`MGDrivE` (`MarshallLab/MGDrivE`, Sánchez C., Wu, Bennett, Marshall, UC
  Berkeley, *Methods Ecol. Evol.* 2020 [`MGDrivE 2/3`]):** Models CRISPR-Cas9
  homing and toxin-antidote mosquito gene drives across metapopulation networks,
  coupling inheritance cubes $I_{ijk}$ (maternal $\times$ paternal $\to$
  offspring genotype frequencies with homing cleavage and resistance allele
  generation) with larval density-dependent mortality and stochastic Petri-net
  epidemiological transmission.
- **`AlgebraicPetri.jl` (`AlgebraicJulia/AlgebraicPetri.jl`, Baez, Pollard,
  Halter, Patterson, Fairbanks, Topos Institute / UF, 2020–2025):** Implements
  John Baez and Blake Pollard's **Open Petri Nets and Open Reaction Networks**
  using decorated/structured cospans in `Catlab.jl`, compiling composed Petri
  nets into both deterministic Lotka-Volterra/mass-action ODEs (`DifferentialEquations.jl`)
  and stochastic jump processes while preserving compositional functoriality.

##### 8.3 Design Philosophy and Tradeoffs
- **Top-Down Trophic Mass-Balance (`Ecopath`/`Ecosim`) vs. Bottom-Up Individual
  Genetics (`SLiM`/`MGDrivE`):** `Ecopath` constrains undetermined interaction
  rates using thermodynamic conservation of biomass across trophic levels
  ($EE_i \le 1$, Gross Food Conversion Efficiency $GE_i = (P/B)_i / (Q/B)_i \in
  [0.05, 0.35]$), making it ideal for data-limited multi-species fisheries.
  `SLiM` and `MGDrivE` track explicit diploid/haploid genotypes to capture
  evolutionary resistance (e.g., NHEJ functional resistance alleles breaking a
  CRISPR gene drive), which aggregate biomass ODEs cannot represent.
- **Monolithic Scripts vs. Functorial Cospan Composition (`AlgebraicPetri.jl`):**
  In traditional ODE scripts, gluing a vector-population model (`MGDrivE`) to a
  pathogen transmission model requires error-prone manual editing of shared rate
  equations; `AlgebraicPetri.jl` composes open Petri nets via pushouts in a
  symmetric monoidal double category, guaranteeing by functoriality that fluxes
  across shared boundary species cancel identically.

##### 8.4 Ecosystem Comparisons
| Tool | Primary Abstraction | Mathematical Semantics | Key Compositional / Safety Invariant |
| :--- | :--- | :--- | :--- |
| `Ecopath with Ecosim` | Trophic guild mass balance | Linear balance ($EE_i \le 1$) + Foraging-arena ODEs | Trophic pyramid conservation & fishing quota sustainability |
| `SLiM 4` | Multi-species explicit chromosomes | Discrete-generation individual agent simulation (`Eidos`) | Exact gamete segregation + spatial carrying capacity |
| `MGDrivE` | Metapopulation genotype-cubed Petri net | 3D inheritance tensor $I_{ijk}$ + delay ODE / CTMC | Probability-simplex conservation ($\sum_k I_{ijk} = 1$) & threshold containment |
| `AlgebraicPetri.jl` | Open Petri nets (structured cospans) | Functorial semantics into `ODEProblem` / `JumpProblem` | Pushout boundary flux conservation across glued sub-models |

##### 8.5 Formal Theory and Trusted Computing Base (TCB)
Three rigorous mathematical pillars underpin these tools:
1. **Volterra–Goh Global Stability and Hofbauer–Sigmund Permanence:** For a
   Generalized Lotka-Volterra system $\dot{N}_i = N_i(r_i + (AN)_i)$, if there
   exists a positive interior equilibrium $N^* > 0$ and a positive diagonal
   matrix $D \succ 0$ such that $D A + A^T D \prec 0$, then the Goh Lyapunov
   function $V(N) = \sum_i d_i (N_i - N_i^* - N_i^* \ln(N_i/N_i^*))$ proves
   global asymptotic stability on $\operatorname{int}(\mathbb{R}_+^S)$.
2. **Baez–Pollard Functorial Semantics (`AlgebraicPetri.jl`):** The black-box
   map from open reaction networks (structured cospans) to open dynamical systems
   is a symmetric monoidal double functor; pushout composition of networks
   commutes with vector-field summation on shared boundary ports.
3. **Mendelian/Drive Inheritance Stochasticity (`MGDrivE`):** Every parental
   cross $(i,j)$ in the 3D inheritance cube must satisfy $I_{ijk} \ge 0$ and
   $\sum_k I_{ijk} = 1$ (adjusted for genotype-specific embryonic lethality).

##### 8.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Eco.Prog` is a trophic food web (`Ecopath`/`Ecosim`), gene-drive
    metapopulation network (`MGDrivE`), or composed open Petri net
    (`AlgebraicPetri.jl`).
  - `SemObs` (`obs`) projects onto species survival/permanence indicators above
    the Allee extinction floor $N_{\text{crit}}$, sustainable harvest yields, and
    gene-drive containment boundaries.
  - `Partial.ub` (`defined = False`) triggers on: (1) **keystone extinction /
    trophic collapse** ($N_i(t) \le N_{i,\text{crit}}$); (2) **`Ecopath`
    thermodynamic conservation violation** (Ecotrophic Efficiency $EE_i > 1$ or
    trophic conversion efficiency $GE_i > 1$, creating biomass from nothing);
    (3) **non-stochastic `MGDrivE` inheritance cube** ($\sum_k I_{ijk} > 1$); or
    (4) **uncontained gene-drive spillover** into a non-target refuge population.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `decodeOut : L_Species.Out → Option L_Guild.Out` aggregates fine-grained
    species/genotype populations (`SLiM`/`MGDrivE`) into macro-guild biomasses
    (`Ecopath`), returning `none` during acute post-shock transients and
    preserving total biomass and harvest flux via `obs_decodeOut`.
  - `Compiles L_PolicySpec L_ManagedWeb codec s t` certifies that a fisheries
    escapement policy or threshold-dependent gene-drive release schedule `t`
    satisfies the conservation and containment contract `s`.
  - `Abstracts L_Lyapunov L_GLV codec v t` certifies Volterra–Goh logarithmic
    Lyapunov sublevel sets or Hofbauer–Sigmund boundary average-Lyapunov
    functions $v$ over-approximating the nonlinear food-web dynamics `t`.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `InhabitedPre` and `ProductiveOn` prevent vacuous stability proofs where
    $D A + A^T D \prec 0$ holds on paper but $-A^{-1} r$ has a negative component
    (so no interior coexistence equilibrium exists and species go extinct on the
    boundary!): `ProductiveOn` requires a verified strictly positive interior
    witness $N^* > N_{\text{crit}}$ (and `Ecopath` balance $0 \le EE_i \le 1$).
  - `StepResult.externalCall boundaryInv branches` models seasonal pulse
    harvesting, MPA openings, or `AlgebraicPetri.jl` open boundary port fluxes,
    where `boundaryInv` asserts that the population state lies inside the safe
    Goh Lyapunov basin before the external seasonal shock branches.
- **`VerificationResult` and `TrustPolicy`:**
  - Checks `Ecopath` mass balance ($EE_i \in [0,1]$), `MGDrivE` cube stochasticity,
    `AlgebraicPetri.jl` pushout wiring laws, and exact rational Cholesky
    factorizations $-(D A + A^T D) = L D_{\text{chol}} L^T \succ 0$ in Lean,
    while isolating empirical field diet-matrix estimates $DC_{ji}$ and gene-drive
    homing cleavage rates in `waived` under `TrustPolicy`.

---

### Part II: PDE Conservation Compilers, Mathematical Certificates, Railway Interlocking, HCI/Pragmatics, Epistemology, Smart Grids, and Deep-Space Autonomy

---

#### 9. Structure-Preserving Scientific Computing, Floating-Point Error Certificates, and Automatic Differentiation (`Firedrake`, `FEniCSx`/`DOLFINx`, `Dedalus`, `Devito`, `VCFloat2`/`VST-Float`, `Enzyme`)

`Basis: normative + source + derived`

##### 9.1 Goals and Primary Users
Computational physicists, geophysical fluid dynamicists, climate modelers,
seismic imaging engineers, and numerical analysts use these compilers to
translate symbolic partial differential equations (PDEs) into vectorized C/LLVM/GPU
stencil and finite-element kernels, differentiate simulation kernels for PDE-constrained
adjoint optimization, and prove rigorous IEEE-754 floating-point roundoff bounds.

##### 9.2 History and Intellectual Lineage
- **`FEniCSx` / `DOLFINx` (`FEniCS/dolfinx`, Logg, Mardal, Wells, Scrogings,
  Garth, Richardson, 2003–2026) and `Firedrake` (`firedrakeproject/firedrake`,
  Rathgeber, Ham, Mitchell, Lange, Luporini, McRae, Bercea, Markall, Kelly,
  Imperial College London, *ACM TOMS* 2016):** Automated the Finite Element
  Method (FEM) by compiling variational forms written in the **Unified Form
  Language (`UFL`)** ($\int_\Omega \nabla u \cdot \nabla v\,dx = \int_\Omega f v\,dx$)
  on **Finite Element Exterior Calculus (FEEC)** function spaces (Arnold–Falk–Winther
  de Rham cochain complexes $H^1 \xrightarrow{\nabla} H(\text{curl})
  \xrightarrow{\nabla \times} H(\text{div}) \xrightarrow{\nabla \cdot} L^2$) via
  `FFCx` (in `FEniCSx`) or `TSFC` + `Loopy` (in `Firedrake`) into optimized C
  element assembly kernels.
- **`Dedalus` (`DedalusProject/dedalus`, Burns, Vasil, Oishi, Lecoanet, Brown,
  *Phys. Rev. Research* 2020 [`Dedalus v3`]):** Symbolic spectral PDE framework
  that compiles arbitrary differential equations written in plain text/LaTeX-style
  operators (`dt(u) + u@grad(u) = -grad(p) + nu*lap(u)`) into ultraspherical
  (Chebyshev/Fourier/Jacobi/spherical-harmonic) sparse banded matrices with
  implicit-explicit (IMEX) Runge-Kutta timesteppers.
- **`Devito` (`devitocodes/devito`, Louboutin, Lange, Luporini, Kukreja, Witte,
  Herrmann, Velesko, Gorman, Imperial College, *Geosci. Model Dev.* 2019):**
  SymPy-based symbolic Finite-Difference (FD) compiler that lowers high-order
  seismic wave-equation and stencil operators into cache-blocked, SIMD-vectorized
  OpenMP/CUDA/HIP C kernels with automated discrete adjoint generation.
- **`VCFloat2` and `VST-Float` (`VeriNum/vcfloat`, Appel, Kellison, Boldo,
  Melquiond, Tekriwal, Princeton / Inria, *CPP* / *FM* / *JAR* 2016–2025):**
  Coq/Rocq formal verification framework built on `Flocq` ( formal IEEE-754
  arithmetic) and `Interval` that automatically generates and proves Taylor-form
  floating-point roundoff error bounds and absence of `NaN`/`±Inf` overflow for
  C/CompCert numerical kernels (including verified stationary iterative linear
  solvers and Runge-Kutta ODE steps).
- **`Enzyme` (`EnzymeAD/Enzyme`, Moses, Churavy, Paehler, Hückelheim, Narayanan,
  Schanen, Doerfert, Edelman, MIT, *NeurIPS* 2020 / *SC* 2021 / *PLDI* 2022):**
  LLVM-IR and MLIR compiler plugin that performs reverse-mode and forward-mode
  Automatic Differentiation (AD) *after* mid-level compiler optimizations (loop
  invariant code motion, inlining, scalar replacement), synthesizing shadow
  memory tapes and cache-efficient adjoint accumulation loops.

##### 9.3 Design Philosophy and Tradeoffs
- **Variational FEEC (`Firedrake`/`FEniCSx`) vs. Sparse Spectral (`Dedalus`) vs.
  Structured Stencil (`Devito`):** `Firedrake` and `FEniCSx` preserve topological
  de Rham cochain identities ($d_h \circ d_h = 0$, e.g., $\nabla \cdot (\nabla
  \times \vec{A}_h) = 0$ and exact discrete divergence-free velocity in
  Raviart-Thomas / Brezzi-Douglas-Marini elements) on unstructured meshes,
  preventing spurious pressure modes in geophysical flows. `Dedalus` achieves
  exponential spectral accuracy on smooth periodic/spherical geometries using
  sparse ultraspherical conversion operators. `Devito` maximizes hardware
  FLOP/byte roof-line performance on regular Cartesian grids via polyhedral loop
  blocking.
- **High-Level Symbolic AD (`Firedrake` `dolfin-adjoint` / `Devito`) vs.
  Low-Level LLVM AD (`Enzyme`):** `Firedrake` differentiates at the symbolic `UFL`
  variational level before code generation; `Enzyme` differentiates arbitrary
  already-optimized LLVM/MLIR kernels (Crucial when C/Rust/Julia/CUDA kernels
  bypass a symbolic DSL), but requires careful shadow-pointer alias analysis and
  primal tape recomputation vs. caching proofs to ensure no overwritten memory
  corrupts the reverse pass.

##### 9.4 Ecosystem Comparisons
| Tool | Discretization / Domain | Intermediate Representation | Target Code / Certificate | Primary Correctness Property |
| :--- | :--- | :--- | :--- | :--- |
| `Firedrake` | Unstructured FEM / FEEC | `UFL` $\to$ `GEM` $\to$ `TSFC` $\to$ `Loopy` | Vectorized C / PETSc / `pyadjoint` | Exact discrete de Rham cochain & conservation laws |
| `FEniCSx` (`DOLFINx`) | Unstructured FEM / FEEC | `UFL` $\to$ `Basix` $\to$ `FFCx` | C99 / C++20 assembly kernels | Finite-element basis tabulations & variational assembly |
| `Dedalus` | Sparse Spectral (Chebyshev/Spherical) | Symbolic operator tree $\to$ sparse CSR | MPI + FFTW / sparse linear algebra | Tau-method boundary conditions & spectral conservation |
| `Devito` | High-order Finite Difference | SymPy equations $\to$ `Devito` IRclusters | OpenMP / CUDA / HIP C stencils | CFL stability, stencil symmetry, & discrete adjoints |
| `VCFloat2` | IEEE-754 floating-point C | CompCert Clight $\to$ `VCFloat` exprs | Coq/Rocq `Flocq` + `Interval` proof | Rigorous ULP/absolute roundoff & `NaN`/`Inf` freedom |
| `Enzyme` | LLVM IR & MLIR programs | Activity/Alias-annotated SSA CFG | Forward/Reverse LLVM adjoint IR | Exact discrete Fréchet/cotangent derivative $\langle \bar{y}, df(x)\delta x \rangle = \langle d^*f(x)\bar{y}, \delta x \rangle$ |

##### 9.5 Formal Theory and Trusted Computing Base (TCB)
Only `VCFloat2`/`VST-Float` executes inside a formal theorem-proving kernel (Coq/
Rocq over CompCert Clight and `Flocq`), reducing roundoff error bounds to
interval Taylor forms:
$$\tilde{f}(x) = f(x) + \sum_i g_i(x, \delta)\,\delta_i + R(\delta), \qquad |\delta_i| \le \mathbf{u} = 2^{-53}.$$
In `Firedrake`, `FEniCSx`, `Dedalus`, `Devito`, and `Enzyme`, the Python/C++
symbolic lowering passes (`TSFC`, `FFCx`, `Enzyme` LLVM pass) are unverified: a
subtle loop-carried alias bug in `Enzyme` tape caching, an inverted mesh element
($\det J \le 0$) in `DOLFINx`, or a CFL time-step violation in `Devito` can
silently corrupt simulation physics.

##### 9.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Variational.Prog` is a `UFL` / FEEC variational form (`Firedrake`/
    `FEniCSx`) or exact real/interval stencil (`VCFloat2`); `L_IEEE754.Prog` is
    the lowered SIMD/LLVM stencil or adjoint kernel (`Devito`/`Enzyme`).
  - `SemObs` (`obs`) projects mesh state vectors onto macroscopic conserved
    integrals (total mass $\int_\Omega \rho_h\,dx$, discrete divergence
    $\|\nabla \cdot u_h\|$, total energy, or adjoint inner-product duality
    residuals).
  - `Partial.ub` (`defined = False`) triggers on: (1) **IEEE-754 `NaN` or `±Inf`
    generation** (`VCFloat2`); (2) **mesh simplex inversion** ($\det J_K \le 0$
    in `Firedrake`/`FEniCSx`); (3) **CFL instability violation** ($\Delta t
    \cdot \max |c| / \Delta x > C_{\text{CFL}}$ in `Devito`); or (4) **primal
    memory overwrite before reverse-mode tape read** in `Enzyme`.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `decodeOut : L_IEEE754.Out → Option L_RealEnclosure.Out` maps finite
    IEEE-754 bitvectors (`BitVec 64`) to exact dyadic rationals and maps `NaN` /
    `±Inf` to `none` (`VCFloat2`). Consequently, any path that can produce `NaN`
    or `±Inf` automatically fails `Compiles` and `Abstracts`.
  - `Compiles L_PrimalCotangent L_EnzymeAdjoint codec s t` certifies `Enzyme`'s
    reverse-mode LLVM pass: for every input and output seed $\bar{y}$, the
    generated adjoint kernel `t` computes the exact discrete cotangent map of
    `s` without tape-alias corruption (`defined = True`).
  - `Abstracts L_VCFloatInterval L_IEEE754 codec v s` certifies that the
    `VCFloat2` interval Taylor enclosure `v` soundly contains every concrete
    IEEE-754 execution of the compiled stencil `s`.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `ProductiveOn` prevents adaptive timesteppers or Krylov/Newton solvers in
    `Firedrake`/`Dedalus` from vacuously satisfying conservation by stalling at
    $\Delta t = 0$ or diverging without producing a converged iterate.
  - `EventualBehaviorOf` abstracts variable-count Krylov (CG/GMRES) iterations
    and adaptive RK45 micro-steps into a single macro-epoch step to target time
    $T$.
  - `StepResult.externalCall boundaryInv branches` models **multi-physics
    operator splitting and PETSc/BLAS external solver handoffs**, where
    `boundaryInv` verifies interface flux conservation and stiffness-matrix
    positive-definiteness before the external call.
- **`VerificationResult` and `TrustPolicy`:**
  - Checks `VCFloat2`-style dyadic interval Taylor enclosures, FEEC discrete
    cochain commutativity ($d_h \circ d_h = 0$), and `Enzyme` SSA tape liveness
    in Lean, while recording continuum regularity assumptions ($u \in H^s(\Omega)$)
    and subgrid turbulence closures in `waived` under `TrustPolicy`.

---

#### 10. Pure and Applied Mathematical Proof Orchestration, Computational Topology, and Combinatorial Certificates (`Flyspeck`, `Lean Blueprint`, `AlphaProof`/`AlphaGeometry 2`, `SnapPy`/`Regina`, `Kenzo`, `CakeLPR`)

`Basis: normative + source + derived`

##### 10.1 Goals and Primary Users
Research mathematicians, formalization project leads, low-dimensional
topologists, and automated theorem-proving engineers use these systems to
verify massive computer-assisted mathematical proofs (sphere packing, polynomial
Freiman-Ruzsa, Carleson's theorem, IMO Olympiad geometry/algebra, 3-manifold
hyperbolicity, algebraic topology of infinite complexes, and boolean SAT/Ramsey
combinatorial bounds).

##### 10.2 History and Intellectual Lineage
- **`Flyspeck` (`flyspeck/flyspeck`, Hales, Adams, Bauer, Dang, Harrison, Hoang,
  Kaliszyk, Magron, McLaughlin, Nguyen, Nguyen, Nipkow, Obua, Pleso, Rute,
  Solovyev, Ta, Tran, Trieu, Urban, Vu, Zumkeller, *Forum of Mathematics, Pi*
  2017):** Formalized Thomas Hales's proof of the Kepler Conjecture (maximum
  density of sphere packings in $\mathbb{R}^3$ is $\pi / \sqrt{18}$) in HOL
  Light and Isabelle/HOL, combining: (1) classification of $\approx 5,000$ tame
  planar graphs (`Archiver` verified in Isabelle/HOL), (2) tens of thousands of
  linear programming bounds relaxed from nonlinear geometric constraints, and
  (3) **Solovyev's formal nonlinear interval-arithmetic Taylor verifier** in HOL
  Light certifying hundreds of 6-variable trigonometric inequalities.
- **`Lean Blueprint` (`PatrickMassot/leanblueprint`, Massot, 2020–2026):**
  `plasTeX` + Lean 4 dependency-graph orchestration tool powering landmark
  collaborative formalizations including **Sphere Eversion** (Massot, van Doorn,
  Nash), the **Liquid Tensor Experiment** (Scholze, Commelin), the **Polynomial
  Freiman-Ruzsa (`PFR`) Conjecture** (Tao, Dillies, et al., 2023), **Carleson's
  Theorem** (van Doorn, Becker, et al., 2024–2025), and the **Fermat's Last
  Theorem (`FLT`)** project (Buzzard). It links human-readable LaTeX definitions
  and lemma nodes (`\lean{...}`, `\uses{...}`, `\leanok`) to Lean 4 declarations
  and tracks `sorry`-free transitively verified subgraphs.
- **`AlphaProof` and `AlphaGeometry 2` (`google-deepmind/alphageometry`, Trinh,
  Wu, Le, He, Luong, *Nature* 2024; Silver, Hubert, Schrittwieser, et al.,
  Google DeepMind, 2024–2025):** Achieved silver-medal/gold-level International
  Mathematical Olympiad (IMO) performance by pairing neuro-symbolic search with
  sound deductive engines: `AlphaProof` runs AlphaZero reinforcement learning directly
  against the **Lean 4 kernel** as its environment, while `AlphaGeometry` /
  `AlphaGeometry 2` pairs a Gemini-based auxiliary-point generator with a fast
  symbolic **Deductive Database (`DD`) + Algebraic Rules (`AR`)** full-angle/ratio
  Gaussian elimination engine.
- **`SnapPy` (`3-manifolds/SnapPy`, Culler, Dunfield, Goerner, Weeks) and
  `Regina` (`regina-normal/regina`, Burton, Budney, Pettersson, *ACM TOMS*):**
  The premier computational 3-manifold topology suites. `SnapPy` finds hyperbolic
  structures on knot complements by solving Thurston's complex gluing equations
  and includes **`verify_hyperbolicity()`** (using rigorous interval arithmetic
  and the HIKMOT / Krawczyk criterion to produce a mathematical proof of
  complete hyperbolic structure). `Regina` manipulates 3- and 4-manifold
  triangulations via bistellar **Pachner flips** ($2\text{--}3$, $3\text{--}2$,
  $1\text{--}4$), normal surface enumeration, and isomorphism signatures.
- **`Kenzo` (`jromanf/kenzo`, Sergeraert, Rubio, Dousson, Romero, Heras,
  Institut Fourier / Univ. La Rioja):** Implements **Sergeraert's Effective
  Homology** in Common Lisp (accompanied by Coq/ACL2 formalizations by Lambán,
  Rubio, Poza, Domínguez, Dénès): represents infinite-dimensional simplicial
  sets (loop spaces $\Omega X$, Eilenberg-MacLane spaces $K(\mathbb{Z}, n)$)
  paired with explicit **strong deformation retractions / chain contractions**
  $(f, g, h) : C_*(X) \Rightarrow EC_*$ onto finite-type chain complexes $EC_*$
  satisfying the perturbation lemma side conditions ($f g = \text{id}$, $d h +
  h d = \text{id} - g f$, $f h = 0$, $h g = 0$, $h h = 0$).
- **`CakeLPR` (`tanyongkiam/cake_lpr`, Tan, Heule, Myreen, *TACAS* 2021 / *JAR*
  2023):** Verified checker for **Linear Propagation Redundancy (LPR)** and
  DRAT/LRAT clausal proofs synthesized down to verified x86-64 machine code via
  the **CakeML** compiler, used to machine-check multi-terabyte combinatorial
  SAT proofs (Boolean Pythagorean Triples, Schur Number Five, Keller's Conjecture).

##### 10.3 Design Philosophy and Tradeoffs
- **In-Kernel Reflection (`Flyspeck` / `AlphaProof`) vs. Verified External Binary
  (`CakeLPR`) vs. Deductive Engine (`AlphaGeometry 2`):** `Flyspeck` and
  `AlphaProof` check every inference step inside the HOL Light or Lean 4 kernel
  (maximally small TCB, but slow on billion-step SAT/LP traces). `CakeLPR`
  compiles a HOL4 correctness theorem into a native CakeML binary that checks
  100-GB LPR files at C speed while preserving an end-to-end HOL4 machine-code
  theorem. `AlphaGeometry 2`'s `DD+AR` engine is an unverified C++/Python solver
  whose synthetic trace must be translated into Lean (`LeanEuclid`/`GeoCoq`) to
  remove `DD+AR` from the TCB.
- **`SnapPy` / `Regina` / `Kenzo`:** Separate *heuristic topological search*
  (finding a sequence of Pachner moves in `Regina` or floating-point Newton
  approximations in `SnapPy`) from *certificate checking* (checking bistellar
  gluing maps, HIKMOT interval positivity of tetrahedral shapes, or `Kenzo`'s
  5 chain-contraction equations $f g = \text{id}, d h + h d = \text{id} - g f$).

##### 10.4 Ecosystem Comparisons
| Tool | Mathematical Domain | Search / Discovery Engine | Verification / Certificate Mechanism | TCB Status |
| :--- | :--- | :--- | :--- | :--- |
| `Flyspeck` | Sphere packing ($\mathbb{R}^3$) & tame graphs | C++ `cfsqp` nonlinear opt + GLPK LP | HOL Light interval Taylor + Isabelle graph archive | Kernel-checked (HOL Light + Isabelle) |
| `Lean Blueprint` | Collaborative pure math (`PFR`, `Carleson`) | Human + tactic-assisted modular decomposition | Lean 4 kernel (`lake build`) + LaTeX dependency DAG | Lean 4 kernel (flags remaining `sorry`s) |
| `AlphaProof` | Olympiad algebra, number theory, analysis | AlphaZero MCTS + Gemini RL prover | Direct Lean 4 tactic execution in kernel | Lean 4 kernel |
| `AlphaGeometry 2` | Euclidean plane geometry | Gemini neuro-symbolic point generator | `DD` (deductive database) + `AR` (linear angle/ratio matrix) | Custom `DD+AR` solver (unless exported) |
| `SnapPy` / `Regina` | 3-manifold topology & knots | Newton gluing solver / greedy Pachner search | HIKMOT interval arithmetic / isomorphism signatures | Unverified C++/Python (certificates extractable) |
| `Kenzo` | Algebraic topology of loop spaces | Functional Lisp lazy simplicial evaluation | Effective Homology 5-equation chain contractions | Partial Coq/ACL2 formalization of perturbation lemma |
| `CakeLPR` | Extremal combinatorics & SAT (`LRAT`/`LPR`) | `CaDiCaL` / ` Kissat` untrusted SAT solvers | Verified CakeML x86-64 LPR proof checker | HOL4 + CakeML verified machine code |

##### 10.5 Formal Theory and Trusted Computing Base (TCB)
Every tool in this family exemplifies the **Oracle-Search vs. Kernel-Check**
separation:
- In `Kenzo`, **Brown's / Sergeraert's Basic Perturbation Lemma (BPL)** proves
  that given a chain contraction $(f, g, h) : C_* \Rightarrow D_*$ and a small
  differential perturbation $\delta$ on $C_*$ where $h \circ \delta$ is locally
  nilpotent, a new chain contraction $(f', g', h')$ exists explicitly via the
  geometric series $\sum_{k=0}^\infty (-1)^k (\delta h)^k$, preserving homology
  groups $H_*(C_*, d + \delta) \cong H_*(D_*, d')$.
- In `SnapPy`, **Thurston's Hyperbolic Dehn Surgery / HIKMOT Theorem** reduces
  completeness and positivity of a hyperbolic 3-manifold triangulation to
  checking that complex cross-ratio parameters $z_i \in \mathbb{H}^3$ satisfy
  $\operatorname{Im}(z_i) > 0$ and logarithmic gluing equations $\sum_j G_{ij}
  \operatorname{Log}(z_j) = 2\pi i$ via Krawczyk interval contraction.

##### 10.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Topo.Prog` represents a simplicial complex / 3-manifold triangulation
    (`Regina`/`SnapPy`), differential graded chain complex (`Kenzo`), or CNF
    formula (`CakeLPR`).
  - `SemObs` (`obs`) is the preserved mathematical invariant: homology group
    isomorphism class $H_*(K; \mathbb{Z})$ (`Kenzo`), homeomorphism / ambient
    isotopy class (`Regina`/`SnapPy`), or unsatisfiability truth value (`CakeLPR`).
  - `Partial.ub` (`defined = False`) triggers on: (1) an **invalid Pachner or
    Reidemeister move** (e.g., folding two distinct tetrahedra onto the same
    vertices or creating a non-manifold edge in `Regina`); (2) **negatively
    oriented / degenerate tetrahedra** ($\operatorname{Im}(z_i) \le 0$ in
    `SnapPy`); (3) **failure of nilpotency or differential equations** ($d^2 \ne
    0$ or $d h + h d \ne \text{id} - g f$ in `Kenzo`); or (4) an **invalid
    LPR/RAT clause step** in `CakeLPR`.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - In `Kenzo` Effective Homology, the chain contraction $(f, g, h) : C_*(X)
    \Rightarrow EC_*$ **is literally a `BehaviorCodec` between infinite complex
    $C_*(X)$ and finite effective complex $EC_*$**: `decodeOut` is the chain
    projection $f$, `encodeOut` is the chain inclusion $g$, `decodeOut_encodeOut`
    is $f \circ g = \text{id}_{EC_*}$, and `encodeOut_of_decodeOut` up to chain
    homotopy $d h + h d = \text{id} - g f$ guarantees via `obs_decodeOut` that
    passing to homology classes $H_*$ is an exact bijection!
  - `Compiles L_Topo L_Topo codec K1 K2` certifies `Regina`'s Pachner
    simplification sequences and `Kenzo`'s BPL reductions.
  - `Abstracts L_LinearLP L_NonlinearPacking codec v s` directly formalizes
    `Flyspeck`'s linear programming relaxations `v` over-approximating nonlinear
    trigonometric sphere-packing configurations `s`.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - In `Flyspeck` tame-graph enumeration and `CakeLPR` symmetry-breaking cube
    partitions, `InhabitedPre` and `ProductiveOn` ensure that the case partition
    exhaustively covers 100% of canonical orbits and every branch produces a
    refutation certificate (preventing a buggy canonicalizer filter from
    silently dropping hard cases).
  - `EventualBehaviorOf` captures `Kenzo`'s locally nilpotent perturbation
    series $(\delta h)^k \to 0$ and `Regina`'s greedy simplification sequences.
  - `StepResult.externalCall boundaryInv branches` models invoking untrusted
    external solvers (`SnapPy`'s Newton solver, `CaDiCaL` for `CakeLPR`, or
    `AlphaGeometry 2`'s Gemini point generator) where `boundaryInv` verifies the
    returned certificate (HIKMOT interval box, LPR witness, or constructive
    non-degeneracy side conditions) before admitting the step.
- **`VerificationResult` and `TrustPolicy`:**
  - Directly mirrors `Lean Blueprint` (`PatrickMassot/leanblueprint`): in any
    large formalization (`PFR`, `Carleson`, `FLT`), lemmas that are not yet
    proved or that depend on external textbook theorems are tracked as explicit,
    granularity-isolated `Obligation` IDs in `waived` under `TrustPolicy` rather
    than polluting the global environment with untracked axioms.

---

#### 11. Railway Interlocking, Supply-Chain Logistics, and Certified Integer Programming (`Atelier B`, `Ovado`, `ProB`, `HLL`/`Prover iLock`, `EURIS`, `RobustRailS`, `OR-Tools`, `VIPR`)

`Basis: normative + source + derived`

##### 11.1 Goals and Primary Users
Railway signaling engineers (designing CENELEC EN 50128 SIL 4 computer-based
interlockings and CBTC automatic train control), airline/maritime operations
research teams, and discrete optimization specialists use these tools to
specify, synthesize, and certify collision-free track-routing logic, validate
station topology configuration tables, and verify Mixed-Integer Linear
Programming (MILP) recovery schedules.

##### 11.2 History and Intellectual Lineage
- **`Atelier B` (ClearSy, Jean-Raymond Abrial's B-Method, 1996–2026), `Ovado`
  (`OVADO²`, RATP & Systerel), and `ProB` (`hhu-stups/prob2_kernel`, Leuschel &
  Butler, HHU Düsseldorf, *FME* 2003–2026):** The gold standard for SIL 4
  driverless metro and railway verification (deployed on Paris Métro Line 14,
  Line 1, Roissy VAL, São Paulo, and worldwide CBTC systems). `Atelier B`
  verifies stepwise refinement from abstract B machines down to `B0` executable
  C/Ada code; `Ovado` validates gigabyte-scale station-specific topological
  configuration data against formal B predicates; and `ProB` provides
  constraint-based animation, LTL model checking, and independent double-chain
  validation of `Ovado` predicates.
- **`HLL` and `Prover iLock` (Prover Technology, Stålmarck's Method, Sheeran,
  Singh, Stålmarck, *FMCAD* 2000):** Industrial synchronous hardware/software
  verification suite using the declarative **High-Level Language (`HLL`)** and
  Stålmarck's dilemma-rule tautology checker / CDCL SAT induction to verify
  interlocking control tables and generate CENELEC SIL 4 proof logs.
- **`EURIS` (NS Railinfrabeheer / Movares, Berger, Middelkoop, 1990s–2000s) and
  `RobustRailS` / `RSL` (DTU & Banedanmark, Haxthausen, Peleska, Vu, *Sci.
  Comput. Program.* 2014–2020):** `EURIS` pioneered object-oriented geographical
  interlocking specification (points, signals, track sections communicating via
  neighbor telegrams); `RobustRailS` formalized generic parameterized route-table
  interlockings in the **RAISE Specification Language (`RSL`)** and compiled
  station layouts into SMT/SAL transition systems.
- **Google `OR-Tools` (`google/or-tools`, Perron, Furnon, Gay, `CP-SAT` / `GLOP`)
  and `VIPR` (`ambros-gleixner/VIPR`, Cheung, Gleixner, Steffy, *IPCO* 2017 /
  *Math. Program. Comput.*):** `OR-Tools` (`CP-SAT` lazy clause generation +
  MILP routing) solves large-scale supply-chain, cold-chain, and crew/vehicle
  recovery problems; `VIPR` defines the first **solver-independent certificate
  format for Mixed-Integer Linear Programs**, verifying optimality and
  infeasibility bounds in exact rational arithmetic via Chvátal-Gomory / split
  cutting-plane derivations and branch-and-bound tree certificates.

##### 11.3 Design Philosophy and Tradeoffs
- **Constructive Refinement (`Atelier B`) vs. Automated Synchronous SAT Induction
  (`Prover iLock` / `HLL`) vs. Data Validation (`Ovado` + `ProB`):** `Atelier B`
  proves generic control algorithms once for all stations via interactive/SMT
  refinement obligations, and offloads station-specific track layouts to static
  data properties checked by `Ovado` and `ProB` (avoiding re-proving code per
  rail yard). `Prover iLock` compiles each station's boolean interlocking equations
  into `HLL` and discharges $k$-induction safety invariants automatically via SAT,
  accompanied by a separate binary proof-log checker (`Prover Certifier`).
- **Heuristic/CDCL Search (`OR-Tools` `CP-SAT`) vs. Exact Rational MIP
  Certificates (`VIPR`):** `OR-Tools` uses floating-point LP relaxations mixed
  with integer propagation for speed, whereas `VIPR` checks a standalone flat text
  certificate using exact GMP rationals (`viprchk`) with zero solver TCB.

##### 11.4 Ecosystem Comparisons
| Tool | Primary Application | Formal Specification Language | Verification / Solving Engine | CENELEC / Certificate Output |
| :--- | :--- | :--- | :--- | :--- |
| `Atelier B` | SIL 4 train control code synthesis | Abstract Machine Notation (AMN / B) | `bbatch` PO generator + `Atelier B` provers | Discharged refinement Proof Obligations (POs) |
| `Ovado` + `ProB` | Railway topology & parameter validation | B-Method set-theoretic predicates | `Ovado` evaluator + `ProB` Kodkod/CLP kernel | Dual-channel independent data validation report |
| `Prover iLock` | Interlocking control-table CAD & proof | `HLL` (synchronous stream equations) | Stålmarck SAT + $k$-induction | Machine-checkable `.plog` proof certificate |
| `EURIS` / `RobustRailS` | Geographical & route-table signaling | `EURIS` OO diagrams / RAISE `RSL` | SAL / SMT bounded model checking | Route-exclusivity & flank-protection proofs |
| `OR-Tools` (`CP-SAT`) | Supply-chain & fleet/crew scheduling | CP-SAT protobuf / MiniZinc | Lazy clause generation + simplex/cuts | Feasible schedule + dual bound (DRAT/LRAT experimental) |
| `VIPR` | Certified MILP optimality/infeasibility | `.vipr` linear inequality & branch tree | `viprchk` exact rational checker (C++/GMP) | Exact rational cutting-plane & branch tree proof |

##### 11.5 Formal Theory and Trusted Computing Base (TCB)
In railway interlocking (`Atelier B`, `Prover iLock`, `RobustRailS`), safety
reduces to three inductive invariants over track sections $T$, points (switches)
$P$, and routes $R$:
1. **Mutual Exclusion of Conflicting Routes:** $\forall r_1 \ne r_2 \in
   \text{Conflicts},\; \neg(\text{locked}(r_1) \land \text{locked}(r_2))$.
2. **Point Locking Under Occupancy / Route Locking:** No point $p \in r$ can
   move while route $r$ is locked or track section $t_p$ is occupied.
3. **Sequential Release & Flank Protection:** A sub-route lock releases only
   after the train's rear axle clears the section in topological order, and
   converging switches are locked in protective positions (`flank protection`).
In `VIPR`, every derived valid inequality $a^T x \ge \beta$ for a MILP $\{x \in
\mathbb{Q}^n \mid A x \ge b, x_I \in \mathbb{Z}^{|I|}\}$ is certified either as
a nonnegative rational Farkas combination $\lambda^T A x \ge \lambda^T b$
($\lambda \ge 0$) or by integer rounding $a \in \mathbb{Z}^n \implies a^T x \ge
\lceil \beta \rceil$.

##### 11.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Plan.Prog` is an abstract B machine (`Atelier B`), `RSL` route table
    (`RobustRailS`), or master logistics SLA contract; `L_Impl.Prog` is the
    concrete `B0` / `HLL` interlocking state machine or `OR-Tools` dispatch
    schedule.
  - `SemObs` (`obs`) projects onto externally visible train arrivals, conserved
    vehicle/container serial numbers, and SLA delivery timestamps.
  - `Partial.ub` (`defined = False`) triggers on: (1) **derailment or collision**
    (two trains occupying the same track section, or a switch moving under a
    train in `Prover iLock`/`RobustRailS`); (2) **`Ovado` topological data
    inconsistency** (e.g., non-symmetric neighbor links or braking distance
    exceeding signal sighting distance); or (3) **cold-chain spoilage / FAA Part
    117 crew rest violation / ghost inventory** in `OR-Tools` schedules.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Atelier B`'s gluing invariant $J(s_{\text{abs}}, s_{\text{conc}})$ between
    an abstract B machine and a concrete `B0` implementation maps directly onto
    `BehaviorCodec`: `decodeOut : L_B0.Out → Option L_Abs.Out` reconstructs the
    abstract set-theoretic state from concrete arrays/bitvectors, returning
    `none` if any `Ovado` data-representation invariant fails.
  - `Compiles L_AbsB L_B0 codec s t` is the exact encoding of `Atelier B`
    stepwise refinement!
  - `Abstracts L_VIPRLP L_MILP codec v s` certifies `VIPR`'s rational
    cutting-plane and branch-and-bound linear relaxations `v` over-approximating
    the discrete integer feasible set of `s`.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - In both railway signaling (`Prover iLock`, `Atelier B`) and logistics
    (`OR-Tools`), **the trivial safety bug is holding all signals red or
    canceling all shipments**: a deadlocked rail yard has zero collisions
    (`defined = True`)! `InhabitedPre` and `ProductiveOn` enforce **route
    availability and non-starvation**: for every valid train request or
    disruption scenario in `pre`, a collision-free route or recovery schedule
    actually completes.
  - `StepResult.externalCall boundaryInv branches` models **CBTC radio block
    handovers** and **3PL customs cold-chain custody transfers**, where
    `boundaryInv` verifies `Ovado` boundary consistency or Arrhenius thermal
    exposure integral $\int k(\Theta(t))\,dt \le \tau_{\max}$ at the exact
    instant of handover.
- **`VerificationResult` and `TrustPolicy`:**
  - Checks `Prover iLock` boolean $k$-induction proofs, `Ovado` finite set
    predicates, and `VIPR` exact rational Farkas/rounding certificates inside
    Lean, while tracking physical wheel-rail adhesion braking curves and
    customs delay distributions as explicit `TrustPolicy` waivers.

---

#### 12. Urban Traffic-Signal Network Control and Reactive Temporal-Logic Synthesis (`NEMA TS2`, `TuLiP`, `SUMO`)

`Basis: normative + source + derived`

##### 12.1 Goals and Primary Users
Traffic control engineers, cyber-physical systems researchers, and municipal
Department of Transportation (DOT) signal authorities use these standards and
tools to specify dual-ring intersection controllers, synthesize correct-by-construction
reactive controllers from Linear Temporal Logic (LTL), and simulate urban
corridor progression and emergency preemption.

##### 12.2 History and Intellectual Lineage
- **`NEMA TS2` (National Electrical Manufacturers Association Standards
  Publication TS 2-2003 / TS 2-2016 / ATC 5201) and `MUTCD` (Manual on Uniform
  Traffic Control Devices):** Defines the North American hardware/software
  standard for **Dual-Ring, Eight-Phase, Two-Barrier traffic controllers** paired
  with an independent hardware **Malfunction Management Unit (`MMU` / Conflict
  Monitor Unit `CMU`)** that physically disconnects field load switches into
  hardware flashing red/yellow if conflicting permissive outputs (`Green`/`Yellow`/
  `Walk`) are energized for $> 200\text{--}500\text{ ms}$ or if minimum
  clearance intervals are violated.
- **`TuLiP` (`tulip-control/tulip-control`, Wongpiromsarn, Topcu, Ozay, Xu,
  Murray, Caltech, *HSCC* 2011 / *ACM TECS*):** Python toolbox for **Temporal
  Logic Planning and Reactive Synthesis**: abstracts continuous state spaces
  into finite transition systems via polytope partitioning (`polytope`/`cvxopt`)
  and synthesizes Moore/Mealy reactive controllers satisfying **Generalized
  Reactivity(1) (`GR(1)`)** specifications ($\Box \Diamond \text{env\_live}
  \implies \Box \Diamond \text{sys\_live}$) using symbolic BDD games (`dd`/`omega`/
  `gr1c`).
- **`Eclipse SUMO` (`eclipse-sumo/sumo`, Krajzewicz, Erdmann, Behrisch, Bieker,
  DLR German Aerospace Center, 2001–2026):** Microscopic, continuous-space,
  discrete-time ($\Delta t = 0.1\text{--}1.0\text{ s}$) multi-modal traffic
  simulator supporting Krauss/IDM car-following dynamics, `NEMA` dual-ring
  controllers, railway grade-crossing preemption, and `TraCI` (Traffic Control
  Interface) closed-loop RL/MPC control.

##### 12.3 Design Philosophy and Tradeoffs
- **Hardware-Enforced Ring-Barrier Automaton (`NEMA TS2`) vs. Symbolic `GR(1)`
  Game Synthesis (`TuLiP`) vs. Microscopic Simulation (`SUMO`):** `NEMA TS2`
  constrains phase transitions by structural design: Ring 1 (`Phases 1–4`) and
  Ring 2 (`Phases 5–8`) may advance independently *within* a compatibility group
  (West-East vs. North-South) but must cross the **Barrier** simultaneously,
  structurally preventing perpendicular collisions. `TuLiP` generalizes this to
  arbitrary adversarial environment assumptions via $O(N^3)$ symbolic fixed-point
  games over `GR(1)` formulas, guaranteeing deadlock-freedom and fair phase
  service by construction. `SUMO` evaluates high-fidelity nonlinear queue
  spillback and shockwave propagation via `TraCI` but provides no formal safety
  proofs for RL policies.

##### 12.4 Ecosystem Comparisons
| System | Abstraction Layer | Core Model | Primary Safety / Liveness Mechanism |
| :--- | :--- | :--- | :--- |
| `NEMA TS2` + `MMU` | Intersection controller standard | Dual-ring 8-phase barrier + conflict matrix | Barrier synchronization + `MinGreen`/`Yellow`/`RedClear` timers + `MMU` cutout |
| `TuLiP` | Reactive synthesis compiler | Continuous polytope abstraction + `GR(1)` LTL | Symbolic BDD streett/Büchi 2-player game synthesis (`omega`/`gr1c`) |
| `Eclipse SUMO` | Microscopic traffic plant | Krauss/IDM car-following + `TraCI` API | Runtime collision/teleport detection & `NEMALight` emulator |

##### 12.5 Formal Theory and Trusted Computing Base (TCB)
`TuLiP` relies on **Bloem–Jobstmann–Piterman–Pnueli–Sa'ar `GR(1)` Game
Synthesis**: for specifications of the form
$$\left(\theta_e \land \Box \rho_e \land \bigwedge_{i=1}^m \Box \Diamond J_i^e\right) \implies_{\text{strict}} \left(\theta_s \land \Box \rho_s \land \bigwedge_{j=1}^n \Box \Diamond J_j^s\right),$$
winning states and strategies are computed in polynomial symbolic steps via nested
three-level $\mu$-calculus fixed points $\nu Z.\,\bigcap_{j=1}^n \mu Y.\,\bigcup_{i=1}^m
\nu X.\,( (J_j^s \land \text{CPre}(Z)) \lor \text{CPre}(Y) \lor (\neg J_i^e
\land \text{CPre}(X)) )$.

##### 12.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Corridor.Prog` is a `TuLiP` `GR(1)` specification or adaptive RL/MPC
    `TraCI` controller (`SUMO`); `L_NEMA.Prog` is the concrete `NEMA TS2`
    dual-ring 8-phase state machine.
  - `SemObs` (`obs`) is the driver- and pedestrian-visible signal-head transition
    trace (`Red`, `Yellow`, `Green`, `Walk`, `FDW`) and phase service timestamps.
  - `Partial.ub` (`defined = False`) triggers on: (1) **conflicting permissive
    phases** (`MMU` conflict matrix violation); (2) **barrier desynchronization**
    between Ring 1 and Ring 2; (3) **clearance interval truncation** (`Yellow`
    or pedestrian `FDW` shortened during preemption below ITE/MUTCD kinematic
    bounds); or (4) **queue spillback onto an active railway grade crossing**.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `decodeOut : L_NEMA.Out → Option L_Corridor.Out` decodes 16-channel load-switch
    bitmasks into abstract phase states, returning `none` on any bitmask that
    violates the `MMU` conflict table.
  - `Compiles L_GR1Spec L_NEMA codec s t` certifies a `TuLiP`-synthesized
    controller (or a verified Simplex safety shield wrapping an untrusted `SUMO`
    RL agent) against the `NEMA TS2` safety envelope.
  - `Abstracts L_PolytopeTS L_ContinuousTraffic codec v s` certifies `TuLiP`'s
    continuous-to-discrete cell-transmission / polytope abstraction step.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `InhabitedPre` and `ProductiveOn` capture the exact `GR(1)` **realizability
    and justice ($\Box \Diamond J_j^s$) obligation**: an intersection controller
    cannot vacuously avoid collisions by remaining in eternal all-red or starving
    minor-street/pedestrian calls (`ProductiveOn` proves bounded-horizon service
    for every detector call).
  - `StepResult.externalCall boundaryInv branches` models **Emergency Vehicle
    Preemption (EVP) and Railroad Grade-Crossing Preemption**, where
    `boundaryInv` guarantees that mandatory pedestrian `FDW`, `YellowChange`,
    `RedClearance`, and track-clearance green intervals complete before entering
    the preemption dwell state.
- **`VerificationResult` and `TrustPolicy`:**
  - Checks the `NEMA TS2` conflict matrix, barrier invariants, and `TuLiP`
    winning-strategy transition relation in Lean, while tracking civil-engineering
    approach grades, design speeds, and MUTCD $3.5\text{ ft/s}$ pedestrian
    walking-speed assumptions in `waived` under `TrustPolicy`.

---

#### 13. Formal Pragmatics, Multi-Agent Interaction Protocols, and HCI Mode-Confusion Verifiers (`PVSio-web`, `IVY`, `SCR`/`RSML-e`, `WebPPL-RSA`, `BSPL`)

`Basis: normative + source + derived`

##### 13.1 Goals and Primary Users
Avionics human-factors engineers (Airbus/Boeing cockpit Flight Mode Annunciators
[FMA]), FDA medical-device assurance teams (infusion pumps, ventilators),
computational linguists (formal pragmatics), and multi-agent systems researchers
use these tools to eliminate silent **automation mode confusion**, verify
human-machine keypad/display predictability, model Gricean conversational
implicature, and verify decentralized commitment protocols without shared-state
race conditions.

##### 13.2 History and Intellectual Lineage
- **`SCR` (Software Cost Reduction, Parnas, Heitmeyer, Naval Research Lab, 1978–
  2005) and `RSML-e` (Requirements State Machine Language without Events,
  Leveson, Heimdahl, Miller, MIT / Univ. of Minnesota / Rockwell Collins):**
  Pioneered tabular state-machine specifications for flight-control and TCAS II
  avionics, discovering that pilots suffer catastrophic **mode confusion** when
  automation transitions silently between control laws without a salient Flight
  Mode Annunciator change or when mode tables are non-deterministic (`disjointness`)
  or incomplete (`coverage`).
- **`PVSio-web` (`pvsioweb/pvsio-web`, Masci, Oladimeji, Zhang, Curzon,
  Thimbleby, Harrison, Formal Methods Group at NIA/NASA Langley & Swansea/QMUL,
  *CAV* 2015) and `IVY` (Campos & Harrison, Univ. of Minho, 2008–2020):**
  Connect interactive graphical prototypes of medical devices (e.g., Baxter
  Colleague / Alaris GP volumetric infusion pumps) directly to the **SRI PVS
  theorem prover** (`PVSio` evaluator) or NuSMV/Cadence SMV (`IVY`), proving FDA
  human-factors predictability properties (e.g., numeric keypad entry of `1.25`
  never silently registers as `125` due to decimal-point mode latching).
- **`WebPPL-RSA` (`probmods/webppl`, Goodman & Stuhlmüller, *DIPPL* 2014; Frank
  & Goodman, *Science* 2012 Rational Speech Act [RSA] framework):** Formalizes
  Gricean conversational pragmatics as recursive Bayesian inference in a
  probabilistic programming language: a literal listener $L_0(s \mid u) \propto
  \llbracket u \rrbracket(s) P(s)$ updates on truth conditions, a pragmatic
  speaker $S_1(u \mid s) \propto \exp(\alpha (\ln L_0(s \mid u) - C(u)))$ chooses
  utterances to maximize epistemic utility, and a pragmatic listener $L_1(s \mid
  u) \propto S_1(u \mid s) P(s)$ recovers scalar implicatures (`some` $\implies$
  `not all`) and presuppositions against Stalnaker's Common Ground.
- **`BSPL` (`munindar/bspl`, Blindingly Simple Protocol Language, Singh, Chopra,
  Christie, North Carolina State Univ. & Lancaster Univ., *AAMAS* / *IEEE
  Internet Comput.* 2011–2025):** Information-based multi-agent interaction
  protocol language where messages are typed purely by information causality
  (`key`, `in`, `out`, `nil` parameter bindings). Instead of fragile sequence
  diagrams, `BSPL` verifies **enactment safety** (no two agents ever bind the
  same `out` parameter to conflicting values for a given `key`) and **liveness**
  via local causality compilation (`Splee` / `TlaBSPL`).

##### 13.3 Design Philosophy and Tradeoffs
- **Tabular Determinism (`SCR`/`RSML-e`) vs. Interactive Theorem Proving on
  UI Prototypes (`PVSio-web`/`IVY`):** `SCR` and `RSML-e` enforce syntactic
  table disjointness and coverage on mode transition tables; `PVSio-web` links
  actual visual widget rendering (HTML/JS infusion-pump faceplate) to PVS
  higher-order logic theorems over user mental models (`predictability`,
  `reversibility`, `mode clarity`).
- **Information Causality (`BSPL`) vs. Epistemic Bayesian Pragmatics
  (`WebPPL-RSA`):** `BSPL` achieves race-free asynchronous multi-agent
  coordination by making every parameter transition monotonic in a key-indexed
  relational commitment store (`nil` $\to$ bound), whereas `WebPPL-RSA` models
  probabilistic ambiguity resolution over finite world states.

##### 13.4 Ecosystem Comparisons
| Tool | Domain | Formal Semantics | Key Bug Class Prevented |
| :--- | :--- | :--- | :--- |
| `PVSio-web` | Medical device & cockpit UIs | PVS higher-order logic + `PVSio` execution | Keypad decimal/unit mode latches & hidden state transitions |
| `IVY` | Interactive HCI model checking | Modal Action Logic (MAL) $\to$ NuSMV CTL/LTL | Unannounced mode changes & unreachable undo/escape states |
| `SCR` / `RSML-e` | Avionics flight-guidance tables | Tabular condition/event automata | Non-disjoint transitions, missing cases, & FMA mode confusion |
| `WebPPL-RSA` | Formal pragmatics & dialogue | Recursive Bayesian fixed point ($L_0 \to S_1 \to L_1$) | Presupposition failure, scalar ambiguity, & common-ground drift |
| `BSPL` | Multi-agent interaction protocols | Information-causality parameter lattice (`key`/`in`/`out`) | Conflicting decentralized commitments & asynchronous deadlock |

##### 13.5 Formal Theory and Trusted Computing Base (TCB)
Across `SCR`/`RSML-e`, `PVSio-web`, and `BSPL`, the central theorem is
**Observational Mode Transparency (Bisimulation Quotienting onto the User-Visible
Interface / Common Ground)**:
- Let $S_{\text{full}}$ be the concrete firmware state space and $\pi_{\text{UI}} :
  S_{\text{full}} \to D_{\text{display}}$ be the projection onto user-visible
  display annunciators. The system is **free of hidden mode confusion** if and
  only if for every user action $a$, the induced safety-critical control effect
  and next display state factor deterministically through $\pi_{\text{UI}}(s)$:
  $$\pi_{\text{UI}}(s_1) = \pi_{\text{UI}}(s_2) \implies \text{ControlMode}(s_1) = \text{ControlMode}(s_2) \land \pi_{\text{UI}}(\delta(s_1, a)) = \pi_{\text{UI}}(\delta(s_2, a)).$$
- In `BSPL`, a protocol is **safe** iff for every key tuple $\vec{k}$ and
  non-key parameter $p$, at most one agent can ever emit a message with `out` $p$
  on $\vec{k}$, and **live** iff every enactment can extend to bind all public
  output parameters.

##### 13.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_User.Prog` is the user's display-driven mental model (`PVSio-web`/`IVY`)
    or the public `BSPL` commitment contract; `L_Auto.Prog` is the full avionics
    or infusion-pump firmware (`RSML-e`) or decentralized agent enactment.
  - `SemObs` (`obs`) is **strictly the user-visible display state + physical
    actuator mode class** (in HCI) or the **shared Common Ground / `BSPL` key-value
    binding store** (in pragmatics/protocols).
  - `Partial.ub` (`defined = False`) triggers on: (1) **hidden mode divergence**
    (two internal firmware states $s_1, s_2$ with identical display panels
    $\text{obs}(s_1) = \text{obs}(s_2)$ that apply different infusion rates or
    flight control laws); (2) **`SCR` table non-disjointness**; (3) **`BSPL`
    parameter conflict** (two messages binding the same `out` parameter on the
    same `key` to different values); or (4) **unaccommodated presupposition** in
    `WebPPL-RSA`.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - Anneal's `BehaviorCodec` partial-bijection laws (`decodeOut_encodeOut`,
    `encodeOut_of_decodeOut`, and `obs_decodeOut`) **directly enforce the
    Mode-Transparency Law**: if `L_User.Out` is indexed purely by visible
    display annunciators, constructing a valid `BehaviorCodec` between `L_User`
    and `L_Auto` mathematically proves that no two distinct control modes can
    alias to the same display representation!
  - `Abstracts L_UserMentalModel L_AutoFirmware codec M_user M_auto` certifies
    `PVSio-web` and `RSML-e` mode-clarity obligations.
  - `Compiles L_BSPLSpec L_AgentEnactment codec s t` certifies that local agent
    enactments `t` satisfy the global `BSPL` protocol specification `s` without
    race conditions (`defined = True`).
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `ProductiveOn` proves `IVY` / `PVSio-web` **reversibility / escape-hatch
    liveness** (every reachable modal dialog admits a valid path back to a safe
    root state or emergency stop) and `BSPL` **protocol enactment liveness**
    (no decentralized deadlock where Agent A waits for an `in` parameter that
    Agent B requires A's `out` parameter to produce).
  - `StepResult.externalCall boundaryInv branches` models **human-in-the-loop
    `Confirm` actions** (`PVSio-web`), where `boundaryInv` asserts that all
    material dosage parameters (`rate`, `VTBI`, `units`) are rendered visibly on
    the primary display before accepting the `Confirm` button press.
- **`VerificationResult` and `TrustPolicy`:**
  - Discharges `SCR`/`RSML-e` table disjointness/coverage, `PVSio-web` display
    injectivity, and `BSPL` information-causality safety in Lean, while isolating
    human-factors assumptions (`PilotScansFMAOnAudioChime`, `WebPPL_RationalityAlpha`)
    as explicit `TrustPolicy` waivers.

---

#### 14. Causal Inference, `do`-Calculus Identification, and Differential Privacy Compilers (`Ananke`, `causaleffect`, `DoWhy`, `Dagitty`, `OpenDP`, `Tumult Core`)

`Basis: normative + source + derived`

##### 14.1 Goals and Primary Users
Epidemiologists, biostatisticians, econometricians, and privacy-preserving data
platform engineers use these compilers to determine whether an interventional
causal query $P(Y \mid \text{do}(X = x))$ is mathematically identifiable from
observational data under a Structural Causal Model (SCM) with unobserved
confounders, and to compile statistical queries over sensitive datasets with
machine-checked $(\varepsilon, \delta)$ or Rényi / Zero-Concentrated Differential
Privacy ($\text{zCDP}$) guarantees.

##### 14.2 History and Intellectual Lineage
- **Pearl's `do`-Calculus, `causaleffect` (`santikka/causaleffect`, Tikka &
  Karvanen, *J. Stat. Softw.* 2017), and `Dagitty` (Textor, van der Zander,
  Gilthorpe, Liśkiewicz, Ellison, *Int. J. Epidemiol.* 2016):** Built on Judea
  Pearl's three rules of `do`-calculus (1995) and **Shpitser & Pearl's complete
  `ID` / `IDC` algorithms** (*UAI* 2006) and **Tian & Pearl's c-component
  factorization** (2002). `Dagitty` computes minimal sufficient back-door
  adjustment sets and instrumental variables in browser/R; `causaleffect`
  symbolically executes the complete `ID`, `IDC`, `ID*`, and transportability
  algorithms over Acyclic Directed Mixed Graphs (ADMGs with directed causal edges
  $\to$ and bidirected latent-confounder arcs $\leftrightarrow$), outputting
  exact LaTeX observational probability formulas or a minimal **hedge** witness
  proving non-identifiability.
- **`Ananke` (`causal/ananke`, Bhattacharya, Nabi, Shpitser, Johns Hopkins
  Univ., *JMLR* / *UAI* 2020–2024) and `DoWhy` (`py-why/dowhy`, Sharma & Kiciman,
  Microsoft Research / PyWhy, 2018–2026):** `Ananke` extends causal identification
  to **nested Markov models** (fixing ratios over districts in ADMGs even when
  ordinary back-door/front-door criteria fail) and semiparametric primal-dual
  doubly robust estimators. `DoWhy` structures causal pipelines into a 4-stage
  state machine (`Model` $\to$ `Identify` $\to$ `Estimate` $\to$ `Refute`).
- **`OpenDP` (`opendp/opendp`, Gaboardi, Vadhan, Shoemate, SmartNoise, Harvard Univ.,
  2020–2026) and `Tumult Core` (`tmlt.core`, Berghel, Bohannon, Desfontaines,
  Estes, Gerlitz, Hay, Machanavajjhala, Miklau, Mironov, et al., Tumult Labs,
  2022–2026):** Implement the **Vadhan–Gaboardi Programming Framework for
  Differential Privacy** in Rust (`OpenDP`) and Python/Spark (`Tumult Core`).
  Every data transformation $T : (X, d_X) \to (Y, d_Y)$ carries a verified
  **stability map** bounding output distance $d_Y(T(x), T(x')) \le S_T(d_X(x,
  x'))$, and every randomized measurement $M : (Y, d_Y) \to \mathcal{D}(Z)$
  carries a **privacy map** bounding privacy loss $D_{\text{privacy}}(M(y),
  M(y')) \le P_M(d_Y(y, y'))$, using exact base-2 / rational arithmetic to prevent
  **Mironov's IEEE-754 floating-point least-significant-bit reconstruction
  attack** (*CCS* 2012).

##### 14.3 Design Philosophy and Tradeoffs
- **Complete Symbolic Identification (`causaleffect`/`Ananke`) vs. Workflow
  Orchestration (`DoWhy`/`Dagitty`):** `Dagitty` checks only covariate adjustment
  (back-door) and instrumental variables; `causaleffect` and `Ananke` implement
  complete recursive district/c-component decompositions (`ID` and nested fixing
  $\phi_V$), succeeding on front-door, Verma-constraint, and napkin graphs where
  covariate adjustment is impossible. `DoWhy` wraps identification with empirical
  sensitivity refuters (placebo treatment, random common cause).
- **Composable Stability/Privacy Maps (`OpenDP` / `Tumult Core`) vs. Ad-Hoc
  Noise Addition:** Naive DP libraries add `numpy.random.laplace` to unclipped
  SQL aggregates, which fails catastrophically via unbounded sensitivity
  ($\Delta f = \infty$) or IEEE-754 mantissa gaps. `OpenDP` and `Tumult Core`
  refuse to construct a `Measurement` unless a chain of `Transformation`s with
  bounded metric stability (e.g., `clamp(L, U)` + `bounded_sum`) connects the
  input dataset metric (`SymmetricDistance` $\le 1$) to the noise mechanism, and
  enforce floating-point-safe discrete Gaussian/Laplace sampling.

##### 14.4 Ecosystem Comparisons
| Tool | Domain | Input Specification | Output Artifact | Core Mathematical Guarantee |
| :--- | :--- | :--- | :--- | :--- |
| `causaleffect` | Symbolic causal identification | ADMG graph ($G = (V, E_d, E_b)$) + $P(y \mid \text{do}(x), z)$ | Observational functional or non-ID hedge | Soundness & completeness of Shpitser–Pearl `ID`/`IDC` |
| `Ananke` | Graphical & semiparametric causality | ADMG / Chain Graph + fixing schedule | Nested Markov functional + AIPW estimator | District fixing ($\phi$-operator) & semiparametric efficiency |
| `Dagitty` | Epidemiological DAG analysis | Causal DAG with exposure/outcome/latent tags | Minimal back-door sets & testable $d$-separations | Pearl back-door criterion & tetrad/conditional independence |
| `DoWhy` | End-to-end causal workflow | Graph + DataFrame + treatment/outcome | ATE/CATE estimate + refutation test suite | Explicit 4-step separation of identification from estimation |
| `OpenDP` | Composable differential privacy | Rust/Python combinator AST (`Transformation`/`Measurement`) | Privacy-certified release + $(\varepsilon, \delta)$/zCDP bound | Compositional stability/privacy maps + Mironov-safe samplers |
| `Tumult Core` | Spark-scale differential privacy | PySpark transformation tree + privacy accountant | Distributed DP table release | Exact rational/arb-precision zCDP / Pure-DP accounting |

##### 14.5 Formal Theory and Trusted Computing Base (TCB)
1. **Pearl's Three Rules of `do`-Calculus and Shpitser–Pearl `ID`:**
   - **Rule 1 (Insertion/deletion of observations):** $P(y \mid \text{do}(x), z,
     w) = P(y \mid \text{do}(x), w)$ if $(Y \perp\!\!\!\perp Z \mid X, W)_{G_{\overline{X}}}$.
   - **Rule 2 (Action/observation exchange):** $P(y \mid \text{do}(x), \text{do}(z),
     w) = P(y \mid \text{do}(x), z, w)$ if $(Y \perp\!\!\!\perp Z \mid X, W)_{G_{\overline{X}\underline{Z}}}$.
   - **Rule 3 (Insertion/deletion of actions):** $P(y \mid \text{do}(x), \text{do}(z),
     w) = P(y \mid \text{do}(x), w)$ if $(Y \perp\!\!\!\perp Z \mid X, W)_{G_{\overline{X}\overline{Z(W)}}}$.
   Every step of `causaleffect` and `Ananke` reduces to finite graph
   mutilations ($G_{\overline{X}}, G_{\underline{Z}}$) and decidable path-blocking
   ($d$-separation / $m$-separation) checks!
2. **OpenDP / Tumult Stability Composition Theorem:** If $T_1 : (M_0, d_0) \to
   (M_1, d_1)$ is $c_1$-stable and $T_2 : (M_1, d_1) \to (M_2, d_2)$ is
   $c_2$-stable, then $T_2 \circ T_1$ is $(c_2 \cdot c_1)$-stable; composing with
   an $\varepsilon$-DP measurement $M$ yields $(c_2 c_1 \varepsilon)$-DP. Currently,
   `OpenDP` tracks these proofs in human-written LaTeX companion documents
   (`proof.tex` files paired with Rust modules) rather than machine-checked
   theorem-prover kernels.

##### 14.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - *Causal Compiler:* `L_Interv.Prog` is an interventional query $P(Y \mid
    \text{do}(X), Z)$ over an SCM $\mathcal{M}$ compatible with ADMG $\mathcal{G}$;
    `L_Obs.Prog` is the compiled purely observational probability functional
    output by `causaleffect` or `Ananke`. `SemObs` is the target probability
    distribution over $Y$.
  - *DP Compiler:* `L_DPSpec.Prog` is a statistical query specification with
    privacy ceiling $(\varepsilon_{\max}, \delta_{\max})$; `L_OpenDP.Prog` is a
    chained `OpenDP` / `Tumult Core` pipeline. `SemObs` is the released output
    distribution paired with the certified privacy ledger $(\varepsilon_{\text{used}},
    \delta_{\text{used}})$.
  - `Partial.ub` (`defined = False`) triggers on: (1) **invalid `do`-calculus
    step or collider bias** (applying Rule 1/2/3 when the mutilated-graph
    $d$-separation side condition fails, or encountering a Shpitser–Pearl
    **hedge** witness); (2) **positivity violation** (dividing by $P(X \mid Z) =
    0$); (3) **unbounded DP sensitivity** (omitting a `clamp` transformation
    before `sum` in `OpenDP`, so $S_T(1) = \infty$); (4) **privacy budget
    overrun** ($\varepsilon_{\text{used}} > \varepsilon_{\max}$); or (5)
    **Mironov floating-point LSB leakage**.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - **Pearl's `do`-calculus and `causaleffect`/`Ananke` identification are
    literally verified compilation (`Compiles L_Interv L_Obs codec P_do P_obs`)**:
    lowering an interventional expression containing $\text{do}(X)$ into an
    observational estimator containing only standard conditional probabilities
    $P(V)$ via a chain of `Compiles.trans` steps, where each step is guarded by
    a decidable Lean check of $d$-separation in $G_{\overline{X}\underline{Z}}$!
  - In `OpenDP` / `Tumult Core`, `BehaviorCodec` maps exact mathematical discrete
    distributions to fixed-point/dyadic sampler bitstrings, returning
    `decodeOut = none` on any naive IEEE-754 float state susceptible to Mironov's
    mantissa-gap attack.
  - `Abstracts L_StabilityBound L_DataPipeline codec v s` certifies `OpenDP`'s
    relational stability/privacy maps ($d_{\text{out}} \le c \cdot d_{\text{in}}$)
    in Lean, replacing `OpenDP`'s manual `proof.tex` files with kernel-checked
    theorems!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `InhabitedPre` and `ProductiveOn` rule out the trivial privacy/epistemic
    bypass where a pipeline achieves $\varepsilon = 0$ privacy or zero bias by
    outputting constant noise or rejecting all datasets (`pre = ∅`):
    `ProductiveOn` proves that for every dataset/SCM satisfying positivity in
    `pre`, the compiled estimator or `OpenDP` measurement produces a valid
    output within utility bounds.
  - `StepResult.externalCall boundaryInv branches` models **interactive adaptive
    privacy composition (`OpenDP` `Queryable` / `Tumult` `PrivacyAccountant`)**
    and **reusable holdout / clinical-trial DSMB unblinding**, where
    `boundaryInv` checks that remaining privacy budget $\varepsilon_{\max} -
    \varepsilon_{\text{spent}} \ge \varepsilon_{\text{query}}$ (and pre-registered
    SAP hash lock) holds before executing the next adaptive query.
- **`VerificationResult` and `TrustPolicy`:**
  - Machine-checks every `do`-calculus $d$-separation side condition (`Dagitty`/
    `causaleffect`/`Ananke`) and `OpenDP`/`Tumult` stability composition in Lean,
    while recording **untestable domain causal assumptions**—specifically the
    absence of omitted bidirected arcs in $\mathcal{G}$ (`Unconfoundedness_X_Y_given_Z`,
    `SUTVA_NoInterference`, `Faithfulness`)—as explicit `Obligation` IDs in
    `waived` under `TrustPolicy` (an **Epistemic Bill of Materials**).

---

#### 15. Smart-Grid AC Optimal Power Flow and Carbon-Accounting Provenance (`PowerModels.jl`, `MATPOWER`, `WBCSD PACT`, `EnergyTag`)

`Basis: normative + source + derived`

##### 15.1 Goals and Primary Users
Transmission and distribution system operators (ISOs/RTOs/DSOs), power-systems
optimization researchers, and corporate/supply-chain sustainability auditors
use these frameworks to solve AC Optimal Power Flow (AC-OPF) and $N-1$
security-constrained unit commitment, and to track hourly 24/7 Carbon-Free
Energy (CFE) certificates and Scope 3 Product Carbon Footprints (PCFs) without
double-counting.

##### 15.2 History and Intellectual Lineage
- **`MATPOWER` (`MATPOWER/matpower`, Zimmerman, Murillo-Sánchez, Thomas, Cornell
  Univ., *IEEE Trans. Power Syst.* 1997–2024):** Established the global reference
  data format (`.m` case files: `bus`, `gen`, `branch`, `gencost`) and
  Newton-Raphson / interior-point (`MIPS`) solvers for steady-state AC and DC
  power flow and Optimal Power Flow.
- **`PowerModels.jl` (`lanl-ansi/PowerModels.jl`, Coffrin, Bent, Sundar, Ng,
  Lubin, Los Alamos National Laboratory, *PSCC* 2018–2026):** Built a declarative
  Julia/JuMP algebraic modeling hierarchy that decouples **power network problem
  specifications** (`OPF`, `PF`, `OTS` [Optimal Transmission Switching], `TNEP`)
  from **mathematical power-flow formulations**: exact non-convex polar/rectangular
  (`ACPPowerModel`, `ACRPowerModel`), linearized `DCMPPowerModel`, Second-Order
  Cone (`SOCWRPowerModel`, Jabr relaxation), Quadratic Convex (`QCRMPowerModel`,
  Coffrin–Hijazi–Van Hentenryck), and Semidefinite Programming (`SDPWRMPowerModel`,
  Lavaei–Low relaxation).
- **`WBCSD PACT` (Partnership for Carbon Transparency / Pathfinder Framework
  v2.1 & Tech Specs, World Business Council for Sustainable Development, 2021–
  2026):** Standardized the global cradle-to-gate Scope 3 Product Carbon
  Footprint (PCF) calculation rules and REST API data-exchange schema (`ProductFootprint`,
  `CarbonFootprint`, `DataQualityIndicators`, primary data share [PDS], and
  mass/economic allocation conservation across multi-tier bills of materials).
- **`EnergyTag` (Granular Certificate [GC] Standard v2 & API Specification,
  2021–2026):** Defined the normative standard for **hourly/sub-hourly Granular
  Certificates**, replacing annual unbundled RECs/GOs with time-stamped,
  grid-bidding-zone-tagged MWh certificates and strict battery storage
  charge/discharge retirement rules ($\eta_{\text{RTE}} \cdot E_{\text{charged}}
  \ge E_{\text{discharged}}$) to prevent temporal and spatial greenwashing.

##### 15.3 Design Philosophy and Tradeoffs
- **Non-Convex Local Interior-Point (`MATPOWER` / `ACPPowerModel`) vs. Convex
  Relaxation Hierarchy (`PowerModels.jl` `SOCWR`/`QCRM`/`SDPWRM`):** Solving
  exact non-convex AC-OPF via Ipopt (`ACPPowerModel`) finds feasible local
  minima quickly but cannot prove global optimality or certify that an $N-1$
  contingency problem is truly infeasible. `PowerModels.jl`'s convex relaxations
  (`SOCWR`, `QCRM`, `SDPWRM`) provide rigorous dual lower bounds and infeasibility
  certificates over all complex voltage phasors $V_i = |V_i| e^{j\theta_i}$ by
  lifting $W_{ij} = V_i V_j^*$ into a convex cone ($\|W_{ij}\|^2 \le W_{ii}
  W_{jj}$), trading a relaxation gap when the rank-1 condition fails.
- **Supply-Chain Mass Balance (`PACT`) vs. Temporal Grid Matching (`EnergyTag`):**
  `PACT` enforces cradle-to-gate stoichiometric conservation of embodied
  $\text{kgCO}_2\text{e}$ across chemical/manufacturing Bills of Materials (sum
  of co-product allocated footprints equals total facility process + upstream
  emissions), whereas `EnergyTag` enforces hourly temporal exclusivity and
  loss-adjusted battery storage shifting for Scope 2 electricity.

##### 15.4 Ecosystem Comparisons
| System | Domain | Core Mathematical / Data Model | Primary Soundness Guarantee |
| :--- | :--- | :--- | :--- |
| `MATPOWER` | AC / DC Power Flow & OPF | Complex nodal admittance $I = Y_{\text{bus}} V$ + `MIPS` | KCL/KVL residual convergence & thermal/voltage bounds |
| `PowerModels.jl` | Multi-formulation power optimization | Non-convex AC $\sqsubseteq$ `QCRM` $\sqsubseteq$ `SOCWR` / `SDPWRM` | Convex outer-approximation bounds & infeasibility certificates |
| `WBCSD PACT` | Scope 3 Product Carbon Footprints | Directed acyclic BOM mass-balance graph | Co-product allocation conservation ($\sum \alpha_k = 1$) & audit trail |
| `EnergyTag` | 24/7 Hourly Granular Certificates | Time-indexed $(t, \text{zone})$ MWh certificate ledger | Single-claim retirement exclusivity & storage round-trip loss conservation |

##### 15.5 Formal Theory and Trusted Computing Base (TCB)
1. **Power-Flow Relaxation Inclusion (`PowerModels.jl`):** For any power network,
   the feasible set of exact AC power flow $\mathcal{F}_{\text{AC}}$ is contained
   in the Quadratic Convex (`QCRM`) and Jabr SOCP (`SOCWR`) relaxations:
   $$\mathcal{F}_{\text{AC}} \subseteq \mathcal{F}_{\text{QCRM}} \subseteq \mathcal{F}_{\text{SOCWR}}.$$
   Moreover, around any approximate numerical AC power-flow root $x_0$ returned
   by `MATPOWER`/Ipopt, **Krawczyk's interval Newton operator**
   $$K(X) = x_0 - C \cdot F(x_0) + (I - C \cdot F'(X))(X - x_0)$$
   certifies with 100% mathematical rigor in interval arithmetic that a true
   continuous AC power-flow solution $x^* \in X$ exists and satisfies all bus
   voltage bounds $[V_{\min}, V_{\max}]$ and branch thermal limits $|S_{ij}| \le
   S_{ij}^{\max}$.
2. **Token / Mass-Balance Conservation (`PACT` & `EnergyTag`):** Every `EnergyTag`
   storage transformation and `PACT` co-product split is a linear nonnegative
   mass-conserving map on conserved quantities $(\text{MWh}, \text{kgCO}_2\text{e})$.

##### 15.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Grid.Prog` is an AC-OPF dispatch or Virtual Power Plant (VPP) disaggregation
    schedule (`PowerModels.jl`/`MATPOWER`) or a `PACT`/`EnergyTag` certificate
    transformation graph.
  - `SemObs` (`obs`) projects onto boundary substation $(P, Q)$ injections,
    $N-1$ security status, and total conserved $\text{kgCO}_2\text{e}$ / MWh
    across the system boundary.
  - `Partial.ub` (`defined = False`) triggers on: (1) **KCL/KVL non-convergence
    / voltage collapse** ($K(X) \not\subset \operatorname{int}(X)$); (2) **bus
    voltage or branch thermal violation** ($|V_i| \notin [0.95, 1.05]$ or
    $|S_{ij}| > S_{ij}^{\max}$ in base case or any $N-1$ contingency); (3)
    **`EnergyTag` double-counting or perpetual-motion battery storage**
    (issuing discharged GCs exceeding $\eta_{\text{RTE}} \cdot E_{\text{charged}}$
    or matching across congested zones); or (4) **`PACT` co-product allocation
    leakage** ($\sum_k \text{PCF}_k < \text{TotalFacilityEmissions}$).
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - **Notice how `PowerModels.jl`'s formulation hierarchy is a textbook instance
    of Anneal's `Abstracts`:** `Abstracts L_SOCWR L_ACPF codec v s` and
    `Abstracts L_QCRM L_ACPF codec v' s` express that the convex `SOCWR` and
    `QCRM` models soundly over-approximate the exact non-convex AC power-flow
    equations `s`!
  - For `PACT` and `EnergyTag`, `BehaviorCodec` (`decodeOut_encodeOut` and
    `encodeOut_of_decodeOut`) enforces **1-to-1 serial-numbered Granular
    Certificate conservation**, while `obs_decodeOut` proves that splitting or
    blending chemical precursor batches preserves total embodied $\text{kgCO}_2\text{e}$.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `InhabitedPre` and `ProductiveOn` rule out the **blackout / load-shedding
    safety bypass**: opening all circuit breakers ($P_{\text{gen}} = P_{\text{load}}
    = 0$) satisfies every thermal line limit $0 \le S_{ij}^{\max}$, but fails
    `ProductiveOn` on demand satisfaction! Constructively, `ProductiveOn` is
    discharged via a Krawczyk interval-Newton witness $K(X) \subset
    \operatorname{int}(X)$ proving a genuine AC solution serving the load exists.
  - `StepResult.externalCall boundaryInv branches` models **TSO–DSO substation
    interchange** and **cross-company `PACT` API PCF exchanges**, where
    `boundaryInv` verifies the DSO capability envelope or `PACT` cryptographic
    data-quality signature before accepting the external payload.
- **`VerificationResult` and `TrustPolicy`:**
  - Checks Krawczyk AC power-flow existence enclosures, `SOCWR` dual bounds, and
    `PACT`/`EnergyTag` ledger conservation in Lean, while isolating physical
    $\pi$-equivalent transmission line impedance parameters and secondary LCA
    emission factors (e.g., `Ecoinvent_v3_10`, `IPCC_AR6_GWP100`) as explicit
    `TrustPolicy` waivers.

---

#### 16. Deep-Space Autonomous Science Scheduling, Timeline Executives, and Ephemeris Geometry (`ASPEN`, `CLASP`, `Aerie`, `EUROPA`, `PLEXIL`, `NAIF SPICE`)

`Basis: normative + source + derived`

##### 16.1 Goals and Primary Users
Spacecraft mission planners, flight software engineers, and astrodynamics
navigation teams at NASA JPL, NASA Ames, ESA, and commercial space programs use
these tools to synthesize conflict-free spacecraft command timelines (managing
attitude slews, solar keep-out cones, eclipse battery depth-of-discharge, and
solid-state recorder buffers), execute autonomous onboard plans across
light-hours of latency, and compute high-precision planetary ephemerides and
instrument field-of-view geometry.

##### 16.2 History and Intellectual Lineage
- **`NAIF SPICE` (`CSPICE` / `Toolkit`, Acton, Bachman, Semenov, Wright, NASA
  JPL Navigation and Ancillary Information Facility, 1984–2026):** The ground-truth
  astrodynamics and spacecraft geometry engine used across virtually every
  planetary mission. It evaluates Chebyshev polynomial planetary/spacecraft
  ephemerides (`SPK`, e.g., `DE440`), body orientations (`PCK`), spacecraft
  attitude quaternions and Euler angles (`CK`), instrument field-of-view boresight
  cones (`IK`), frame transformation trees (`FK`), and spacecraft clock
  correlations (`SCLK`).
- **`ASPEN` (Automated Scheduling and Planning Environment, Chien, Rabideau,
  Knight, Sherwood, Engelhardt, JPL, 1997–2024) and `CLASP` (Compressed
  Large-scale Activity Scheduling and Planning, Knight, Rabideau, JPL):**
  `ASPEN` pioneered timeline-based constraint modeling and **iterative repair**
  (heuristic conflict resolution over state, resource, and temporal reservation
  timelines) and flew onboard **Earth Observing-1 (`EO-1` Autonomous Sciencecraft
  Experiment)** and served `Orbiting Carbon Observatory` (`OCO-2/3`) and `NISAR`.
  `CLASP` specializes in long-range horizon scheduling for pushbroom/radar
  instruments coupled with `SPICE` geometric visibility windows.
- **`EUROPA` (`nasa/europa`, Frank, Jónsson, Morris, Rajan, McGann, NASA Ames,
  2000–2016):** Constraint-based temporal interval planner (`NDDL` modeling
  language) built around a unified **Simple Temporal Network (`STN`)** and flaw-resolution
  search engine; flew in the Mars Exploration Rovers (`Spirit`/`Opportunity`)
  ground MAPGEN system and `Deep Space 1` Remote Agent heritage.
- **`Aerie` (`NASA-AMMOS/aerie`, NASA JPL Advanced Multi-Mission Operations
  System, 2021–2026):** Modern open-source Java/TypeScript multi-mission
  planning, simulation, and constraint-checking platform deployed for **Europa
  Clipper**, **Mars Sample Return**, and **Psyche**. Missions write Java mission
  models that emit discrete/continuous state profiles; `Aerie` runs discrete-event
  simulations, schedules activities, and evaluates declarative temporal/resource
  constraints.
- **`PLEXIL` (`nasa/plexil`, Plan Execution Interchange Language, Verma, Estlin,
  Jónsson, Pasareanu, Simmons, Tso, NASA Ames & JPL, 2005–2026):** Deterministic,
  reactive onboard execution language and executive (flown on `LADEE`, ISS
  Robonaut, and Mars rover prototypes). Every `PLEXIL` plan is a hierarchical tree
  of nodes governed by a strict **7-state synchronous transition automaton**
  (`INACTIVE` $\to$ `WAITING` $\to$ `EXECUTING` $\to$ `FINISHING` / `ITERATION_ENDED`
  $\to$ `FINISHED`, with `FAILING`) guarded by explicit `StartCondition`,
  `InvariantCondition`, `PreCondition`, `PostCondition`, and `ExitCondition`
  monitors evaluated at every micro-step until quiescence.

##### 16.3 Design Philosophy and Tradeoffs
- **Ground/Horizon Timeline Scheduling (`ASPEN`/`CLASP`/`EUROPA`/`Aerie`) vs.
  Synchronous Onboard Reactive Execution (`PLEXIL`):** `ASPEN`, `EUROPA`, and
  `Aerie` optimize multi-day/multi-orbit activity placements against complex
  resource models (battery State-of-Charge integrals, SSR memory partitions,
  `SPICE` target visibility cones). However, at execution time in deep space,
  actual durations and power draws deviate from nominal predictions; `PLEXIL`
  provides a small, deterministic, formally analyzable reactive executive that
  continuously monitors `InvariantCondition`s and triggers local fault-recovery
  nodes within milliseconds if a sensor or actuator deviates.
- **Declarative Interval Constraints (`EUROPA`) vs. Imperative Java Simulation
  Models (`Aerie`):** `EUROPA`'s declarative `NDDL` enables backtracking constraint
  propagation (Floyd-Warshall / Bellman-Ford over Simple Temporal Networks) but
  struggles with complex nonlinear orbital/thermal dynamics; `Aerie` lets engineers
  write expressive Java discrete-event simulators paired with `SPICE` JNI calls,
  trading automatic backward constraint propagation for high-fidelity subsystem
  modeling.

##### 16.4 Ecosystem Comparisons
| System | Primary Role | Core Representation | Verification / Safety Mechanism |
| :--- | :--- | :--- | :--- |
| `NAIF SPICE` | Ephemeris & attitude geometry | Chebyshev `SPK`, quaternion `CK`, FOV `IK` | Frame-tree transformations & occultation/keep-out geometry Finder (`GF`) |
| `ASPEN` / `CLASP` | Iterative-repair & pushbroom scheduling | State/depletable/non-depletable timelines | Timeline conflict detection (power, SSR, slews) + repair heuristics |
| `EUROPA` | Constraint-based temporal planning | Interval tokens + Simple Temporal Network (`STN`) | Negative-cycle STN consistency ($\forall i, d_{ii} \ge 0$) + flaw resolution |
| `Aerie` | Multi-mission simulation & scheduling | Java discrete-event profiles + constraint DSL | Continuous/discrete profile violation windows (`Europa Clipper`) |
| `PLEXIL` | Onboard reactive plan executive | 7-state synchronous node tree + guard conditions | Synchronous micro-step quiescence + `InvariantCondition` fault monitors |

##### 16.5 Formal Theory and Trusted Computing Base (TCB)
1. **Simple Temporal Network (`STN`) Consistency (`EUROPA`/`ASPEN`):** A network
   of timepoints $t_i$ with binary duration bounds $l_{ij} \le t_j - t_i \le
   u_{ij}$ is dynamically consistent if and only if its distance graph contains
   no negative-weight cycles, witnessed by a potential vector $\pi \in
   \mathbb{Q}^n$ satisfying $\pi_j - \pi_i \le u_{ij}$ for every edge (checkable
   in $O(|E|)$ once solved).
2. **`PLEXIL` Synchronous Quiescence Semantics (Dowek, Muñoz, Păsăreanu, *NASA
   Formal Methods* / PVS & Java PathFinder formalizations):** Given an external
   event, the `PLEXIL` executive executes internal node state transitions until a
   quiescent fixed point is reached; soundness requires **determinism** (no
   race conditions on shared command variables between sibling nodes) and
   **bounded micro-step termination** (no cyclic `RepeatCondition`/`StartCondition`
   livelock).
3. **$SO(3)$ Attitude Keep-Out Geometry (`SPICE`):** For instrument boresight
   $\vec{b}_{\text{body}} \in S^2$, spacecraft attitude quaternion $q(t) \in
   \text{Spin}(3)$, and unit Sun/bright-body vector $\vec{s}_\odot(t)$ from
   `SPK`, optical safety requires:
   $$\forall t \in [t_0, t_1], \qquad \langle q(t)\,\vec{b}_{\text{body}}\,q(t)^{-1},\; \vec{s}_\odot(t) \rangle \le \cos \theta_{\text{keepout}}.$$

##### 16.6 Mapping onto Anneal's 4 `trusted/` Primitives
- **`Language SemObs` and `Partial`:**
  - `L_Campaign.Prog` is a high-level science observation campaign (`CLASP`/
    `Aerie` science goals); `L_Timeline.Prog` is a compiled time-tagged sequence
    or `PLEXIL` execution plan coupled with `SPICE` ephemeris/attitude profiles.
  - `SemObs` (`obs`) projects onto completed science observation records,
    downlinked CCSDS telemetry frames, and spacecraft survival status.
  - `Partial.ub` (`defined = False`) triggers on: (1) **`SPICE` bright-body
    keep-out cone violation** (slewing a cryogenic spectrometer across the Sun or
    bright planetary limb); (2) **eclipse battery Depth-of-Discharge (DoD)
    underflow** ($\text{SoC}(t) < \text{SoC}_{\text{survival}}$) or survival-heater
    propellant freeze-out; (3) **SSR priority-data overwrite** before ground
    pass acknowledgment; (4) **negative-cycle `STN` temporal inconsistency** in
    `EUROPA`; or (5) **`PLEXIL` micro-step livelock / sibling write-write race**.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `decodeOut : L_Timeline.Out → Option L_Campaign.Out` maps low-level attitude
    quaternion slews, heater toggles, and SSR pointer updates to completed
    science observation events, returning `none` if any attitude quaternion is
    unnormalized or mid-slew (`obs_decodeOut` preserves science target coverage).
  - `Compiles L_Campaign L_PLEXIL codec s t` certifies that a `PLEXIL` onboard
    plan or `Aerie`/`ASPEN` command sequence `t` achieves the science campaign
    `s` while maintaining 100% `SPICE` keep-out, thermal, power, and memory
    safety (`defined = True`).
  - `Abstracts L_ResourceEnvelope L_SpacecraftSim codec v s` formalizes `ASPEN`/
    `Aerie`'s piecewise-linear resource profile envelopes `v` over-approximating
    full nonlinear radiative thermal ($\sigma \epsilon A T^4$) and Peukert
    battery discharge ODEs `s`.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Anti-Safe-Mode-Lockout Guarantee (`ProductiveOn`):** A spacecraft can
    trivially satisfy all `SPICE` Sun-keep-out, battery-SoC, and thermal survival
    constraints (`defined = True`) by dropping immediately into **eternal Safe
    Mode** (pointing solar arrays at the Sun, shutting off all science
    instruments, and ignoring every flyby target)! Pairing `Compiles` with
    `ProductiveOn` proves that on nominal flyby conditions (`NominalPre`), the
    schedule completes the mandatory science observations, while on hardware
    fault conditions (`FaultPre`), `PLEXIL`'s `FailSafe` handler reaches a stable
    sun-pointed recovery attitude within $T_{\text{safe}}$.
  - `EventualBehaviorOf` proves that `PLEXIL`'s synchronous internal micro-step
    loop always reaches quiescence in finitely many transitions per external
    tick.
  - `StepResult.externalCall boundaryInv branches` models **autonomous onboard
    science triggers** (e.g., `EO-1` / Europa plume or transient detection
    requesting an opportunistic `ASPEN`/`PLEXIL` target slew), where
    `boundaryInv` runs the verified `SPICE` keep-out and eclipse-SoC lookahead
    gate before admitting the slew into the active command queue.
- **`VerificationResult` and `TrustPolicy`:**
  - Checks `EUROPA` `STN` potential witnesses ($\pi_j - \pi_i \le u_{ij}$),
    `PLEXIL` micro-step determinism/termination, and interval Chebyshev `SPICE`
    keep-out bounds in Lean, while isolating `SPICE` `DE440` ephemeris
    covariance bounds and end-of-life solar-array radiation degradation factors
    (critical in Jupiter's radiation belts for Europa Clipper) as explicit
    `TrustPolicy` waivers.

---

### Cross-Domain Master Synthesis Matrix

| # | Tool Family | Primary Tools | `Partial.ub` (`defined = False`) | `decodeOut = none` | `Compiles` + `ProductiveOn` | `TrustPolicy` Waived Priors |
| :- | :--- | :--- | :--- | :--- | :--- | :--- |
| **1** | **Genetic Logic (GDA)** | `Cello 2.0`, `GEC`, `Eugene`, `Proto`, `SynBioHub`, `iBioSim`, `LOICA` | Ribosome/RNAP toxicity collapse; steady state in $(\theta_{\text{OFF}}, \theta_{\text{ON}})$ | Pre-settled transient RPU trajectory | NOR technology mapping + non-empty stable fixed point | UCF cytometry spline fits & chassis growth cutoffs |
| **2** | **CRNs & DSD** | `Visual DSD`, `Peppercorn`, `CRN++`, `Piperine`, `PRISM`, `Storm`, `Catalyst.jl`, `CRNT`, `BioNetGen` | Fuel gate starvation; ODE blowup; `CRN++` clock-phase overlap | Non-resting `Peppercorn` 3-way/4-way intermediate complex | DSD pathway refinement + critical siphon persistence | `Piperine`/`NUPACK` blunt-end leak rate separation |
| **3** | **Tile & DNA Origami** | `Xgrow`, `ISU TAS`, `caDNAno`, `DAEDALUS` | Glue mismatch; nondeterministic site; non-Eulerian scaffold loop | Partially assembled $k \times k$ supertile block | Local determinism confluence + geometric canyon freedom | kTAM $(G_{\text{mc}}, G_{\text{se}})$ & $10.5\text{ bp/turn}$ strain |
| **4** | **Digital Microfluidics** | `Puddle`, `BioCoder`, `MFSimStatic`, `BioStream`/`AquaCore`, `OpenDrop` | Droplet merge ($\|p_i - p_j\|_\infty \le 1$); dirty cell; pin tug | Mid-mix $2 \times 3$ rotary loop or mid-transit state | Assay DAG dilution accuracy + deadlock-free routing | Empirical rotary mixing cycle counts for viscosity $\mu$ |
| **5** | **Flux Balance (FBA)** | `COBRApy`, `MEMOTE`, `StrainDesign`, `eQuilibrator`, `QSopt_ex` | Atomic/charge imbalance ($E S \ne 0$); Type-III loop; lethality | Non-steady-state metabolite accumulation ($S v \ne 0$) | `QSopt_ex` Farkas growth-coupled yield + viable $v^* > 0$ | `eQuilibrator` group-contribution $\Delta_f G'^\circ$ priors |
| **6** | **Physiological Control** | `UVA/Padova` (`simglucose`), `OpenAPS`, `Loop`, `Flow*` | Severe hypoglycemia ($G < 54$); IOB overdose stacking | Active postprandial digestion transient | `Flow*` Taylor flowpipe safety + active euglycemia return | `UVA/Padova` cohort bounds & CGM transport lag |
| **7** | **RNA Folding** | `NUPACK 4`, `ViennaRNA`/`Barriers`/`Treekin`, `LinearFold`, `LinearDesign`, `Multistrand` | MFE degeneracy; ensemble defect $> \epsilon$; G-quadruplex | High-energy unzipped kinetic intermediate | Inverse-fold MFE/defect proof + trap-free saddle path | Turner 2004 loop parameters & pseudoknot heuristics |
| **8** | **Ecology & Open Petri** | `Ecopath`/`Ecosim`, `SLiM 4`, `MGDrivE`, `AlgebraicPetri.jl` | Keystone extinction; $EE_i > 1$; non-stochastic drive cube | Post-disturbance seasonal transient | Goh/Hofbauer Lyapunov permanence + interior $N^* > 0$ | Field diet matrix $DC_{ji}$ & CRISPR cleavage rates |
| **9** | **PDEs, Float & AD** | `Firedrake`, `FEniCSx`, `Dedalus`, `Devito`, `VCFloat2`, `Enzyme` | `NaN`/`±Inf`; inverted simplex ($\det J \le 0$); CFL $> 1$; tape alias | Non-finite IEEE-754 bitvector (`NaN`/`Inf`) | `VCFloat2` Taylor bound / `Enzyme` cotangent + solver convergence | Continuum solution regularity $u \in H^s(\Omega)$ |
| **10** | **Math Certificates** | `Flyspeck`, `Lean Blueprint`, `AlphaProof`, `AlphaGeometry 2`, `SnapPy`, `Regina`, `Kenzo`, `CakeLPR` | Invalid Pachner move; $\operatorname{Im}(z_i) \le 0$; $d h + h d \ne \text{id} - g f$; bad LPR | Unreduced chain / non-normal intermediate | `Kenzo` BPL / `CakeLPR` soundness + 100% orbit coverage | Unproved `Blueprint` lemmas & classification axioms |
| **11** | **Rail & MILP Logistics** | `Atelier B`, `Ovado`, `ProB`, `Prover iLock`, `EURIS`, `RobustRailS`, `OR-Tools`, `VIPR` | Conflicting route lock; switch under train; cold-chain spoilage | Concrete state violating `Ovado` gluing invariant | B-refinement / `VIPR` cut proof + non-starvation liveness | Wheel-rail braking adhesion curves & customs buffers |
| **12** | **Traffic Control** | `NEMA TS2`, `TuLiP`, `Eclipse SUMO` | Conflicting greens (`MMU` fault); truncated `Yellow`/`FDW` | Invalid load-switch channel bitmask | `TuLiP` `GR(1)` safety shield + bounded-wait phase service | Approach grade & MUTCD $3.5\text{ ft/s}$ walk speed |
| **13** | **HCI & Pragmatics** | `PVSio-web`, `IVY`, `SCR`/`RSML-e`, `WebPPL-RSA`, `BSPL` | Hidden mode transition; `BSPL` `out`-key conflict; presupposition fail | Unquiesced UI frame / uncommitted speech act | Bijective display mode transparency + escape/enactment liveness | Pilot FMA scan on chime & Gricean speaker alpha |
| **14** | **Causality & Privacy** | `Ananke`, `causaleffect`, `DoWhy`, `Dagitty`, `OpenDP`, `Tumult Core` | Unblocked back-door/hedge; unbounded sensitivity; Mironov float leak | Non-dyadic float susceptible to LSB attack | `do`-calculus compilation / `OpenDP` stability + utility witness | Untestable SCM causal DAG structure (Epistemic BOM) |
| **15** | **Grid & Carbon** | `PowerModels.jl`, `MATPOWER`, `WBCSD PACT`, `EnergyTag` | Voltage collapse; $N-1$ thermal overload; GC double-counting | Unconverged Newton iterate | `SOCWR`/`QCRM` abstraction + Krawczyk root existence | $\pi$-line impedance model & IPCC/Ecoinvent LCA factors |
| **16** | **Space Autonomy** | `ASPEN`, `CLASP`, `Aerie`, `EUROPA`, `PLEXIL`, `NAIF SPICE` | `SPICE` Sun keep-out violation; battery DoD floor; `PLEXIL` livelock | Unnormalized quaternion / mid-quiescence micro-step | Keep-out/power safety + science completion (no eternal safe-mode) | `DE440` ephemeris covariance & radiation degradation |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **ARCTIC (`daigolab/ARCTIC`), BioCRNpyler, BioModelAnalyzer
  (`Microsoft/BioModelAnalyzer`), RBS Calculator, and Double Dutch:** Context-
  aware genetic circuit technology mappers bounding retroactivity/ribosome
  titration (`Abstracts`) and Z3 interval stabilization provers.
- **Nuskell (`DNA-and-Natural-Algorithms-Group/nuskell`), KinDA, ERODE
  (`sysma/erode`), KaSa (`KappaTools`), Charlie, LoLA 2, and Stamina:** Formal
  CRN-to-DSD pathway-bisimulation compiler (`Compiles` + `BehaviorCodec`),
  differential equivalence reducer, Kappa static analyzer, and Petri-net
  siphon/trap persistence checkers (`ProductiveOn`).
- **scadnano, PERDIX/TALOS, MagicDNA, oxDNA, BioScript (`UCR-
  Microfluidics/BioScript`, OOPSLA 2018), Fluigi, and PyLabRobot:** Wireframe
  DNA origami compilers and EPA chemical-reactivity type systems rejecting
  hazardous droplet mixes (`Partial.ub`).
- **pyTFA (`EPFL-LCSB/pytfa`), SoPlex Exact-Rational LP, efmtool, CarveMe,
  UPPAAL Pacemaker Verifier, C2E2/DryVR, DrTransformer, and Findpath:**
  Thermodynamic FBA, exact rational Farkas certificates, cotranscriptional RNA
  prefix-chain verifiers (`StepResult.externalCall`), and direct folding pathway
  witness solvers.
- **VeriPB + CakePB (`StephanGocht/VeriPB`), HomotopyContinuation.jl `certify`,
  Perseus/CHomP (Discrete Morse homology), OSCAR.jl, and KBMAG:** HOL4-verified
  symmetry-breaking/dominance certificates, Krawczyk ball-arithmetic root
  uniqueness certificates, and homology-preserving cellular collapse (`Compiles`
  + `EventualBehaviorOf`).
- **SafeCap (`safecap.io`), UMC/KandISTI, MaxPressure Lyapunov Traffic
  Controller, EOFMC (human-automation mode confusion), `autobounds`
  (`bergerlab/autobounds`, JASA 2024), Alpine.jl, and SPIKE (HST/JWST):** SSI
  railway theorem proving, task-analytic cockpit mode-confusion detection, sharp
  polynomial LP causal bounds (`Abstracts`), and telescope keep-out scheduling.

## Boundaries

- **Wet-lab stochastic single-cell gene-expression extrinsic noise and somatic
  mutation evolution (`not examined`):** While `Cello 2.0`, `iBioSim`, and
  `LOICA` model steady-state cytometry distributions and small-network Gillespie
  CTMCs, plasmid copy-number fluctuations during rapid cell division and
  evolutionary loss-of-function mutations over $> 50$ generations are outside
  the scope of static UCF / ODE verification and must be bounded via
  experimental chassis characterization.
- **Full 3D Navier-Stokes continuum turbulence existence vs. discrete stencil
  verification (`known not to apply`):** Mapping `Firedrake`, `FEniCSx`,
  `Dedalus`, `Devito`, and `VCFloat2` onto Anneal's primitives certifies the
  *discrete* variational cochain identities ($d_h \circ d_h = 0$), CFL
  stability, discrete adjoint exactness (`Enzyme`), and IEEE-754 roundoff bounds
  of the compiled numerical solver relative to its discrete specification; it
  does not resolve continuum Navier-Stokes regularity without explicit smoothness
  assumptions tracked in `VerificationResult.waived`.
- **Untestable empirical causal graph structure (`unsupported` by purely
  observational data without interventional or instrumental experiments):** As
  proven by Pearl and Shpitser (`causaleffect`, `Ananke`), no observational
  compiler can verify the absence of latent bidirected confounders beyond
  testable Verma / $d$-separation constraints; Anneal's architecture captures
  this exact boundary by forcing the causal DAG assumptions into
  `VerificationResult.waived` rather than claiming they are proved theorems.
- **Proprietary commercial interlocking and solver binaries (`not examined` at
  closed-source level):** While `Prover iLock`, `Atelier B` (`bbatch`), and
  commercial MIP solvers (Gurobi/CPLEX) have closed-source internal search
  engines, this report examines their published proof/certificate interfaces
  (`HLL` proof logs, B proof obligations, `Ovado`/`ProB` predicates, and `VIPR`
  / `QSopt_ex` rational certificates), which eliminate the closed-source search
  engines from the verification TCB.

## Evidence

All technical claims in this report were synthesized and verified on `2026-10-31`
from the following primary specifications, repositories, and peer-reviewed
publications:

1. **Genetic Design Automation (`Cello`, `GEC`, `Eugene`, `Proto`, `SBOL3`,
   `iBioSim`, `LOICA`):**
   - Nielsen et al., "Genetic circuit design automation," *Science* 352(6281),
     aac7341 (2016), DOI `10.1126/science.aac7341`; source: `CIDAR-LAB/cello`.
   - Jones et al., "Genetic circuit design automation with Cello 2.0," *Nature
     Protocols* 17, 1097–1113 (2022), DOI `10.1038/s41596-021-00675-2`; source:
     `CIDAR-LAB/Cello-v2-core`.
   - Pedersen & Phillips, "Towards programming languages for genetic engineering
     of living cells," *J. R. Soc. Interface* 6, S437–S450 (2009), DOI
     `10.1098/rsif.2009.0035`.
   - Oberortner et al., "Eugene: A Domain-Specific Language for Specifying and
     Constraining Synthetic Biological Parts, Devices, and Systems," *ACS Synth.
     Biol.* 5(6), 489–505 (2016), DOI `10.1021/sb500356d`.
   - Beal, Lu, Weiss, "Automatic compilation from high-level biologically-oriented
     programming language to genetic regulatory networks," *PLoS ONE* 6(8),
     e22490 (2011).
   - Myers et al., `MyersResearchGroup/iBioSim` (`REB2SAC` and LEMA/Petri-net
     engine); Vidal et al., `RudgeLab/LOICA` (*ACS Synth. Biol.* 2022);
     `SynBioHub/synbiohub` and *SBOL Version 3.1.0 Specification*.
2. **Chemical Reaction Networks & DNA Strand Displacement (`Visual DSD`,
   `Peppercorn`, `Piperine`, `CRN++`, `PRISM`, `Storm`, `Catalyst.jl`, `CRNT`,
   `BioNetGen`):**
   - Lakin et al., "Visual DSD: a design and analysis tool for DNA strand
     displacement systems," *Bioinformatics* 27(22), 3211–3213 (2011).
   - Badelt et al., "A general-purpose CRN-to-DSD compiler with formal
     verification, optimization and simulation capabilities," *J. R. Soc.
     Interface* 17(167) (2020); source:
     `DNA-and-Natural-Algorithms-Group/peppercornenumerator` and
     `DNA-and-Natural-Algorithms-Group/piperine`.
   - Vasić, Soloveichik, Khurshid, "CRN++: Molecular Programming Language,"
     *Natural Computing* 19, 391–407 (2020); source: `marko-vasic/crnPlusPlus`.
   - Kwiatkowska, Norman, Parker, `prismmodelchecker/prism`; Hensel et al.,
     `stormchecker/storm`; Loman et al., `SciML/Catalyst.jl` (*PLoS Comput.
     Biol.* 2023); Feinberg, *Foundations of Chemical Reaction Network Theory*,
     Springer (2019), DOI `10.1007/978-3-030-03858-8`; Harris et al.,
     `RuleWorld/bionetgen`.
3. **Tile Assembly & DNA Origami (`Xgrow`, `ISU TAS`, `caDNAno`, `DAEDALUS`):**
   - Winfree et al., `DNA-and-Natural-Algorithms-Group/xgrow`; Soloveichik &
     Winfree, "Complexity of self-assembled shapes," *SIAM J. Comput.* 36(6),
     1544–1569 (2007).
   - Patitz, "Simulation of self-assembly in the abstract tile assembly model
     with ISU TAS," *FNANO 2011*; Douglas et al., `cadnano/cadnano2.5` (*Nucleic
     Acids Res.* 2009); Veneziano et al., "Designer nanoscale DNA assemblies
     programmed from the top down," *Science* 352(6293), aaf4388 (2016), DOI
     `10.1126/science.aaf4388`.
4. **Digital Microfluidics (`Puddle`, `BioCoder`, `MFSimStatic`, `AquaCore`,
   `OpenDrop`):**
   - Willsey et al., "Puddle: A Dynamic, Error-Correcting, Full-Stack
     Microfluidics Platform," *ASPLOS 2019*; source: `uwmisl/puddle`.
   - Grissom et al., "An open-source compiler and PCB synthesis tool for digital
     microfluidic biochips," *INTEGRATION, the VLSI Journal* 51, 169–193 (2015);
     source: `UCRMicrofluidics/MFSimStatic`.
   - Amin et al., "AquaCore: A programmable architecture for microfluidics,"
     *ISCA 2007*, DOI `10.1145/1250662.1250696`; Ananthanarayanan & Thies,
     `BioCoder` (*Bioinformatics* 2010); Gaudenz, `GaudiLabs/OpenDrop`.
5. **Flux Balance Analysis (`COBRApy`, `MEMOTE`, `StrainDesign`, `eQuilibrator`,
   `QSopt_ex`):**
   - Ebrahim et al., `opencobra/cobrapy` (*BMC Syst. Biol.* 2013); Lieven et
     al., `opencobra/memote` (*Nat. Biotechnol.* 2020); Schneider, von Kamp,
     Klamt, `klamt-lab/straindesign` (*PLoS Comput. Biol.* 2022); Beber et al.,
     `elad.noor/equilibrator-api` (*Nucleic Acids Res.* 2022); Applegate et al.,
     `jonls/qsopt-ex` (*INFORMS J. Comput.* 2007).
6. **Physiological Control (`UVA/Padova` `simglucose`, `OpenAPS`, `Loop`,
   `Flow*`):**
   - Dalla Man et al., "The UVA/PADOVA Type 1 Diabetes Simulator: New Features,"
     *J. Diabetes Sci. Technol.* 8(1), 26–34 (2014); Xie, `jxx123/simglucose`.
   - OpenAPS Reference Design, `openaps/oref0` (`lib/determine-basal/determine-basal.js`
     implementing `IOBpredBG`, `COBpredBG`, `UAMpredBG`, `ZTpredBG`);
     `LoopKit/Loop`; Chen, Ábrahám, Sankaranarayanan, "Flow*: An Analyzer for
     Non-linear Hybrid Systems," *CAV 2013*, DOI `10.1007/978-3-642-39799-8_18`.
7. **RNA Folding (`NUPACK 4`, `ViennaRNA`/`Barriers`/`Treekin`, `LinearFold`,
   `LinearDesign`, `Multistrand`):**
   - Fornace, Huang, Newman, Pierce, "NUPACK: Analysis and Design of Nucleic Acid
     Systems," *ACS Synth. Biol.* (2023), DOI `10.1021/acssynbio.3c00125`;
     Lorenz et al., `ViennaRNA/ViennaRNA`; Huang et al., `LinearFold/LinearFold`;
     Zhang et al., "Algorithm for Optimized mRNA Design Improves Stability and
     Immunogenicity," *Nature* 621, 396–403 (2023), source:
     `LinearDesignSoftware/LinearDesign`; Schaeffer et al.,
     `DNA-and-Natural-Algorithms-Group/multistrand`.
8. **Ecology & Compositional Petri Nets (`EwE`, `SLiM 4`, `MGDrivE`,
   `AlgebraicPetri.jl`):**
   - Christensen & Walters, "Ecopath with Ecosim: methods, capabilities and
     limitations," *Ecol. Model.* 172, 109–139 (2004), DOI
     `10.1016/S0304-3800(03)00364-3`; Haller & Messer, `MesserLab/SLiM` (*Mol.
     Biol. Evol.* 2023); Sánchez C. et al., `MarshallLab/MGDrivE`; Baez &
     Pollard, "A Compositional Framework for Reaction Networks," *Rev. Math.
     Phys.* 29(09) (2017), source: `AlgebraicJulia/AlgebraicPetri.jl`.
9. **PDE Compilers, Floating-Point & AD (`Firedrake`, `FEniCSx`, `Dedalus`,
   `Devito`, `VCFloat2`, `Enzyme`):**
   - Rathgeber et al., `firedrakeproject/firedrake` (*ACM TOMS* 2016); Baratta
     et al., `FEniCS/dolfinx`; Burns et al., `DedalusProject/dedalus` (*Phys.
     Rev. Research* 2020); Louboutin et al., `devitocodes/devito` (*Geosci.
     Model Dev.* 2019); Appel & Kellison, `VeriNum/vcfloat` ("VCFloat2:
     Floating-Point Error Analysis in Coq," *CPP 2024*); Moses et al.,
     `EnzymeAD/Enzyme` (*NeurIPS 2020* / *SC 2021*).
10. **Mathematical Certificates & Topology (`Flyspeck`, `Lean Blueprint`,
    `AlphaProof`, `AlphaGeometry 2`, `SnapPy`, `Regina`, `Kenzo`, `CakeLPR`):**
    - Hales et al., `flyspeck/flyspeck` (*Forum Math. Pi* 2017); Massot,
      `PatrickMassot/leanblueprint`; Trinh et al., `google-deepmind/alphageometry`
      (*Nature* 2024); Culler et al., `3-manifolds/SnapPy` (HIKMOT
      `verify_hyperbolicity`); Burton et al., `regina-normal/regina`; Dousson,
      Rubio, Sergeraert, `jromanf/kenzo`; Tan, Heule, Myreen,
      `tanyongkiam/cake_lpr` (*TACAS 2021*).
11. **Rail Interlocking, Logistics & Traffic (`Atelier B`, `Ovado`, `ProB`,
    `Prover iLock`, `EURIS`, `RobustRailS`, `OR-Tools`, `VIPR`, `NEMA TS2`,
    `TuLiP`, `SUMO`):**
    - Leuschel & Butler, `hhu-stups/prob2_kernel`; Borälv & Stålmarck, "Prover
      Technology in Railways," DOI `10.1007/3-540-40922-X_8`; Haxthausen,
      `RobustRailS`; Perron & Furnon, `google/or-tools`; Cheung, Gleixner,
      Steffy, `ambros-gleixner/VIPR` (*IPCO 2017*); Wongpiromsarn et al.,
      `tulip-control/tulip-control`; Lopez et al., `eclipse-sumo/sumo`.
12. **HCI, Pragmatics, Causality, Privacy, Grid & Space (`PVSio-web`, `IVY`,
    `SCR`/`RSML-e`, `WebPPL-RSA`, `BSPL`, `Ananke`, `causaleffect`, `DoWhy`,
    `Dagitty`, `OpenDP`, `Tumult Core`, `PowerModels.jl`, `MATPOWER`, `PACT`,
    `EnergyTag`, `ASPEN`, `CLASP`, `Aerie`, `EUROPA`, `PLEXIL`, `SPICE`):**
    - Masci et al., `pvsioweb/pvsio-web` (*CAV 2015*); Goodman & Stuhlmüller,
      `probmods/webppl`; Singh, `munindar/bspl`; Tikka & Karvanen,
      `santikka/causaleffect` (*J. Stat. Softw.* 2017); Bhattacharya et al.,
      `causal/ananke`; Sharma & Kiciman, `py-why/dowhy`; Gaboardi et al.,
      `opendp/opendp`; Berghel et al., `tmlt.core`; Coffrin et al.,
      `lanl-ansi/PowerModels.jl`; Zimmerman et al., `MATPOWER/matpower`; WBCSD
      *Pathfinder Framework v2.1*; *EnergyTag Granular Certificate Standard v2*;
      `NASA-AMMOS/aerie`; `nasa/europa`; `nasa/plexil`; Acton et al., NASA JPL
      NAIF `CSPICE`.

## Revalidation

To revalidate the findings in this report against future versions of Anneal's
`trusted/lean/` kernel or updated upstream tool releases:

1. **Anneal Kernel Interface Check:** Verify that the four core `trusted/lean/`
   modules continue to expose:
   - `Language SemObs` with `Partial` (`defined : Prop` and `val : defined → Out → Prop`)
     and `obs : Out → SemObs`;
   - `BehaviorCodec L₁ L₂` with partial-bijection laws (`decodeQuery_encodeQuery`,
     `decodeOut_encodeOut`, `encodeOut_of_decodeOut`, `obs_decodeOut`),
     `Compiles`, and `Abstracts`;
   - `ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
     `StepResult.externalCall boundaryInv branches`;
   - `VerificationResult policy waived obligations` and `TrustPolicy`.
2. **Tool-Specific Certificate Format Probes:**
   - For `VIPR` (`ambros-gleixner/VIPR`) and `QSopt_ex` (`jonls/qsopt-ex`), check
     whether the `.vipr` rational cutting-plane grammar or Farkas dual output
     format has changed; both reduce directly to rational linear combination
     checks in Lean's `Rat`.
   - For `CakeLPR` (`tanyongkiam/cake_lpr`), check whether the LPR/LRAT binary
     clause steps remain compatible with propagation-redundancy witness checking.
   - For `OpenDP` (`opendp/opendp`) and `Tumult Core` (`tmlt.core`), inspect the
     `Transformation` (`StabilityMap`) and `Measurement` (`PrivacyMap`) traits
     in `rust/src/core/mod.rs` to confirm that metric stability composition
     still mediates all privacy guarantees.
   - For `Aerie` (`NASA-AMMOS/aerie`) and `PLEXIL` (`nasa/plexil`), verify that
     activity/node state-transition guards (`StartCondition`, `InvariantCondition`,
     `ExitCondition`) and resource profile envelopes retain synchronous
     deterministic semantics.
