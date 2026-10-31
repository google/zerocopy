<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Historical Verification Failures Across Synthetic Biology, Chemical Reaction Networks, Mathematical Formalization, PDE Compilers, Railway Interlocking, and Aerospace Control

## Summary

Across synthetic biology compilers, molecular reaction cascades, constraint-based
metabolic reconstructions, computer-assisted mathematical proofs, numerical
partial differential equation (PDE) and automatic differentiation (AD)
compilers, railway interlocking systems, and aerospace human-machine and
autonomy architectures, catastrophic post-deployment and post-publication
failures recur along four formal fault lines that map directly onto the four
core verification primitives in Anneal's Trusted Computing Base (`trusted/lean/`):

1. **Silent domain extension and unmodeled undefined behavior (`Language SemObs`
   and `Partial`):** When a specification or compiler models an intrinsically
   partial physical, numerical, or mathematical operation as a total function—or
   omits an environmental/structural breakdown mode from `defined = False`
   (`Partial.ub`)—ill-formed states propagate silently as valid outcomes. In
   `Lean 4` / `Mathlib` autoformalization benchmarks (`MiniF2F`, `PutnamBench`),
   totalizing division (`0 / 0 = 0`) and natural-number subtraction (`a - b = 0`
   for `a < b`) without side-condition guards produces formally proven theorems
   whose mathematical meaning is falsified at boundary inputs. In genome-scale
   Flux Balance Analysis (`FBA`), omitting chemical-potential (`ll-FBA`) and
   elemental-balance guards from `defined` admits thermodynamically impossible
   Type-III internal loops that synthesize ATP from nothing, while IEEE-754
   simplex tolerances ($\epsilon \approx 10^{-7}$ in `Gurobi`/`GLPK`, exposed by
   `MEMOTE` and exact rational solver `QSopt_ex`) allow positive biomass flux in
   stoichiometrically blocked networks. In `Enzyme` reverse-mode automatic
   differentiation and shock-capturing PDE stencils, evaluating derivatives
   across discontinuous branches (`if (x == 0.0)`, Heaviside phase changes, or
   unclipped WENO negative-pressure states) yields silent $O(1)$ gradient errors
   or `NaN` propagation instead of failing closed via `Partial.ub`.
2. **Spurious target behaviors, non-injective observation spines, and unit
   mismatches (`BehaviorCodec`, `Compiles`, and `Abstracts`):** When a target
   implementation admits physical or algebraic pathways outside the image of the
   source specification (`L_tgt.sem t ≰ codec.toMorphism (L_src.sem s)`), or
   when the codec violates partial-bijection and spine-preservation laws
   (`encodeOut_of_decodeOut`, `decodeOut_encodeOut`, `obs_decodeOut`),
   compilation soundness collapses. In DNA strand-displacement (`DSD`) cascades
   (`Qian & Winfree` 2011 seesaw gates; `Visual DSD`), blunt-end coaxial
   stacking and helix fraying create zero-toehold leak pathways that release
   output strands with zero input (`Compiles` soundness failure), requiring the
   multi-domain clamps of `Thachuk, Winfree & Soloveichik` (2015) to restore a
   sound `BehaviorCodec`. In cockpit human-computer interaction, the **Air Inter
   Flight 148** Airbus A320 crash (20 January 1992, 87 fatalities) resulted from
   a non-injective display projection (`SemObs`) on the Flight Control Unit
   (FCU) that rendered `-3.3°` Flight Path Angle (`TRK-FPA`) and `-3,300 ft/min`
   Vertical Speed (`HDG-V/S`) as the near-identical two-digit token `-3.3` vs.
   `-33`, violating `encodeOut_of_decodeOut` mode transparency. In deep-space
   navigation, the loss of the **Mars Climate Orbiter** (23 September 1999)
   stemmed from an unverified `BehaviorCodec` across the `SM_FORCES` angular
   momentum impulse file interface (`lbf·s` emitted by Lockheed Martin ground
   software vs. `N·s` decoded by JPL navigation software, a $4.448222\times$
   scale violation of `obs_decodeOut`).
3. **Empty-domain vacuity, stochastic siphons, and resource-exhaustion livelocks
   (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`):** Partial-correctness safety (`b ≤ spec`) holds
   vacuously whenever a system produces no terminal outcomes (`val h = ∅`),
   starts from an uninhabited precondition (`pre = ∅`), or omits invariant
   framing across open-world environmental coupling (`StepResult.externalCall`).
   In the landmark **`Cello` 1.0** genetic circuit compiler (`Nielsen et al.`,
   *Science* 2016), 15 of 60 (25%) compiled *Escherichia coli* logic circuits
   failed in vivo despite passing static truth-table simulation because Cello's
   independent Hill-function gate model omitted `StepResult.externalCall`
   host-resource coupling (ribosome/RNAP depletion and cellular growth burden),
   tandem promoter roadblocking, and downstream retroactivity. In discrete
   Chemical Reaction Networks (`CRNs`), bimolecular networks whose deterministic
   mass-action ODEs converge to a strictly positive attractor can suffer
   probability-1 finite-molecule extinction into a boundary **critical siphon**
   (`Angeli, De Leenheer & Sontag` 2007), violating `ProductiveOn`. On **Mars
   Exploration Rover Spirit (Sol 18, 21 January 2004)**, unbounded accumulation
   of unlinked `dosFs` directory entries in flash memory exhausted VxWorks
   system RAM during boot initialization, trapping the rover in an infinite
   watchdog reboot livelock (over 120 resets) that preserved memory-safety
   invariants (`defined = True`) while reducing mission productivity to zero
   (`ProductiveOn` failure). In the **18 March 2019 Hong Kong MTR Tsuen Wan Line
   collision** at Central Station, a warm-standby switchover between primary and
   tertiary Thales `SelTrac` Zone Controllers (`StepResult.externalCall`
   failover boundary) failed to repopulate the crossover conflict-locking table,
   violating `boundaryInv` and authorizing two trains (`T131` and `T112`) onto
   the same crossover simultaneously.
4. **Unverified oracle code and global antecedent explosion
   (`VerificationResult` and `TrustPolicy`):** Relying on unverified imperative
   search scripts or placing concrete assumptions on the left-hand side of a
   global implication (`AllHold assumptions → Verified`) allows a single buggy
   helper or false lemma to corrupt an entire theorem corpus. In pure
   mathematics, **Kempe's 1879 proof of the Four-Color Theorem** stood for 11
   years before Heawood (1890) exposed a non-commuting dual Kempe-chain color
   swap in the degree-5 inductive step; **Kapranov and Voevodsky's 1991 strict
   $\infty$-groupoid equivalence** stood for 7 years until **Carlos Simpson's
   1998 counterexample** (`arXiv:math/9810059`) proved via Whitehead products on
   $S^2$ that strict 3-groupoids cannot realize all homotopy 3-types; and
   **Hales's 1998 Kepler Conjecture proof** required 16 years of `Flyspeck`
   formalization (`Hales et al.` 2017) in `HOL Light` and `Isabelle/HOL` to
   replace ~100,000 lines of unverified C++ interval arithmetic and repair bugs
   in the tame-graph enumeration oracle.

## Applicability

The findings in this report apply to the nine subjects recorded in
`REPORT.json`:

1. **Anneal core verification framework** at
   `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` and **Anneal
   MIR-to-x86-64 compiler branch** at
   `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`, together with the
   hardened primitives established in the companion `reference` corpus reports
   (`anneal-behavior-codec-and-progress-refinement-2026`,
   `anneal-partial-compile-and-conditioning-refinement-2026`,
   `anneal-structural-external-calls-and-tcb-mutation-testing-2026`, and
   `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`):
   - `Language SemObs` and `Partial` (`defined : Prop`, `val : defined → B`,
     `Partial.ub`),
   - `BehaviorCodec L₁ L₂` (`encodeQuery`, `decodeQuery`, `encodeOut`,
     `decodeOut : L₂.Out → Option L₁.Out`, `obs_decodeOut`,
     `decodeOut_encodeOut`, `encodeOut_of_decodeOut`), `Compiles`, and
     `Abstracts`,
   - `ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
     `StepResult.externalCall boundaryInv next`, and
   - `VerificationResult policy waived obligations` (`ScopedVerificationResult`
     and `TrustPolicy`).
2. **Biocomputing, CRN, metabolic, and microfluidic synthesis tools:**
   - `Cello 1.0` (`CIDARLAB/cello`, `Nielsen et al.`, *Science*
     352(6281):aac7341, 2016) and `Cello 2.0` (`Jones et al.`, *Nature
     Microbiology* 2022),
   - `Qian & Winfree` (*Science* 332:1196–1201, 2011) seesaw DSD cascades,
     `Visual DSD` (`Lakin et al.` 2011), `Thachuk, Winfree & Soloveichik` (*DNA
     21*, LNCS 9211:133–153, 2015) leakless DSD motifs, and Petri-net siphon
     persistence (`Angeli, De Leenheer & Sontag`, *Math. Biosci.* 207:107–129,
     2007),
   - `MEMOTE` (`opencobra/memote`, `Lieven et al.`, *Nature Biotechnology*
     38:272–276, 2020), loopless FBA (`Schellenberger, Lewis & Palsson`,
     *Biophys. J.* 100:544–553, 2011), exact rational simplex `QSopt_ex`
     (`Applegate et al.` 2007), and `MFSim` digital microfluidics synthesis
     (`Grissom & Brisk`, *ACM JETC* 2015).
3. **Mathematical formalization and computer-assisted proof systems:**
   - `Hales` (1998/2005) Kepler Conjecture proof and `Flyspeck` (`Hales et al.`,
     *Forum of Mathematics, Pi* 5:e2, 2017),
   - `Kempe` (*Amer. J. Math.* 2:193–200, 1879) and `Heawood` (*Quart. J. Pure
     Appl. Math.* 24:332–338, 1890),
   - `Kapranov & Voevodsky` (*Cah. Topol. Géom. Différ. Catég.* 32:29–46, 1991),
     `Simpson` (`arXiv:math/9810059`, 1998), and `Voevodsky` (*Bull. Amer. Math.
     Soc.* 55:405–434, 2018), and
   - `MiniF2F` (`Zheng et al.` 2021) and `PutnamBench` (`Tsoukalas et al.` 2024)
     over `Lean 4` and `Mathlib4`.
4. **Scientific computing, railway signaling, and aerospace control systems:**
   - `Enzyme` LLVM automatic differentiation (`Moses & Churavy`, *NeurIPS* 2020;
     `Hückelheim et al.`, `arXiv:2305.07542`, 2023),
   - Hong Kong EMSD investigation of the 18 March 2019 MTR Tsuen Wan Line
     Central Station collision (July 2019), Singapore LTA investigation of the
     15 November 2017 Joo Koon collision (December 2017), and `ProB`/`Atelier B`
     ERTMS/ETCS and `METEOR` verification (`Leuschel et al.`, *STTT* 2020),
   - French BEA investigation of Air Inter Flight 148 (`F-GGED`, 20 January
     1992), JPL postmortem of the Mars Spirit Rover Sol 18 flash anomaly
     (January 2004), and NASA Mishap Investigation Board report on the Mars
     Climate Orbiter (November 1999).

All structural failure models and their refutation by Anneal's four `trusted/`
primitives are mechanized with zero kernel axioms in
[support/CrossDomainFailureTaxonomy.lean](support/CrossDomainFailureTaxonomy.lean).

## Findings

### 1. Synthetic Biology, CRN, Tile Assembly, and Microfluidics Failures

#### 1.1 Cello 1.0 In Vivo Circuit Failures: Unmodeled Host-Resource Coupling, Roadblocking, and Retroactivity (Nielsen et al. 2016)

`Basis: documentation + source + execution (support/CrossDomainFailureTaxonomy.lean)`

**Historical incident and quantitative metrics.** In April 2016, Alec A. K.
Nielsen, Bryan S. Der, Jonghyeon Shin, Prashant Vaidyanathan, Vanya Paralanov,
Elizabeth A. Strychalski, David Ross, Douglas Densmore, and Christopher A. Voigt
published *Genetic circuit design automation* (*Science* 352(6281):aac7341,
2016), introducing **Cello**, an electronic design automation (EDA) compiler that
synthesizes behavioral Verilog specifications into DNA plasmid sequences of NOR
and NOT transcriptional repressor gates (using TetR-family repressors in
*Escherichia coli*). Each gate $i$ was characterized in isolation in a User
Constraints File (UCF) by its steady-state Hill response curve in Relative
Promoter Units (RPU):

$$y_i = y_{i,\min} + (y_{i,\max} - y_{i,\min}) \frac{\kappa_i^{n_i}}{\kappa_i^{n_i} + x_i^{n_i}}$$

where $x_i = \sum_j x_{ij}$ is the summed upstream promoter activity driving
repressor $i$. Cello compiled 60 distinct multi-input logic circuits (comprising
up to 7 NOR/NOT gates and 888,000 base pairs of assembled DNA across 412 circuit
states). When tested in vivo by flow cytometry:

- **45 of the 60 circuits (75%)** functioned correctly across all input logic
  combinations on the first build (with 92% of the 412 individual input-output
  states matching predicted ON/OFF thresholds).
- **15 of the 60 circuits (25%) failed in vivo** (exhibiting inverted logic,
  collapsed dynamic range inside the indeterminate noise gap
  $(\theta_{\text{OFF}}, \theta_{\text{ON}})$, or bimodal cell populations),
  despite Cello's static Hill-function simulator predicting clear Boolean signal
  separation for all 60 designs.

**Technical root-cause analysis.** Postmortem experimental dissection by Nielsen
et al. (2016) and subsequent Cello 2.0 follow-ups (`Chen et al.`, *Nat. Chem.
Biol.* 2020; `Jones et al.`, *Nat. Microbiol.* 2022) traced the 15 circuit
failures to three physical effects absent from Cello 1.0's compositional
semantics:

1. **Unmodeled cellular growth burden and ribosome/RNAP pool saturation (host
   resource coupling):** Repressors such as `SrpR`, `PhlF`, and `BM3R1` impose
   heavy metabolic and translational load when expressed at high RPU. In
   isolated 1-gate UCF characterization, the host *E. coli* maintains sufficient
   free RNA polymerase ($\text{RNAP}_{\text{free}}$) and free ribosomes
   ($\text{Rib}_{\text{free}}$). When 5 to 7 gates are simultaneously active in
   a compiled cascade, total heterologous resource demand $\sum_i r_i x_i^*$
   exceeds the cellular carrying capacity $R_{\max}$. Growth rate $\mu$ drops by
   $>50\%$, plasmid copy number fluctuates, and effective promoter maximum output
   $y_{i,\max}$ scales down non-monotonically by $\frac{1}{1 + \sum_k J_k x_k}$
   (`Qian, Del Vecchio et al.`, *ACS Synth. Biol.* 2017), collapsing ON states
   below $\theta_{\text{ON}}$.
2. **Tandem promoter roadblocking and transcriptional interference:** To realize
   a 2-input `NOR` gate ($y_i = \neg(u_1 \lor u_2)$), Cello places two input
   promoters $P_1, P_2$ in tandem upstream of a single ribozyme insulator and
   repressor CDS. When an upstream promoter $P_1$ recruits RNAP or binds its
   cognate repressor near the downstream promoter $P_2$, steric occlusion and
   elongating RNAP collisions ("roadblocking") reduce the combined transcription
   rate below the additive model $x_i = x_{i,1} + x_{i,2}$ assumed by the
   compiler (`x_actual = x_1 + α_roadblock · x_2` with $\alpha < 1$). Consequently,
   an input state `(0, 1)` fails to produce enough repressor to turn the
   downstream promoter OFF.
3. **Retroactivity (downstream promoter titration impedance):** When a repressor
   protein $X_i$ fans out to multiple downstream operator sites (or high-copy
   plasmid targets), DNA binding sequesters free repressor monomers, altering
   both the effective dissociation constant $\kappa_i$ and the relaxation time
   constant toward steady state.

**Architectural lessons for Anneal's 4 `trusted/` primitives:**

- **`Language SemObs` & `Partial` (`defined` vs. `Partial.ub`):** Cello 1.0
  modeled Hill gate composition as a total function over $\mathbb{R}_{\ge 0}$
  with no resource-capacity guard. In Anneal, each gate evaluation must carry
  cumulative cellular resource load $R_{\text{load}} = \sum_i r_i(x_i^*)$ in
  `Out` and define `defined := R_load ≤ R_max ∧ ∀ k ∈ outputs, x_k^* ≤ θ_OFF ∨
  x_k^* ≥ θ_ON`. Any gate assignment whose summed repressor load exceeds
  $R_{\max}$ (toxicity collapse) or settles inside $(\theta_{\text{OFF}},
  \theta_{\text{ON}})$ triggers `Partial.ub` (`defined = False`), preventing the
  compiler from certifying a toxic circuit.
- **`BehaviorCodec` & `Compiles`:** Cello's additive wire junction rule
  ($x_i = x_{i,1} + x_{i,2}$) was an unsound `Compiles` lowering from abstract
  Boolean `OR` wiring to physical tandem DNA promoters. A sound `Compiles`
  theorem requires either empirically parameterized non-linear tandem interaction
  tensors $f_{\text{tandem}}(x_1, x_2) \in [\underline{f}, \overline{f}]$ via an
  interval `Abstracts` envelope, or physical circuit re-synthesis that avoids
  uninsulated tandem promoters.
- **`StepResult.externalCall boundaryInv branches`:** A genetic circuit does not
  execute in a closed register file; every transcriptional epoch interacts with
  the shared host chassis (`RNAP`, ribosomes, growth-rate dilution $\mu$).
  Modeling host-chassis coupling via `StepResult.externalCall boundaryInv
  branches` requires `boundaryInv` to prove that total circuit resource
  consumption stays strictly inside the host homeostatic invariant basin before
  branching over growth-rate and copy-number perturbations.
- **`VerificationResult` & `TrustPolicy`:** Empirical cytometry curves fitted
  under single-gate conditions carry implicit environmental assumptions
  (`ConstantPlasmidCopyNumber`, `ZeroTandemRoadblocking`, `BoundedRibosomeLoad`).
  Recording these in `VerificationResult policy waived obligations` forces the
  compiler to expose every unproved biological insulation assumption in the
  certificate's `waived` list rather than silently baking them into `Compiles`.

---

#### 1.2 DNA Strand-Displacement Spurious Leak Pathways, Finite-Molecule Siphons, and Tile Self-Assembly Kinetic Traps

`Basis: documentation + source + execution (support/CrossDomainFailureTaxonomy.lean)`

**Historical incidents and quantitative metrics.**

1. **Zero-input spurious leaks in `Qian & Winfree` (2011) seesaw DSD cascades and
   `Visual DSD`:** In *Scaling up digital circuit computation with DNA strand
   displacement cascades* (*Science* 332(6034):1196–1201, 2011), Lulu Qian and
   Erik Winfree demonstrated a 4-bit square-root circuit composed of 130 DNA
   strands using reversible **seesaw gates** (toehold exchange). While formal
   pathway compilers such as Microsoft Research's **`Visual DSD`** (`Lakin,
   Youssef, Polo, Phillips & Bundgaard`, *Bioinformatics* 2011) verify circuits
   under the "infinite-toehold-separation" semantics (where strand displacement
   occurs *only* after a complementary single-stranded toehold domain binds),
   physical wet-lab execution exposed **toeless (zero-toehold) leak reactions**:
   - **Blunt-end coaxial base stacking and breathing/fraying leaks:** At the
     helix ends or nick sites of a resting double-stranded gate complex $G\!:\!O$
     (where output strand $O$ is hybridized to gate backbone $G$), thermal
     breathing transiently frays 1–2 terminal base pairs, allowing an invading
     fuel strand $F$ to displace $O$ with **zero input strand $I$ present** at a
     bimolecular leak rate $k_{\text{leak}} \approx 1\text{–}10\text{ M}^{-1}\text{s}^{-1}$
     (compared to toehold-mediated rate $k_{\text{toehold}} \approx 10^6\text{ M}^{-1}\text{s}^{-1}$).
   - In multi-layer cascades with high fuel concentrations ($[F] \approx 100\text{ nM}$)
     and catalytic seesaw amplification, even a $10^{-5}$ relative leak rate
     triggers autocatalytic runaway within hours, flipping logic `0` outputs to
     `1` prior to input arrival (`Thachuk, Winfree & Soloveichik`, *Leakless DNA
     Strand Displacement Systems*, *DNA 21*, LNCS 9211:133–153, 2015).
2. **Stochastic CRN boundary siphons (`Angeli, De Leenheer & Sontag` 2007;
   `Soloveichik, Cook, Winfree & Bruck` 2008):** In synthetic CRN compilers that
   translate polynomial ODEs or consensus protocols into finite-volume stochastic
   CRNs (continuous-time Markov chains on $\mathbb{N}^{\mathcal{S}}$ under the
   Gillespie algorithm), networks such as the autocatalytic infection/oscillator
   motif:
   $$A + B \xrightarrow{k_1} 2B, \qquad B \xrightarrow{k_2} A$$
   have a globally asymptotically stable interior equilibrium $b^* = M - k_2/k_1 > 0$
   in deterministic mass-action ODEs ($\dot{b} = k_1 a b - k_2 b$), yet in any
   finite molecular population $N_A + N_B = M$, the boundary state
   $(N_A = M, N_B = 0)$ is an **absorbing critical siphon** ($Z = \{B\}$) reached
   with **probability 1** in finite time! Once $N_B = 0$, the bimolecular
   reaction $A + B \to 2B$ is permanently disabled (`rate = 0`), extinguishing
   the computation.
3. **kTAM facet nucleation and geometric kinetic traps (`Rothemund, Papadakis &
   Winfree`, *PLoS Biology* 2(12):e424, 2004):** When self-assembling algorithmic
   DNA DX tiles implementing XOR cellular-automaton Sierpinski triangles at
   temperature $\tau = 2$, single-bond ($\tau = 1$) attachments along growth
   facets persisted long enough for an adjacent second tile to lock in the
   mismatched tile, producing a **1% to 10% per-tile error rate** (limiting
   defect-free crystals to $<100$ tiles) until `Winfree & Bekbolatov` (*DNA 9*,
   LNCS 2943:126–144, 2004) introduced $k \times k$ supertile proofreading blocks.

**Architectural lessons for Anneal's 4 `trusted/` primitives:**

- **`Compiles` & `Abstracts` (Spurious Target Transitions Break `Compiles`):**
  Under `Visual DSD`'s idealized semantics $L_{\text{ideal}}$, a gate with input
  $I = 0$ produces output $\{O = 0\}$. In the physical DNA semantics
  $L_{\text{phys}}$ with coaxial nick fraying, the same gate with $I = 0$ can
  produce $\{O = 0, O = 1\}$. Because $\{0, 1\} \not\subseteq \{0\}$,
  `Compiles L_ideal L_phys codec s t` **fails directly**: target behavior is
  strictly wider than source behavior! Restoring `Compiles` requires compiling to
  a $L$-domain leakless motif (`Thachuk et al.` 2015) where any spurious
  outcome requires $L \ge 2$ simultaneous unfavourable toeless invasion events,
  whose thermodynamic barrier is certified via an `Abstracts` energy envelope.
- **`BehaviorCodec` (`decodeOut = none` for Unclean/Partially Migrated States):**
  In both $k \times k$ supertile proofreading (`Winfree & Bekbolatov` 2004) and
  multi-step DSD cascades (`Shin, Thachuk & Winfree`), a single macro-step is
  realized by several reversible micro-steps. Defining `decodeOut` to return
  `none` whenever a $k \times k$ supertile block is incomplete or an intermediate
  DSD complex is non-zero prevents mid-pathway transient states from spoofing
  valid logical outputs, while `Partial.ub` flags any locked-in glue mismatch or
  fuel starvation.
- **`ProductiveOn` & `InhabitedPre` (Refuting Critical Siphons):** Deterministic
  ODE stability is an unsound proxy for discrete CRN liveness whenever the
  stoichiometric network contains an unbuffered minimal siphon $Z \subseteq
  \mathcal{S}$ ($\forall r \in \mathcal{R},\; \text{out}(r) \cap Z \neq \emptyset
  \implies \text{in}(r) \cap Z \neq \emptyset$). In Anneal, `ProductiveOn pre
  crn` over the discrete state space $\mathbb{N}^{\mathcal{S}}$ requires proving
  that from every reachable state in the execution prefix, a valid terminal
  output remains reachable—which is refuted immediately if any trajectory can
  empty a critical siphon $Z$ before reaching a terminal state.

---

#### 1.3 Genome-Scale Metabolic Models (FBA Type-III Loops and Floating-Point LP Leaks), Digital Microfluidics (MFSim / EWOD), and Physiological Control

`Basis: documentation + source + execution (support/CrossDomainFailureTaxonomy.lean)`

**Historical incidents and quantitative metrics.**

1. **Thermodynamically impossible Type-III internal loops and floating-point LP
   feasibility leaks in Genome-Scale Metabolic Models (`Schellenberger et al.`
   2011; `MEMOTE`, `Lieven et al.` 2020):** Standard Flux Balance Analysis (FBA)
   maximizes biomass objective $c^T v$ subject only to mass-balance $S v = 0$ and
   box bounds $\underline{v} \le v \le \overline{v}$. When Christian Lieven,
   Moritz E. Beber, Bernhard O. Palsson, and 45 co-authors audited the published
   corpus of genome-scale metabolic models (GEMs) in BiGG, BioModels, and KBase
   using the **`MEMOTE`** test suite (*Nature Biotechnology* 38:272–276, 2020),
   they discovered widespread structural and numerical defects across peer-reviewed
   models:
   - **Type-III stoichiometrically balanced futile cycles (`Schellenberger, Lewis
     & Palsson`, *Biophys. J.* 100(3):544–553, 2011):** Internal reaction loops
     $c \in \ker(S_{\text{int}})$ ($c \neq 0$) that violate Kirchoff's second law
     of thermodynamics ($\nexists \mu \in \mathbb{R}^{|\mathcal{M}|}$ such that
     $c_j \cdot (S_{\cdot, j}^T \mu) < 0$ for all $j \in \text{supp}(c)$)
     circulate unbounded flux ($v_{\text{loop}} = 1000\text{ mmol/gDW/h}$) and,
     when coupled to poorly curated proton-translocating or cofactor-converting
     reactions, **synthesize ATP, NADH, or biomass out of zero carbon/energy
     input** (`test_find_stoichiometrically_balanced_cycles`).
   - **Floating-point LP feasibility leaks (`QSopt_ex` vs. `Gurobi`/`GLPK`):**
     Large GEMs coupled to macromolecular expression (`ME-models`, `O'Brien et
     al.`, *Mol. Syst. Biol.* 2013) span 5 to 6 orders of magnitude in
     stoichiometric coefficients (from $10^{-6}$ prosthetic group dilutions to
     $10^2$ ATP maintenance). Standard double-precision simplex solvers use a
     primal feasibility tolerance $\epsilon_{\text{feas}} = 10^{-6}$ to
     $10^{-9}$, permitting residual mass violations $\|S v\|_\infty \le 10^{-7}$.
     Multiplying a $10^{-7}$ mass leak on an enzyme cofactor across a high-turnover
     catalytic cycle allows a floating-point LP solver to report positive growth
     ($v_{\text{biomass}} > 0$) on a lethal gene-knockout strain whose exact
     rational feasible space (verified via `QSopt_ex`, `Applegate et al.` 2007,
     or `SoPlex` rational reconstruction) is strictly $\{v \mid v_{\text{biomass}}
     = 0\}$!
2. **Digital Microfluidics (`MFSim`) dynamic droplet spacing (IR) violations and
   surface residue cross-contamination (`Grissom & Brisk` 2015; `Su, Hwang &
   Chakrabarty`, *IEEE TCAD* 2006):** Early grid-routing compilers for
   Electrowetting-on-Dielectric (EWOD) biochips enforced only the **static
   fluid-spacing rule** ($\|p(d_1, t) - p(d_2, t)\|_\infty \ge 2$ at integer
   clock ticks $t$ and $t+1$) while omitting the **dynamic inter-step spacing
   rule** ($\|p(d_1, t+1) - p(d_2, t)\|_\infty \ge 2$). When droplet $d_1$ steps
   into $(x, y)$ at tick $t+1$ while droplet $d_2$ simultaneously vacates the
   adjacent cell $(x+1, y)$ to $(x+2, y)$, hydrodynamic meniscus trailing during
   the sub-cycle actuation transition causes **accidental droplet coalescence**,
   ruining the assay (`Grissom, Curtis, Windh, Phung, Kumar, Zimmerman, O'Neal,
   McDaniel & Brisk`, *ACM JETC* 12(2):16, 2015). Similarly, routers that track
   electrode occupancy without a persistent surface-residue ghost map route a
   clean sample droplet across an electrode previously visited by a protein
   reagent without an intervening wash droplet, causing cross-contamination.
3. **Closed-loop Artificial Pancreas postprandial insulin-stacking hypoglycemia
   (`Steil, Rebrin, Darwin, Hariri & Saad`, *Diabetes* 55(12):3344–3350, 2006):**
   In early clinical trials of fully automated subcutaneous-to-subcutaneous
   Proportional-Integral-Derivative (PID) closed-loop insulin delivery without an
   explicit plasma/subcutaneous **Insulin-On-Board (IOB)** feedback constraint,
   the ~60–90 minute pharmacokinetic lag between subcutaneous infusion ($S_1 \to
   S_2 \to I$) and plasma glucose clearance caused the integral term to continue
   dosing elevated insulin throughout a postprandial glucose peak, inducing
   delayed **postprandial hypoglycemia** ($G(t) < 60\text{ mg/dL}$ requiring
   carbohydrate rescue) after the meal was absorbed (`Weinzimer et al.`,
   *Diabetes Care* 2008).

**Architectural lessons for Anneal's 4 `trusted/` primitives:**

- **`Language SemObs` & `Partial`:**
  - In FBA, `defined` must enforce exact elemental/charge conservation ($E \cdot
    S_{\text{int}} = 0$) and Gordan/thermodynamic loop-law feasibility ($\exists
    \mu,\; \forall j \in \text{supp}(v_{\text{int}}),\; v_j (S_{\cdot, j}^T \mu)
    < 0$), flagging Type-III loops as `Partial.ub`.
  - In EWOD microfluidics, `defined` must enforce *both* static ($\|p_i(t) -
    p_j(t)\|_\infty \ge 2$) and dynamic ($\|p_i(t+1) - p_j(t)\|_\infty \ge 2$
    and $\|p_i(t) - p_j(t+1)\|_\infty \ge 2$) Chebyshev spacing plus a clean or
    same-reagent residue state $\text{res}(x, y)$ at every step.
- **`Abstracts` & `ProductiveOn` (Exact Rational Farkas Certificates vs.
  Floating-Point LP Solvers):** Floating-point LP solvers must be treated as
  untrusted witness generators (`StepResult.externalCall`). A metabolic knockout
  design (`OptKnock`) or flux variability bound only satisfies `Abstracts` and
  `ProductiveOn` when its primal flux vector $v \in \mathbb{Q}^{|\mathcal{R}|}$
  and dual Farkas multiplier $y \in \mathbb{Q}^{|\mathcal{M}|}$ are verified in
  Lean's exact `Rat` arithmetic with zero $\epsilon$-feasibility slack.
- **`StepResult.externalCall boundaryInv branches` (Physiological IOB Control
  Barrier Invariant):** In closed-loop physiological controllers, every 5-minute
  pump actuation step interacts with an open-world delayed plant subject to meal
  and exercise disturbances. Enforcing the Control Barrier Function invariant
  $G(t) - \alpha \cdot (\text{IOB}_{S_1}(t) + \text{IOB}_{S_2}(t)) \ge
  G_{\text{crit}}$ inside `boundaryInv` at every sampling boundary mathematically
  rules out insulin-stacking hypoglycemia.

---

### 2. Pure and Applied Mathematics Formalization and Computer-Assisted Proof Failures

#### 2.1 The Kepler Conjecture (Hales 1998 vs. Flyspeck 2014) and Kempe's Four-Color Erratum (1879–1890)

`Basis: documentation + source + execution (support/CrossDomainFailureTaxonomy.lean)`

**Historical incidents and quantitative metrics.**

1. **Kempe's 1879 false proof of the Four-Color Theorem (`Kempe`, *Amer. J.
   Math.* 2(3):193–200, 1879; `Heawood`, *Quart. J. Pure Appl. Math.* 24:332–338,
   1890):** Alfred Bray Kempe published an inductive proof that every planar map
   is 4-colorable by reducing planar graphs via vertex removals of degree $\le 5$.
   When removing a degree-5 vertex $v$ surrounded by neighbors $v_1, v_2, v_3,
   v_4, v_5$ colored with all 4 colors (say $R, G, B, Y, G$), and when both the
   $R\text{--}B$ alternating path (Kempe chain $C_{RB}(v_1, v_3)$) and the
   $R\text{--}Y$ alternating path ($C_{RY}(v_1, v_4)$) are connected in $G
   \setminus \{v\}$, Kempe claimed that one could simultaneously swap $B \leftrightarrow
   G$ in $C_{BG}(v_5)$ and $Y \leftrightarrow G$ in $C_{YG}(v_2)$ to eliminate
   color $G$ from the neighborhood of $v$. For **11 years**, this proof was
   accepted across the mathematical community until Percy John Heawood (1890)
   constructed a 25-vertex planar counterexample demonstrating that the two
   color-swap operations **do not commute**: because $C_{RB}(v_1, v_3)$ and
   $C_{RY}(v_1, v_4)$ intersect across the planar dual, swapping $B \leftrightarrow
   G$ in $C_{BG}(v_5)$ can create a new $Y\text{--}G$ adjacency along the
   boundary of $C_{YG}(v_2)$, so subsequently swapping $Y \leftrightarrow G$ in
   $C_{YG}(v_2)$ produces two adjacent vertices both colored $G$ (`Partial.ub`
   coloring conflict!). Even after **Appel and Haken (1976)** replaced Kempe's
   1-configuration argument with a 1,936-configuration reducible set checked by
   1,200 hours of IBM 360 assembly code, microfiche audit errors persisted until
   **Georges Gonthier (2005)** formalized the 633-configuration Robertson–Sanders–Seymour–Thomas
   proof in `Coq` using a hypermap combinatorial reflection kernel.
2. **Hales's 1998 computer-assisted proof of the Kepler Conjecture vs. the
   `Flyspeck` formalization (`Hales`, *Annals of Mathematics* 162(3):1065–1185,
   2005; `Hales et al.`, *Forum of Mathematics, Pi* 5:e2, 2017):** In August
   1998, Thomas C. Hales and Samuel P. Ferguson announced a proof of the 1611
   Kepler Conjecture (that no packing of congruent spheres in $\mathbb{R}^3$ has
   density exceeding the face-centered cubic packing $\frac{\pi}{\sqrt{18}}
   \approx 0.74048$). The proof relied on:
   - Enumerating ~5,000 planar **tame hypermaps** (representing candidate local
     Delaunay star configurations that could violate the target density bound),
   - Solving ~100,000 linear programming (LP) relaxations, and
   - Discharging ~1,000 nonlinear trigonometric/dihedral inequalities over 6 to 9
     continuous variables using custom unverified C++ interval-arithmetic Taylor
     approximations (~100,000 lines of C++ and Mathematica scripts).
   A panel of 12 referees headed by Gábor Fejes Tóth labored for **4 years**
   (1998–2002) before retiring exhausted, reporting that they were *"99% certain"*
   of the proof's correctness but could not certify the unverified C++ codebase,
   prompting the *Annals of Mathematics* to introduce a policy disclaimer on
   computer-assisted proofs. During the subsequent **11-year `Flyspeck` project**
   (2003–2014, completed in `HOL Light` and `Isabelle/HOL`), Hales and 21
   collaborators uncovered and repaired real mathematical and software defects in
   the 1998 proof:
   - **Tame graph generator omission (`ProductiveOn` / exhaustive orbit coverage
     defect):** In `Nipkow, Bauer & Schultz` (*IJCAR* 2006), formalizing the tame
     plane graph enumerator in `Isabelle/HOL` exposed a symmetry-pruning bug in
     Hales's original Java/C++ generator: an improper isomorphism filter omitted
     2 valid tame graphs while retaining redundant isomorphic copies, violating
     the completeness invariant that every tame configuration is covered by the
     LP/interval refutation suite.
   - **IEEE-754 rounding-mode state corruption and branch-cut bugs in C++ interval
     arithmetic:** Unverified C++ interval libraries rely on hardware FPU dynamic
     rounding-mode switches (`fesetround(FE_DOWNWARD)` / `FE_UPWARD`). Compiler
     instruction reordering across floating-point calls or math library
     transcendental evaluations (`atan`, `acos` near domain boundaries $\pm 1$)
     without proven outward-rounding bounds invalidated individual sub-cube
     certificates, which `Flyspeck` replaced with `Solovyev`'s formal Taylor-interval
     verifier inside `HOL Light`.

**Architectural lessons for Anneal's 4 `trusted/` primitives:**

- **`StepResult.externalCall` & `VerificationResult` (Untrusted C++/CAS Oracles
  Must Emit Kernel-Checked Witnesses):** Hales's 1998 C++ interval code and LP
  solvers acted as trusted external executables whose boolean exit status (`PASS`)
  was accepted as mathematical truth. Under Anneal's architecture, external
  solvers (`StepResult.externalCall`) are **untrusted witness generators**: an
  LP solver must emit dual Farkas multipliers checked in exact rational arithmetic
  at `boundaryInv`, and a nonlinear solver must emit a formal Bernstein/Taylor
  polynomial certificate checked inside the Lean kernel (`theory/`), eliminating
  100,000 lines of C++ from `trusted/`.
- **`Compiles` & Frame Non-Interference (Refuting Kempe's Entangled Chain Swap):**
  Kempe's error is identical to a non-interfering sequential pass composition
  bug: applying color-swap pass $T_1$ (`swap B ↔ G on C_BG(v5)`) invalidates the
  disjointness precondition of pass $T_2$ (`swap Y ↔ G on C_YG(v2)`). In Anneal's
  `Compiles.trans` (`pass_trans`), composing $T_1$ and $T_2$ requires proving
  that the post-state of $T_1$ satisfies the `defined` well-formedness invariant
  (proper 4-coloring + component separation) required by $T_2$.
- **`ProductiveOn` & `InhabitedPre` (Exhaustive Case-Split Coverage):** In
  `Flyspeck`'s tame graph enumeration, if the case-split generator silently drops
  a valid configuration $g^*$, proving `∀ g ∈ generated, Score(g) ≤ 8π` leaves
  $g^*$ unverified. Pairing the generator with a `ProductiveOn` coverage proof over
  the full precondition `pre := IsTamePlaneGraph` ensures no orbit can be dropped.

---

#### 2.2 Voevodsky's Homotopy Cohomology Errors and Simpson's Counterexample to Kapranov–Voevodsky (1989–2013)

`Basis: documentation + source + execution (support/CrossDomainFailureTaxonomy.lean)`

**Historical incidents and quantitative metrics.** In his 2014 Institute for
Advanced Study lecture (*The Origins and Motivations of Univalent Foundations*,
published posthumously in *Bull. Amer. Math. Soc.* 55(4):405–434, 2018), Fields
Medalist Vladimir Voevodsky documented two subtle, multi-year mathematical errors
in his own peer-reviewed papers that convinced him unmechanized human peer review
could no longer guarantee the reliability of modern abstract mathematics:

1. **The Kapranov–Voevodsky strict $\infty$-groupoid theorem (1991) and Carlos
   Simpson's counterexample (1998):** In *$\infty$-groupoids and homotopy types*
   (*Cahiers de Topologie et Géométrie Différentielle Catégoriques* 32(1):29–46,
   1991), Mikhail Kapranov and Vladimir Voevodsky claimed to prove Grothendieck's
   homotopy hypothesis using **strict** $\infty$-groupoids (globular sets where
   all composition and interchange laws hold on the nose as strict equalities,
   rather than up to higher coherent homotopy). Specifically, they constructed a
   Poincaré $\infty$-groupoid functor $\Pi_\infty : \mathbf{Top} \to
   \mathbf{Strict}\text{-}\infty\text{-}\mathbf{Grpd}$ and claimed it induced an
   equivalence of homotopy categories.
   - In October 1998, **Carlos Simpson** published *Homotopy types of strict
     3-groupoids* (`arXiv:math/9810059`), proving that **no strict 3-groupoid can
     have the homotopy 3-type of the 2-sphere $S^2$** (truncated at $\pi_{\le
     3}$). In any strict 3-groupoid $\mathcal{G}$ with strict Eckmann–Hilton
     interchange on 2-morphisms and 3-morphisms, the **Whitehead product**
     $[\iota_2, \iota_2] \in \pi_3(S^2) \cong \mathbb{Z}$ (the Hopf fibration
     generator $\eta : S^3 \to S^2$) is forced to vanish identically ($[\iota_2,
     \iota_2] = 0$), whereas in topology $[\iota_2, \iota_2] = 2 \eta \neq 0$!
   - The bug in Kapranov–Voevodsky (1991) lay in an unverified "obvious"
     fibrancy/kan-extension step when comparing free strict $\infty$-groupoid
     resolutions with topological loop spaces (`Abstracts` failure): strictifying
     the interchange law silently quotiented out non-trivial higher homotopies.
     Because the 1991 paper was widely cited by authorities, Voevodsky himself
     did not accept Simpson's counterexample until **2013**—**15 years after
     Simpson's preprint and 22 years after publication**—when he attempted to
     formalize the step.
2. **Voevodsky's 1993 Suslin–Voevodsky motivic cohomology lemma error (discovered
   1999–2000):** In *Bloch-Kato conjecture and motivic cohomology with finite
   coefficients* (written 1993, published in *The Arithmetic and Geometry of
   Algebraic Cycles*, NATO Sci. Ser. C 548:117–189, 2000), Voevodsky proved a key
   lemma on presheaves with transfers by induction on dimension, omitting the
   check that a natural projection morphism remained an isomorphism after passing
   to simplicial resolutions. While lecturing on the proof at IAS in 1999–2000,
   Pierre Deligne and Voevodsky noticed a gap; closer inspection revealed a
   direct counterexample to the lemma, forcing Voevodsky to spend six years
   developing an entirely new proof before the main theorem could be salvaged.

**Architectural lessons for Anneal's 4 `trusted/` primitives:**

- **`BehaviorCodec` (`obs_decodeOut` and Strict vs. Weak Quotient Collapse):**
  The Kapranov–Voevodsky bug is a textbook example of an **over-strict
  representation quotient**: mapping a weak topological homotopy 3-type $X \in
  L_{\text{Top3}}$ (where $\pi_2(X) \cong \mathbb{Z}$, $\pi_3(X) \cong
  \mathbb{Z}$, and the $k$-invariant / Whitehead bracket $[\iota_2, \iota_2] = 2$)
  into a strict 3-groupoid $G \in L_{\text{Strict3Grpd}}$ (where strict
  interchange forces $[\iota_2, \iota_2] = 0$) changes the observable homotopy
  invariant `SemObs` (`obs(X) = (ℤ, ℤ, 2) ≠ (ℤ, ℤ, 0) = obs(G)`). Under Anneal's
  `BehaviorCodec`, `obs_decodeOut` requires `L₂.obs o₂ = L₁.obs o₁` whenever
  `decodeOut o₂ = some o₁`. Because no strict 3-groupoid can produce `obs = (ℤ,
  ℤ, 2)`, `BehaviorCodec` + `ProductiveOn` immediately refutes the existence of a
  sound compilation from $L_{\text{Top3}}$ to $L_{\text{Strict3Grpd}}$ on $S^2$!
- **`VerificationResult` & `TrustPolicy` (Preventing Unaudited "Folklore Lemma"
  Propagation):** For 15 years, Kapranov–Voevodsky (1991) and Simpson (1998)
  coexisted as contradictory results in the literature because prose papers do
  not carry machine-checked dependency manifests. In Anneal, any theorem relying
  on an unmechanized external lemma must declare that lemma as a typed obligation
  ID in `VerificationResult policy waived obligations` (`trusted/audit/`), so any
  downstream development immediately sees the unproved assumption in its `.olean`
  trust footprint.

---

#### 2.3 Totalized Partial Functions (`0 / 0 = 0`) and Contradictory-Precondition Vacuity in Lean/Mathlib, MiniF2F, and PutnamBench

`Basis: source + execution (support/CrossDomainFailureTaxonomy.lean)`

**Historical incidents and quantitative metrics.** In interactive theorem provers
built on total type theory (`Lean 4` / `Mathlib4`, `Isabelle/HOL`, `Coq`
`SSR`/`MathComp`, `HOL Light`), defining partial mathematical operations as
functions taking proof obligations (`div : (x y : ℝ) → y ≠ 0 → ℝ`) complicates
term rewriting (`rw`, `simp`, `ring`). Consequently, `Lean 4` (`Init.Prelude` /
`Mathlib.Algebra.GroupWithZero.Defs`) and `Isabelle/HOL` totalize partial
operations by assigning arbitrary default values outside their mathematical
domain:

- **Division by zero (`x / 0 = 0`):** In `Mathlib`'s `GroupWithZero`, `a / 0 =
  a * 0⁻¹ = a * 0 = 0` for all $a \in \mathbb{Q}, \mathbb{R}, \mathbb{C}$, and in
  `Lean 4` core `Nat.div`, `n / 0 = 0`.
- **Truncated natural subtraction (`a - b = 0` for `a < b`):** In `Lean 4` core
  `Nat.sub`, `2 - 5 = 0`, invalidating standard algebraic identities such as
  `(a - b) + b = a` unless `b ≤ a` is explicitly hypothesized.
- **Totalized real square root and logarithm:** `Real.sqrt x = 0` for $x < 0$ and
  `Real.log 0 = 0`.

When automated theorem provers and LLM autoformalization pipelines (`MiniF2F`,
`Zheng, Han & Polu`, *ICLR* 2022; `ProofNet`, `Azerbayev et al.` 2023;
`PutnamBench`, `Tsoukalas et al.`, *NeurIPS Datasets & Benchmarks* 2024)
translated competition and undergraduate mathematics problems into Lean, systematic
specification audits revealed three pervasive classes of **formally kernel-accepted
yet mathematically false or vacuous theorems**:

1. **Silent boundary corruption via `0 / 0 = 0` and `Nat.sub` truncation:**
   Formalizing a rational identity such as $\forall x \in \mathbb{R},\; \frac{x^2
   - x}{x - 1} = x$ without the hypothesis $h : x \neq 1$ changes the truth value
   at $x = 1$ (since $(1 - 1)/(1 - 1) = 0 / 0 = 0 \neq 1$), while conversely the false
   algebraic statement $\forall x \in \mathbb{R},\; \frac{0}{x - x} = 0$ is
   **provable by `rfl` / `simp` in Lean** (`0 / 0 = 0`) despite being undefined in
   real analysis! Even worse, in `Nat` arithmetic, an inequality specification
   such as `a - b ≤ c` holds trivially whenever `a < b` because `a - b` silently
   collapses to `0 ≤ c`.
2. **Contradictory-precondition vacuity (`h₁ : x > 0` and `h₂ : x < 0` or
   over-constrained geometry hypotheses in `MiniF2F`):** Audits of `MiniF2F`
   (which led to `MiniF2F-v2` corrections) found multiple autoformalized Olympiad
   problems where a mistranslated hypothesis (such as writing `(n : ℕ)` with
   `h : n < 0`, or writing mutually inconsistent triangle angle/side constraints)
   rendered the theorem's premise logically equivalent to `False`. Automated RL
   provers achieved "new state-of-the-art solve rates" by finding 2-line
   `omega`/`linarith` proofs of `False.elim` without using the theorem's conclusion!
3. **Empty-set supremum / infimum defaults (`sSup ∅ = 0`):** In `ConditionallyCompleteLattice`
   (`ℝ` in `Mathlib`), `sSup S` and `sInf S` return a junk value (`0`) when $S$ is
   empty (`S = ∅`) or unbounded above (`¬ BddAbove S`). A theorem stating "the
   maximum error `sSup {err x | x ∈ Domain}` is `≤ 0`" is provable in one line if
   a typo in `Domain` makes the set empty (`sSup ∅ = 0 ≤ 0`).

**Architectural lessons for Anneal's 4 `trusted/` primitives:**

- **`Partial` (`defined : Prop`, `val : defined → Out → Prop`) vs. Totalized Junk
  Values:** This failure class is the exact reason Anneal's `Trusted/Refinement.lean`
  rejects totalized junk values (`0 / 0 = 0`) and instead wraps every query's
  semantics in `Partial (Out → Prop)`. In `Trusted/MirSemantics.lean` and
  `Trusted/X86Semantics.lean`, division by zero (`rhs == 0`), shift overflow, and
  checked arithmetic overflow step to `.failed .ub` (`defined = False`,
  `Partial.ub`). Because `Partial.ub` is the strict top element above all
  well-defined specifications (`¬ (Partial.ub ≤ p)` when `p.defined`), a program
  that divides by zero or underflows can **never** accidentally satisfy a numeric
  postcondition via `0 / 0 = 0`!
- **`InhabitedPre` & `ProductiveOn` (Eliminating `MiniF2F`-Style Vacuous
  Specifications):** Every `MiniF2F` contradictory-hypothesis bug (`False →
  Post`) and empty-domain `sSup ∅ = 0` bug is an instance of **uninhabited
  precondition vacuity** (`∀ q, pre q → ...` where `∀ q, ¬ pre q`). Anneal's
  `InhabitedPre pre` (`∃ q, pre q`) and `ProductiveOn pre prog` (`∀ q, pre q →
  ∃ h : (sem prog q).defined, ∃ o, (sem prog q).val h o`) structurally block both
  empty-precondition vacuity and empty-outcome-set vacuity inside the Lean kernel.

---

### 3. Physics/PDE Numerical Compilers, Automatic Differentiation, Railway Interlocking, and Aerospace/Autonomy Failures

#### 3.1 PDE Stencil Instabilities (CFL Violation, Non-Conservative Shock Stencils, Symplectic Drift) and Enzyme AD Discontinuous Branch Failures

`Basis: documentation + source + execution (support/CrossDomainFailureTaxonomy.lean)`

**Historical incidents and quantitative metrics.**

1. **Courant–Friedrichs–Lewy (CFL) blow-up, Gibbs negative-density `NaN` cascades,
   and non-conservative shock speed errors (`Hou & LeFloch`, *Math. Comp.*
   62(206):497–530, 1994; `Godunov` 1959):**
   - **Non-conservative discretization wrong shock speeds (`Hou & LeFloch` 1994):**
     When discretizing nonlinear hyperbolic conservation laws such as the
     inviscid Burgers equation $\partial_t u + \partial_x (\frac{1}{2} u^2) = 0$
     or the compressible Euler equations, replacing the divergence flux form
     $\frac{F(u_{i+1/2}) - F(u_{i-1/2})}{\Delta x}$ with the algebraically
     equivalent smooth chain-rule form $u_i \frac{u_i - u_{i-1}}{\Delta x}$
     (which is valid for $C^1$ solutions) causes the discrete scheme to converge
     at $O(\Delta x \to 0)$ to a **mathematically wrong weak solution** whose
     shock wave propagates at the wrong Rankine–Hugoniot speed (failing to
     telescopically conserve total momentum $\sum_i u_i \Delta x$ across the
     shock discontinuity).
   - **CFL violation ($\nu = \frac{|u| \Delta t}{\Delta x} > 1$) and high-order
     Gibbs undershoots:** By Godunov's Order Barrier Theorem (1959), any linear
     numerical stencil of order $p \ge 2$ (such as Lax–Wendroff or unclipped
     high-order WENO/Discontinuous Galerkin) is non-monotone and generates Gibbs
     spurious oscillations near shocks. In compressible gas dynamics where sound
     speed is $c = \sqrt{\gamma P / \rho}$, a single Gibbs undershoot driving
     density $\rho_i < 0$ or pressure $P_i < 0$ causes `sqrt(γ * P / ρ)` to
     evaluate to IEEE-754 `NaN`, which infects the entire stencil neighborhood within
     steps.
   - **Secular energy drift in non-symplectic Hamiltonian integrators (`Wisdom &
     Holman`, *Astron. J.* 102(4):1528–1538, 1991):** Integrating planetary
     $N$-body Hamiltonian equations ($\dot{q} = \partial H / \partial p,\;
     \dot{p} = -\partial H / \partial q$) with standard 4th-order Runge–Kutta
     (`RK4`) instead of a symplectic integrator (Störmer–Verlet / Wisdom–Holman)
     fails to preserve the Poincaré symplectic 2-form $\omega = \sum_i dp_i \wedge
     dq_i$, introducing a secular artificial energy error $\Delta H(t) \propto t
     \cdot \Delta t^4$ that causes simulated planetary orbits to artificially
     spiral inward or eject over million-orbit horizons.
2. **`Enzyme` LLVM reverse-mode Automatic Differentiation across discontinuous
   branches and kinks (`Moses & Churavy`, *NeurIPS* 2020; `Hückelheim,
   Kukreja, Narayanan, Moses, Hovland & Gorman`, *Understanding Automatic
   Differentiation Pitfalls*, `arXiv:2305.07542`, 2023):** `Enzyme` synthesizes
   adjoint gradient code directly from optimized LLVM IR. When differentiating
   scientific simulations containing conditional branches (`br i1 %cmp`), three
   silent derivative failures occur:
   - **Pointwise zero derivative on step/phase-change branches:** Consider a
     phase-change enthalpy or shock-sensor function `f(T)` that branches on
     `if (T > T_melt) { return H_liquid(T); } else { return H_solid(T); }` where
     $H_{\text{liquid}}(T_{\text{melt}}) - H_{\text{solid}}(T_{\text{melt}}) =
     L_{\text{latent}} > 0$. Reverse-mode AD differentiates only the taken basic
     block, completely dropping the Dirac delta distributional jump
     $L_{\text{latent}} \delta(T - T_{\text{melt}})$ at the interface and
     producing a gradient that misses the latent-heat sensitivity entirely.
   - **Equality-branch replacement (`if (x == 0.0)` / `sinc(x)`):** When a library
     programmer guards a Removable Singularity via `if (x == 0.0) return 1.0;
     else return sin(x) / x;`, evaluating the primal at $x = 0.0$ takes the constant
     branch `return 1.0`, so AD computes $f'(0) = 0$ (correct for $\text{sinc}'(0)$,
      **wrong** for $f''(0) = -1/3$, which AD computes as $0.0$ because the active
     branch is constant `1.0`!). Similarly, for `f(x) = (x == y) ? x : y`, along
     the diagonal $x = y$, $\partial_x f + \partial_y f = 1 + 0 = 1$, whereas if
     LLVM's `InstCombine` rewrites the branch before AD to `return y`, AD computes
     $\partial_x f = 0, \partial_y f = 1$—silently swapping partial derivatives on
     the kink!

**Architectural lessons for Anneal's 4 `trusted/` primitives:**

- **`Language SemObs` & `BehaviorCodec.obs_decodeOut` (Ruling Out Non-Conservative
  Stencils):** Setting `SemObs` of a PDE time-step language to the vector of
  discrete conserved integral quantities (total mass $\sum_i \rho_i \Delta x$,
  total momentum $\sum_i m_i \Delta x$, total energy $\sum_i E_i \Delta x$, or
  symplectic shadow-Hamiltonian interval) means `obs_decodeOut` structurally
  **rejects** non-conservative chain-rule discretizations ($u_i \partial_x u_i$,
  `Hou & LeFloch` 1994) because they fail to preserve telescoping flux balance
  across shock cells!
- **`Partial.ub` (`defined = False`) & `decodeOut = none` for `NaN`/CFL/Positivity
  and AD Kinks:**
  - In PDE solvers, `defined` requires the CFL stability bound $\max_i |u_i|
    \frac{\Delta t}{\Delta x} \le C_{\text{CFL}} \le 1$ and strict thermodynamic
    positivity ($\rho_i > 0,\; P_i > 0$), while `decodeOut` maps any IEEE-754
    `NaN` or `±Inf` bit-pattern to `none`.
  - In Automatic Differentiation compilers (`Compiles L_DiffSpec L_Adjoint`), a
    branch instruction `if (p(x) == 0)` on a continuous active variable where
    left and right limit derivatives disagree ($\lim_{x \to c^-} f'(x) \neq
    \lim_{x \to c^+} f'(x)$) must be classified as `Partial.ub` (`defined =
    False`) at the non-differentiable kink $x = c$ unless the specification is
    explicitly lifted to Clarke generalized subgradients $\partial_C f(x)$ via
    `Abstracts`.

---

#### 3.2 Railway Interlocking and CBTC Signaling Failures: Hong Kong MTR Central Collision (2019), Singapore Joo Koon (2017), and ERTMS/ETCS ProB Verification

`Basis: normative + documentation + source + execution (support/CrossDomainFailureTaxonomy.lean)`

**Historical incidents and quantitative metrics.**

1. **18 March 2019 Hong Kong MTR Tsuen Wan Line Central Station collision (EMSD
   Investigation Report, July 2019):** At 02:55 HKT on 18 March 2019, during a
   non-revenue drill of the new **Thales `SelTrac` Communications-Based Train
   Control (CBTC)** signaling system at Central Station on the MTR Tsuen Wan
   Line, two 8-car Metro Cammell EMU trains (**Train `T131`** departing Platform 1
   toward Admiralty and **Train `T112`** entering Platform 2 from Admiralty)
   collided sideswipe on the diamond crossover track (`Points 513A/514B`),
   derailing bogies on both trains and injuring one train captain—the first-ever
   train-to-train collision in the 40-year operating history of the Hong Kong MTR.
   - **Technical root cause (EMSD Report Sections 4–5):** The Central Station
     signaling sector used a primary/secondary/warm-standby-tertiary **Zone
     Controller (`ZC`)** redundancy architecture. During development of a
     software modification (`BuildP38C1`) to add a local data-structure rebuild
     routine (`RebuildRouteConflictTable`) upon switchover to the warm-standby
     tertiary `ZC3`, a contractor programmer omitted the invocation that
     populated the **mutually exclusive route-locking conflict condition** for
     Compound Turnout / Diamond Crossover tracks when `ZC3` initialized from warm
     standby.
   - When the test script simulated a dual-fault failover from Primary `ZC1` and
     Secondary `ZC2` to Warm-Standby Tertiary `ZC3`, `ZC3` came online with an
     **empty route-conflict set for the Central crossover** while still reporting
     system health `OK` (`defined = True` in the unverified status word!). The
     Automatic Train Protection (`ATP`) module on `ZC3` therefore issued
     overlapping **Movement Authorities (`MAs`)** across the same physical
     crossover diamond to both `T131` and `T112`.
2. **15 November 2017 Singapore MRT East–West Line Joo Koon Station collision
   (Singapore LTA / MOT Investigation Report, December 2017):** At 08:18 SGT on
   15 November 2017, an eastbound 6-car川崎 (Kawasaki) C151A train collided into
   the rear of a stationary C151A train at Joo Koon Station during morning peak
   service, injuring 38 passengers and staff.
   - **Technical root cause:** The preceding train suffered a hardware failure on
     one onboard CBTC transpondercomms module while passing over an **uncalibrated
     trackside circuit modification** at Clementi earlier that morning. When the
     train entered the uncalibrated track section, the Thales `SelTrac` CBTC
     protective-bubble state machine (`Software Build`) encountered an unhandled
     state transition that **collapsed the train's tracked length footprint from a
     6-car train (138 meters) to a single 1-car default contour (~23 meters)**.
     The following train's Automatic Train Operation (`ATO`) computed its
     stopping target relative to the phantom 1-car rear boundary—115 meters
     inside the physical rear 5 cars of the stationary train!
3. **ERTMS/ETCS and Paris Métro Line 14 (`METEOR`) formal verification findings
   via `Atelier B` and `ProB` (`Behm, Benoit, Faivre & Meynadier`, *FM* 1999;
   `Leuschel, Falampin, Fritz & Plagge`, *STTT* 2011; `Hansen, Leuschel et al.`,
   *STTT* 22:515–532, 2020):** In contrast to unverified imperative C/C++ CBTC
   builds, Matra Transport / Siemens and RATP formally specified and refined the
   110,000-line B-Method model of **Paris Métro Line 14 (`METEOR`)** in `Atelier
   B`, discharging **27,800 mathematical proof obligations** and translating the
   lowest B refinement machine (`B0`) into 86,000 lines of Ada with **zero bugs
   found in integration, track testing, or 25+ years of driverless operation**.
   Conversely, when Michael Leuschel and collaborators applied the **`ProB`**
   constraint model checker to industrial interlocking topological datasets
   (railML / Alstom Urbalis) and the official **UNISIG ERTMS/ETCS Subset-026
   Hybrid Level 3 (`HL3`)** state machine specifications, `ProB` discovered
   subtle specification bugs where a train splitting/joining or reversing near a
   Virtual Sub-Section (`VSS`) timer expiry caused a race between `Disconnect`
   and `Occupation` packets, momentarily marking an occupied `VSS` block as
   `Free`!

**Architectural lessons for Anneal's 4 `trusted/` primitives:**

- **`StepResult.externalCall boundaryInv branches` (Refuting the MTR Central `ZC3`
  Failover Bug):** A warm-standby controller failover (`ZC1/ZC2 → ZC3`) is a
  classic `StepResult.externalCall` state-handoff transition. In the 2019 MTR
  Central collision, `ZC3` resumed issuing Movement Authorities without verifying
  that its static topological conflict table matched the physical track layout.
  In Anneal, the failover transition must check `boundaryInv`: every physical
  diamond crossover pair $(r_1, r_2) \in \text{PhysicalCrossings}$ is present in
  the active `RouteConflictTable` and all occupied track sections have disjoint
  locked routes before `ZC3` can take a single step. Omitting the table rebuild
  evaluates `boundaryInv = false`, immediately stepping to `.failed
  .invariantViolation` (`Partial.ub`) instead of issuing conflicting `MAs`.
- **`Abstracts` & Monotone Footprint Envelopes (Refuting the Singapore Joo Koon
  6-Car-to-1-Car Shrinkage Bug):** In physical spatial safety (both railway CBTC
  and EWOD microfluidics), a vehicle or droplet's safety halo `Envelope(train)`
  must **over-approximate (`Abstracts`)** its true physical extent
  `PhysicalFootprint(train) ⊆ Envelope(train)`. On sensor degradation or
  uncalibrated track-circuit entry, a sound `Abstracts` transition may *widen*
  the uncertainty envelope (extending the protective bubble to cover the entire
  track circuit block), but can **never shrink** a 6-car (138 m) train to a 1-car
  (23 m) footprint (`PhysicalFootprint ⊈ Envelope`), which directly violates
  `Abstracts`.

---

#### 3.3 Cockpit HCI Mode Confusion and Deep-Space Autonomy Failures: Air Inter Flight 148 (1992), Mars Spirit Sol 18 Flash Anomaly (2004), and Mars Climate Orbiter (1999)

`Basis: normative + documentation + source + execution (support/CrossDomainFailureTaxonomy.lean)`

**Historical incidents and quantitative metrics.**

1. **Air Inter Flight 148 (`F-GGED`, 20 January 1992, Mont Sainte-Odile,
   Strasbourg, France; BEA Official Accident Report, November 1993):** During a
   nighttime VOR/DME non-precision approach to Runway 05 at Strasbourg–Entzheim
   Airport, the flight crew of Airbus A320-111 `F-GGED` intended to command a
   stabilized $-3.3^\circ$ descent angle using **Track / Flight Path Angle
   (`TRK-FPA`)** mode.
   - **The UI / `BehaviorCodec` defect:** On early-production Airbus A320 Flight
     Control Units (FCUs), the vertical target display window consisted of a
     2-digit 7-segment numeric readout shared between two incompatible control
     modes:
     - In `TRK-FPA` mode, rotating the selector knob to `-3.3` displays `-3.3`
       and commands a **$-3.3^\circ$ flight-path angle** (yielding a safe descent
       rate of $\approx -800\text{ ft/min}$ at 145 knots).
     - In `HDG-V/S` (Heading / Vertical Speed) mode, rotating the same knob to
       `33` displays `-33` (representing **$-3,300\text{ ft/min}$**)!
   - Because turbulence earlier in the radar vectoring had caused the crew to
     remain in `HDG-V/S` mode (rather than pressing the `HDG-V/S / TRK-FPA` mode
     pushbutton), dialing `33` into the FCU window commanded a dive of
     **$-3,300\text{ ft/min}$**—more than $4\times$ the intended sink rate. The
     aircraft descended through the minimum safe altitude inside clouds and
     struck Mont Sainte-Odile at 18:20:33 CET, killing **87 of the 96 occupants**
     (and prompting BEA Recommendation 4.2, after which Airbus redesigned the FCU
     display so `V/S` always shows **4 digits** `-3300` while `FPA` shows **2
     digits + decimal** `-3.3`).
2. **Mars Exploration Rover *Spirit* (`MER-A`) Sol 18 Flash File System Anomaly
   (21 January 2004; JPL Anomaly Report, `Reeves & Neilson`, *IEEE Aerospace
   Conference* 2005):** On Sol 18 of surface operations at Gusev Crater, *Spirit*
   failed to acknowledge X-band and UHF relay passes, transmitting only a carrier
   beep indicating fault-protection resets.
   - **Technical root cause:** *Spirit*'s RAD6000 flight computer ran Wind River
     `VxWorks` with a 128 MB RAM pool and a 256 MB flash memory managed by the
     `dosFsLib` file system. During the 7-month cruise to Mars and the first 17
     sols of imaging, flight software created and deleted thousands of telemetry
     and OPNAV product files. However, `dosFsLib` did **not reclaim directory
     slot structures** when files were unlinked, and on every boot initialization,
     `dosFs` dynamically allocated a linked-list shadow table in system DRAM
     proportional to the high-water mark of total historical directory entries
     (*not* active files).
   - On Sol 18, when a routine command triggered a flight software warm reset,
     the boot-time `dosFs` mount exhausted the shared VxWorks DRAM partition! The
     memory allocator triggered a fatal task exception before the command-ingest
     task started, causing the hardware watchdog timer to reboot the processor—which
     immediately re-mounted flash, re-exhausted DRAM, and rebooted again over
     **120 consecutive times** over 3 days, draining battery heaters until JPL
     engineers timed an emergency command into a narrow boot window to start in
     `crippled` RAM-only mode (`NO_FLASH`) and reformat the flash filesystem.
3. **Mars Climate Orbiter (`MCO`) Loss (23 September 1999; NASA Mishap
   Investigation Board Phase I Report, 10 November 1999):** At 09:00:46 UTC on
   23 September 1999, NASA's $327.6 million Mars Climate Orbiter fired its main
   engine for Mars Orbit Insertion (MOI), passed behind Mars at an actual
   periapsis altitude of **$57\text{ km}$** instead of the planned **$226\text{ km}$**
   (well below the $80\text{ km}$ survivable atmospheric entry corridor), and was
   destroyed by atmospheric aerodynamic stress and heating.
   - **Technical root cause:** Because `MCO` had an asymmetric solar array,
     solar radiation pressure built up angular momentum on the reaction wheels,
     requiring daily hydrazine RCS **Angular Momentum Desaturation (`AMD`)**
     thruster firings. Onboard flight software transmitted raw thruster pulse
     durations in telemetry; on the ground, Lockheed Martin Astronautics'
     `SM_FORCES` ("Small Forces") C software converted thruster pulse widths into
     an ASCII impulse file (`AMD` file) consumed by JPL's Orbit Determination
     navigation suite.
   - The **Software Interface Specification (`SIS`)** explicitly mandated metric
     SI units of **Newton-seconds ($\text{N}\cdot\text{s}$)** for each impulse bit.
     Instead, `SM_FORCES` used the imperial thruster performance equation emitted
     by the thruster manufacturer in **pound-force seconds ($\text{lbf}\cdot\text{s}$)**
     without multiplying by the conversion factor $4.4482216\text{ N/lbf}$. Over
     9 months of cruise and 10+ AMD events, every desaturation burn injected a
     $4.45\times$ unmodeled velocity perturbation, biasing the reconstructed
     trajectory by $170\text{ km}$ at Mars arrival.

**Architectural lessons for Anneal's 4 `trusted/` primitives:**

- **`BehaviorCodec` (`encodeOut_of_decodeOut` and `obs_decodeOut` Mode
  Transparency & Dimensional Soundness):**
  - **Air Inter 148:** Let $L_{\text{Auto}}$ be the autopilot state machine
    (with states `(mode = FPA, target = -33)` meaning $-3.3^\circ$ and `(mode =
    VS, target = -33)` meaning $-3,300\text{ ft/min}$) and $L_{\text{Display}}$
    be the pilot's FCU display language where `SemObs` tracks both the rendered
    2-digit string `"-33"` and the physical vertical acceleration envelope. If
    both states project to the same 2-digit display string `"-33"` while inducing
    divergent physical vertical rates ($-800\text{ ft/min}$ vs. $-3,300\text{ ft/min}$),
    no `BehaviorCodec` can simultaneously satisfy `encodeOut_of_decodeOut`
    (injectivity on displayed states) and `obs_decodeOut` (preservation of the
    physical descent spine)! Requiring a verified `BehaviorCodec` between the
    cockpit display and the control law **mathematically forces the 4-digit
    `"-3300"` vs. `"-3.3"` disambiguation** that Airbus implemented after the
    crash.
  - **Mars Climate Orbiter:** Across the `SM_FORCES` $\to$ `JPL_Nav` interface,
    encoding physical impulse in `SemObs` as a canonical rational quantity in
    millinewton-seconds ($\text{mN}\cdot\text{s}$) causes a producer emitting raw
    $\text{lbf}\cdot\text{s}$ ($4448\text{ mN}\cdot\text{s}$ per unit) and a
    consumer decoding $\text{N}\cdot\text{s}$ ($1000\text{ mN}\cdot\text{s}$ per
    unit) to violate `obs_decodeOut` (`4448 * I ≠ 1000 * I` for any `I > 0`),
    catching the unit mismatch at compile time inside the Lean kernel.
- **`ProductiveOn` & `StepResult.externalCall` (Refuting the Mars Spirit Sol 18
  Flash Boot Livelock):** Notice why the *Spirit* Sol 18 bug is so insidious for
  traditional memory-safety verification: the VxWorks allocator **succeeded in
  preventing an out-of-bounds memory corruption (`defined = True`)** by raising
  an out-of-memory exception and triggering a clean watchdog reset! Under a pure
  partial-correctness safety check (`sem ≤ WellFormed`), an infinite reboot loop
  at boot time is **100% safe** because no memory-corrupting instruction ever
  executes (`val h = ∅` of completed command cycles). In Anneal, requiring
  `ProductiveOn pre bootSequence` over `EventualBehaviorOf`—together with a
  persistent flash-metadata capacity invariant in `StepResult.externalCall
  boundaryInv` across warm resets (`totalDirectoryEntries ≤ maxDramMountQuota`)—refutes
  the unbounded directory-table leak and guarantees that every warm reset reaches
  the command-ingest loop in finite steps.

---

### 4. Cross-Domain Failure-to-Primitive Architectural Matrix and Mechanized Counterexample Suite

`Basis: source + execution + derived (support/CrossDomainFailureTaxonomy.lean)`

Table 1 synthesizes all 12 historical failure classes across synthetic biology,
molecular programming, metabolic and microfluidic engineering, mathematical
formalization, scientific computing, railway interlocking, and aerospace
autonomy, mapping each failure's root cause to the exact Anneal `trusted/`
primitive that refutes it and the corresponding zero-axiom theorem in
[support/CrossDomainFailureTaxonomy.lean](support/CrossDomainFailureTaxonomy.lean).

| # | Domain & Historical Incident | Root Technical Failure Mode | Violated Anneal `trusted/` Primitive | Mechanized Refutation Theorem in `support/CrossDomainFailureTaxonomy.lean` |
| :- | :--- | :--- | :--- | :--- |
| **1** | **Biocomputing (`Cello 1.0`, `Nielsen et al.` *Science* 2016):** 15/60 (25%) *E. coli* logic circuits failed in vivo | Unmodeled host ribosome/RNAP resource saturation (`rLoad > rMax`), tandem promoter roadblocking, and downstream retroactivity | `Partial.ub` (`defined := rLoad ≤ rMax`), `StepResult.externalCall` host coupling, & `VerificationResult` UCF waivers | `cello_unmodeled_resource_overload_refuted` (`L174-190`) |
| **2** | **DNA Strand-Displacement (`Qian & Winfree` *Science* 2011; `Visual DSD`):** Zero-input seesaw gate leak cascades | Blunt-end coaxial base stacking and helix fraying release output strand `1` when input is `0` (`{0, 1} ⊈ {0}`) | `Compiles L_ideal L_phys codec s t` (target outcomes exceed source specification) | `dsd_zero_input_leak_breaks_compiles` (`L209-222`) |
| **3** | **Stochastic CRNs (`Angeli, De Leenheer & Sontag` 2007):** Finite-molecule boundary extinction despite ODE stability | Autocatalytic motif ($A + B \to 2B, B \to A$) empties critical siphon $Z = \{B\}$ ($N_B = 0$) with probability 1 | `ProductiveOn pre crn` (kinetically trapped zero-rate boundary state produces `val h = ∅`) | `crn_stochastic_siphon_breaks_productiveOn` (`L235-239`) |
| **4** | **Genome-Scale FBA (`Schellenberger` 2011; `MEMOTE` 2020; `QSopt_ex`):** Spurious ATP synthesis & $\epsilon$-feasibility leaks | Internal Type-III futile cycle ($S_{\text{int}} c = 0$) with no chemical potential drop, plus $10^{-7}$ IEEE-754 simplex mass leaks | `Partial.ub` (Gordan loop law $\Delta G \cdot v < 0$) & exact rational Farkas `Abstracts` / `ProductiveOn` | `fba_type_iii_loop_violates_thermodynamics` (`L252-257`) |
| **5** | **Digital Microfluidics (`MFSim`, `Grissom & Brisk` 2015):** Accidental EWOD droplet merge & cross-contamination | Static spacing $\|p_1(t) - p_2(t)\|_\infty \ge 2$ holds at ticks $t, t+1$ while dynamic cross-step $\|p_1(t+1) - p_2(t)\|_\infty = 1$ merges menisci | `Partial.ub` (`defined := DynamicSpacingOk ∧ CleanResidue`) | `ewod_static_spacing_misses_dynamic_coalescence` (`L272-276`) |
| **6** | **Combinatorial Proofs (`Kempe` 1879 $\to$ `Heawood` 1890; `Hales` 1998 $\to$ `Flyspeck` 2014):** Entangled chain swaps & C++ interval/enumerator bugs | Non-commuting dual Kempe swaps invalidate intermediate 4-coloring; unverified C++ tame-graph filter dropped 2 orbits | `Compiles.trans` intermediate `defined` preservation, `ProductiveOn` orbit completeness, & `StepResult.externalCall` witness checking | `simpson_refutes_kapranov_voevodsky_strict_3groupoid` & `lean_total_div_zero_vs_anneal_partial_ub` (`L311-350`) |
| **7** | **Homotopy Foundations (`Kapranov & Voevodsky` 1991 $\to$ `Simpson` 1998):** Strict 3-groupoids cannot model $S^2$ | Strict Eckmann–Hilton interchange forces Whitehead product $[\iota_2, \iota_2] = 0$, whereas $\pi_3(S^2)$ has $[\iota_2, \iota_2] = 2\eta \neq 0$ | `BehaviorCodec.obs_decodeOut` + `ProductiveOn` (quotienting out higher homotopies alters `SemObs`) | `simpson_refutes_kapranov_voevodsky_strict_3groupoid` (`L311-329`) |
| **8** | **Autoformalization (`MiniF2F` 2021; `PutnamBench` 2024; `Lean/Mathlib`):** `0 / 0 = 0` totalization & vacuous premises | Totalized `0 / 0 = 0` and `a - b = 0` ($a < b$) validate false identities; contradictory hypotheses (`x > 0 ∧ x < 0`) prove anything via `False.elim` | `Partial.ub` (`defined = False` on divisor `0`) & `InhabitedPre pre` (`∃ q, pre q`) | `lean_total_div_zero_vs_anneal_partial_ub` (`L338-347`) |
| **9** | **PDE Compilers & AD (`Hou & LeFloch` 1994; `Enzyme AD`, `Hückelheim & Moses` 2023):** Wrong shock speeds & branch derivative errors | Non-conservative $u \partial_x u$ stencil violates discrete momentum conservation across shocks; `Enzyme` AD across `if (x == 0)` drops jump/kink sensitivity | `BehaviorCodec.obs_decodeOut` (conserved integral spine `SemObs`) & `Partial.ub` on non-differentiable branch kinks | `pde_nonconservative_stencil_breaks_compiles` (`L365-374`) & `enzyme_kink_discontinuity_flagged_as_ub` (`L384-386`) |
| **10** | **Railway CBTC (`MTR Central` 18 Mar 2019; `Singapore Joo Koon` 15 Nov 2017; `ProB` ERTMS):** Crossover collision & protective-bubble shrinkage | `ZC1 → ZC3` warm-standby failover omitted `RebuildRouteConflictTable` for Central crossover; Joo Koon track circuit shrank 6-car (138 m) train to 1-car (23 m) bubble | `StepResult.externalCall` failover `boundaryInv` (`crossoverLockPopulated = true`) & `Abstracts` spatial over-approximation | `mtr_central_2019_unpopulated_crossover_rejected` (`L404-406`) & `joo_koon_2017_bubble_shrinkage_violates_abstracts` (`L418-425`) |
| **11** | **Cockpit HCI (`Air Inter Flight 148`, 20 Jan 1992):** A320 `-3.3°` FPA vs. `-3,300 ft/min` V/S mode confusion | Shared 2-digit FCU window rendered `-3.3°` FPA ($800\text{ ft/min}$) and `-3,300 ft/min` V/S as `-33`, violating display-to-actuator mode injectivity | `BehaviorCodec` (`encodeOut_of_decodeOut` + `obs_decodeOut` over `(DisplayToken × SinkRate)`) | `air_inter_148_mode_confusion_impossible_under_behaviorCodec` (`L448-450`) |
| **12** | **Deep-Space Autonomy (`Mars Spirit Sol 18` 2004; `Mars Climate Orbiter` 1999):** Flash `dosFs` reboot livelock & `lbf·s` vs. `N·s` unit loss | Unlinked flash directory entries exhausted DRAM at boot, causing 120+ safe watchdog resets (`val = ∅`); `SM_FORCES` emitted `lbf·s` ($4.45\times$ `N·s`) | `ProductiveOn` (refutes safe boot livelock) & `BehaviorCodec.obs_decodeOut` (refutes `4448 mN·s ≠ 1000 mN·s` unit mismatch) | `spirit_sol18_reboot_livelock_safe_but_not_productive` (`L466-475`) & `mars_climate_orbiter_unit_mismatch_refuted` (`L495-503`) |

## Boundaries

The following boundaries separate what this report establishes from cases that
remain unexamined or outside the scope of the mechanized models:

- **Stochastic master-equation transition rates vs. topological siphon
  reachability (`not examined`):** Theorem
  `crn_stochastic_siphon_breaks_productiveOn` in
  `support/CrossDomainFailureTaxonomy.lean` models the reachability of the
  boundary siphon state $N_B = 0$ and its absorbing failure of `ProductiveOn`.
  It does not mechanize continuous-time Markov chain (CTMC) Kolmogorov forward
  equations or mean-extinction-time asymptotics ($\mathbb{E}[T_{\text{ext}}] \sim
  e^{c V}$).
- **Full nonlinear floating-point Navier–Stokes / Euler roundoff propagation
  (`not examined`):** Theorem `pde_nonconservative_stencil_breaks_compiles`
  verifies the algebraic violation of discrete momentum conservation (`SemObs`)
  between conservative Godunov flux differences and non-conservative chain-rule
  differences on a 2-cell shock step. Full IEEE-754 rounding-error accumulation
  across multi-dimensional WENO stencils is not mechanized in this package.
- **Proprietary Thales `SelTrac` source code (`unknown`):** Analysis of the 18
  March 2019 Hong Kong MTR Tsuen Wan Line Central collision and the 15 November
  2017 Singapore MRT Joo Koon collision is derived from the official statutory
  investigation reports published by the Hong Kong Electrical and Mechanical
  Services Department (EMSD, July 2019) and the Singapore Land Transport
  Authority / Ministry of Transport (December 2017). The proprietary C/C++
  source code of `BuildP38C1` is not publicly available and was `not examined`.
- **Attractive stronger claim that `BehaviorCodec` alone prevents pilot error
  (`known not to apply`):** A verified `BehaviorCodec` between an avionics
  control law and a cockpit display (`encodeOut_of_decodeOut` + `obs_decodeOut`)
  guarantees that distinct physical control modes have distinct, non-colliding
  visual annunciations on the display (eliminating the Air Inter Flight 148
  2-digit `-33` representation collision). It does not by itself guarantee that
  a human operator under high cognitive workload will visually attend to the
  annunciator without an explicit human-factors scan assumption tracked in
  `VerificationResult` / `TrustPolicy`.

## Evidence

1. **Anneal core verification framework (`source`):**
   - Repository: `joshlf/anneal` at commit
     `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted/lean/Trusted/Refinement.lean`,
     `trusted/lean/Trusted/StepResult.lean`, `trusted/lean/Trusted/MirSemantics.lean`)
     and commit `4f45f0a391a921ced9c9dc773b9a040dbc215d14`
     (`trusted/lean/Trusted/X86Semantics.lean`,
     `theory/Anneal/Compiler/NaiveCodegen.lean`,
     `theory/Anneal/Compiler/Peephole.lean`).
   - Companion `reference` corpus reports (`observed_at: 2026-10-31`):
     `anneal-behavior-codec-and-progress-refinement-2026`,
     `anneal-partial-compile-and-conditioning-refinement-2026`,
     `anneal-structural-external-calls-and-tcb-mutation-testing-2026`, and
     `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`.
2. **Synthetic biology, CRN, metabolic, and microfluidic primary sources
   (`documentation` + `normative`):**
   - Alec A. K. Nielsen et al., *Genetic circuit design automation*, *Science*
     352(6281):aac7341 (1 April 2016), DOI `10.1126/science.aac7341` (60 *E.
     coli* circuits compiled by `Cello`; 45/60 succeeded first-pass, 15/60 failed
     due to toxicity, roadblocking, and retroactivity).
   - Lulu Qian and Erik Winfree, *Scaling up digital circuit computation with
     DNA strand displacement cascades*, *Science* 332(6034):1196–1201 (3 June
     2011), DOI `10.1126/science.1200520`; Chris Thachuk, Erik Winfree, and
     David Soloveichik, *Leakless DNA Strand Displacement Systems*, *DNA 21*,
     LNCS 9211:133–153 (2015), DOI `10.1007/978-3-319-21999-8_9`.
   - David Angeli, Patrick De Leenheer, and Eduardo D. Sontag, *A Petri net
     approach to the study of persistence in chemical reaction networks*,
     *Mathematical Biosciences* 207(1):107–129 (2007), DOI
     `10.1016/j.mbs.2006.11.007`.
   - Christian Lieven et al., *MEMOTE for standardized genome-scale metabolic
     model testing*, *Nature Biotechnology* 38:272–276 (2020), DOI
     `10.1038/s41587-020-0446-y`; Jan Schellenberger, Nathan E. Lewis, and
     Bernhard Ø. Palsson, *Elimination of Thermodynamically Infeasible Loops in
     Steady-State Metabolic Models*, *Biophysical Journal* 100(3):544–553 (2011),
     DOI `10.1016/j.bpj.2010.12.3707`.
   - Daniel Grissom et al., *An Open-Source Compiler and PCB Synthesis Tool for
     Digital Microfluidic Biochips*, *ACM JETC* 12(2):16 (2015), DOI
     `10.1145/2743025` (`MFSim`).
   - Garry M. Steil et al., *Feasibility of Automating Insulin Delivery for the
     Treatment of Type 1 Diabetes*, *Diabetes* 55(12):3344–3350 (2006), DOI
     `10.2337/db06-0419`.
3. **Mathematical formalization and autoformalization primary sources
   (`documentation` + `source`):**
   - Alfred B. Kempe, *On the Geographical Problem of the Four Colours*, *Amer.
     J. Math.* 2(3):193–200 (1879), DOI `10.2307/2369235`; Percy J. Heawood,
     *Map-Colour Theorem*, *Quart. J. Pure Appl. Math.* 24:332–338 (1890).
   - Thomas Hales et al., *A Formal Proof of the Kepler Conjecture*, *Forum of
     Mathematics, Pi* 5:e2 (2017), DOI `10.1017/fmp.2017.1`; Tobias Nipkow,
     Gertrud Bauer, and Paula Schultz, *Flyspeck I: Tame Graphs*, *IJCAR* 2006,
     LNCS 4130:21–35.
   - Mikhail Kapranov and Vladimir Voevodsky, *$\infty$-groupoids and homotopy
     types*, *Cah. Topol. Géom. Différ. Catég.* 32(1):29–46 (1991); Carlos
     Simpson, *Homotopy types of strict 3-groupoids*, `arXiv:math/9810059`
     (October 1998); Vladimir Voevodsky, *The Origins and Motivations of
     Univalent Foundations*, *Bull. Amer. Math. Soc.* 55(4):405–434 (2018).
   - Kunhao Zheng, Jesse Michael Han, and Stanislas Polu, *MiniF2F: a
     cross-system benchmark for formal Olympiad-level mathematics*, *ICLR* 2022
     (`openai/miniF2F`); George Tsoukalas et al., *PutnamBench: Evaluating
     Neural Theorem-Provers on the Putnam Mathematical Competition*, *NeurIPS*
     2024 (`trishullab/PutnamBench`).
4. **Scientific computing, railway interlocking, and aerospace investigation
   reports (`normative` + `documentation`):**
   - Thomas Y. Hou and Philippe G. LeFloch, *Why nonconservative schemes
     converge to wrong solutions: error analysis*, *Mathematics of Computation*
     62(206):497–530 (1994); Jack Wisdom and Matthew Holman, *Symplectic maps
     for the $n$-body problem*, *Astronomical Journal* 102(4):1528–1538 (1991).
   - William S. Moses and Valentin Churavy, *Instead of Rewriting Foreign Code
     for Machine Learning, Automatically Synthesize Fast Gradients*, *NeurIPS*
     33:12472–12485 (2020) (`EnzymeAD/Enzyme`); Jan Hückelheim et al.,
     *Understanding Automatic Differentiation Pitfalls*, `arXiv:2305.07542`
     (2023).
   - Electrical and Mechanical Services Department (EMSD), Government of the
     Hong Kong SAR, *Investigation Report on Incident of the New Signalling
     System Testing on MTR Tsuen Wan Line on 18 March 2019* (5 July 2019).
   - Land Transport Authority (LTA) / Ministry of Transport (MOT) Singapore,
     *Joo Koon Collision Investigation Report* (16 December 2017).
   - Dominik Hansen, Michael Leuschel et al., *Using a formal B model at runtime
     in a demonstration of the ETCS hybrid level 3 concept with real trains*,
     *Int. J. Softw. Tools Technol. Transf. (STTT)* 22:515–532 (2020), DOI
     `10.1007/s10009-019-00548-6`.
   - Bureau d'Enquêtes et d'Analyses (BEA), *Rapport de la commission d'enquête
     sur l'accident survenu le 20 janvier 1992 près du Mont Sainte-Odile (Bas-Rhin)
     à l'Airbus A 320 immatriculé F-GGED exploité par la compagnie Air Inter*
     (26 November 1993).
   - Glenn Reeves and Tracy Neilson, *The Mars Rover Spirit FLASH Anomaly*,
     *2005 IEEE Aerospace Conference*, pp. 4186–4199 (2005), DOI
     `10.1109/AERO.2005.1559723`.
   - Arthur G. Stephenson et al., *Mars Climate Orbiter Mishap Investigation
     Board Phase I Report*, NASA (10 November 1999).
5. **Mechanized Lean 4 counterexample and refutation suite (`execution`):**
   - Preserved in
     [support/CrossDomainFailureTaxonomy.lean](support/CrossDomainFailureTaxonomy.lean)
     and verified on 2026-10-31 using `leanprover/lean4:v4.34.1` with
     `-DElab.async=false -Ddebug.skipKernelTC=false`. All 14 theorems print
     `'...' does not depend on any axioms`.

## Revalidation

To revalidate the mechanized counterexamples and refutation proofs in this
report package against the Lean 4 kernel with zero axioms, run:

```console
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/anneal-synbio-crns-pde-physics-math-rail-verification-failures-2026/support/CrossDomainFailureTaxonomy.lean
```

Confirm that the command exits with status `0` and that all 14 `#print axioms`
queries output `'Anneal.FailureTaxonomy.<theorem>' does not depend on any axioms`.
