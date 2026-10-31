# Historical verification, compiler, and modeling failures across AI safety, neural certification, automated planning, CAD/CAM, structural engineering, media pipelines, and IoT automation

## Summary

Across safety-critical AI, automated planning, computational fabrication, civil
engineering, graphics and audio pipelines, and cyber-physical smart-home
systems, historical verification and compilation failures rarely stem from
errors in pure mathematical derivations. Instead, postmortems across these
domains expose four recurring structural failure modes at the boundary between
formal models, compilers, and physical or runtime execution:

1. **Semantic gap between idealized verification domains and concrete execution
   (`Language SemObs` and `Partial` mismatch):** Neural network verifiers proved
   adversarial robustness over exact real arithmetic ($\mathbb{R}$) while
   deployed inference executed in non-associative IEEE-754 floating-point
   arithmetic (Jia and Rinard, SAS 2021; `VNN-COMP` 2021–2024); the unverified
   C++ PDDL plan validator `VAL` mutated state sets with inconsistent
   `delete`/`add` micro-step ordering (Abdulaziz and Lammich, ICTAI 2018); and
   3D CNC simulators modeled `G00` rapid traverses as straight lines while
   physical controllers executed independent per-axis "dogleg" paths that
   crashed spindles into fixtures.
2. **Unsound abstraction and unverified representation lowering (`BehaviorCodec`,
   `Compiles`, and `Abstracts` failures):** The 1978 Hartford Civic Center roof
   collapse and the 1991 Sleipner A offshore platform sinking ($47\%$ shear
   underestimation in `NASTRAN`) occurred because coarse structural abstractions
   omitted eccentric buckling modes and failed element-equilibrium well-formedness
   checks (`decodeOut = none`). Similarly, `OpenSCAD`/`CGAL` boolean pipelines
   generated non-manifold meshes when exact kernel coordinates snapped to
   floating-point STL grids (motivating `elalish/manifold` and `mkeeter/fidget`),
   and smart-home rule verifiers missed physical-channel feedback loops
   (heater $\to$ temperature $\to$ window $\to$ security alarm) by analyzing
   digital variables without abstracting the shared physical environment
   (`SOTERIA`, USENIX ATC 2018; `iRuler`, USENIX Security 2019).
3. **Vacuous satisfaction, over-refusal, and non-termination (`ProductiveOn`,
   `InhabitedPre`, and `EventualBehaviorOf` violations):** AI guardrails tuned
   to block indirect prompt injections (`NeMo Guardrails`, `LlamaGuard`) suffer
   from severe over-refusal on benign workflows (`XSTest`, `OR-Bench`), acting
   as vacuous safety filters that preserve safety by destroying utility
   ($\neg\mathsf{ProductiveOn}$). In branch-and-bound neural verification,
   inconsistent `ReLU` split constraints render sub-problem preconditions
   uninhabited ($\neg\mathsf{InhabitedPre}$). In UI layout (`Cassowary` / iOS
   `Auto Layout`), GPU shaders (`GraphicsFuzz`, `Dawn`/`Tint`/`Naga`), TrueType
   font bytecode (`FreeType`, `ATMFD.dll`), and IIR audio DSP filters, missing
   progress and numeric-domain guards cause exponential simplex stalls, GPU
   Timeout Detection and Recovery (`TDR`) hangs, kernel memory corruption, and
   $100\times$ subnormal CPU spikes.
4. **Implicit trust in unverified heuristics and external solvers
   (`VerificationResult` and `TrustPolicy` conflation):** Putting an unverified
   LP/MILP solver (`10^-6` feasibility tolerance in `VNN-COMP`), an LLM
   guardrail judge, or an unverified CAD/FEA preprocessor inside the trusted
   computing base allows a single solver tolerance slip or prompt-injected
   payload to falsify system-wide safety claims without an auditable waiver.

For Anneal, these postmortems validate the exact design of its four `trusted/`
semantic primitives: **(1) `Language SemObs` and `Partial`** (totality of safety
guards via `defined` before outcome refinement via `val`), **(2) `BehaviorCodec`
(`Compiles` and `Abstracts`)** (total input encoding, partial output decoding
`decodeOut = none` for representation invariants, and `obs_decodeOut` spine
preservation), **(3) `ProductiveOn` and `InhabitedPre` (`EventualBehaviorOf`
and `StepResult.externalCall`)** (anti-vacuity, $1 \to k$ step decoupling, and
demonic environment/oracle nondeterminism), and **(4) positive per-obligation
`VerificationResult` (`ob.id ∈ waived ∨ ob.prop`)** (preventing unverified
heuristics or localized waivers from contaminating machine-checked proofs).

## Applicability

This report documents historical verification, compiler, and numerical modeling
failures across eight non-systems and cyber-physical domains—neural-network
certification, agentic AI guardrails, automated PDDL planning, CAD/CAM/textile
manufacturing, civil/structural finite-element engineering, graphics/font/layout
engines, real-time audio DSP, and smart-home trigger-action IoT platforms—and
maps their root causes to Anneal's `trusted/` verification architecture at
`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`.

The primary technical subjects examined are:

- **Neural-network verifier soundness bugs:** Jia and Rinard, *Exploiting
  Verified Neural Networks via Floating Point Numerical Error*, SAS 2021
  (`arXiv:2003.03021`, DOI `10.1007/978-3-030-88806-0_9`); and the International
  Verification of Neural Networks Competition (`VNN-COMP`) summary reports for
  2021 (`arXiv:2109.00498`), 2022 (`arXiv:2212.10376`), 2023
  (`arXiv:2312.16760`), and 2024 (`arXiv:2412.19985`), covering `ERAN`,
  `Reluplex`/`Marabou`, `MIPVerify`, `VeriNet`, `CGDTest`, `NNV`, and
  `α,β-CROWN`.
- **Agentic AI guardrail bypasses and over-refusal:** Indirect prompt injection
  evaluations (`AgentDojo`, `arXiv:2406.13352`; `InjecAgent`,
  `arXiv:2403.02691`), capability-isolated agent architectures (`CaMeL`,
  Debenedetti et al., `arXiv:2503.18813`), and safety over-refusal benchmarks
  (`XSTest`, Röttger et al., NAACL 2024, `arXiv:2308.01263`; `OR-Bench`, Cui et
  al., `arXiv:2405.20947`) applied to `NeMo Guardrails` and `LlamaGuard`.
- **Automated planning validator bugs:** Abdulaziz and Lammich, *A Formally
  Verified Validator for Classical Planning Problems and Solutions*, ICTAI 2018
  (`arXiv:1807.09726`, DOI `10.1109/ICTAI.2018.00079`), contrasting their
  Isabelle/HOL-verified validator against the unverified C++ IPC validator `VAL`
  (Howey, Long, and Fox, ICTAI 2004) and `INVAL`.
- **CAD/CAM, CNC G-code, machine knitting, and structural engineering
  failures:** `OpenSCAD`/`CGAL` non-manifold boolean failures vs.
  `elalish/manifold` and `mkeeter/fidget`; CNC `G00` rapid-traverse dogleg
  collision kinematics; `Knitout` (McCann et al., SIGGRAPH 2016, DOI
  `10.1145/2897824.2925940`) and `Autoknit` (Narayanan et al., SIGGRAPH 2018,
  DOI `10.1145/3197517.3201335`) needle-transfer and yarn-tension limits; the
  1978 Hartford Civic Center space-frame collapse (Lev Zetlin Associates report);
  and the 1991 Sleipner A offshore platform finite-element shear failure
  (SINTEF / Det Norske Veritas inquiry reports).
- **Graphics shaders, font bytecode, UI layout, audio DSP, and IoT rules:**
  `GraphicsFuzz` (Donaldson et al., OOPSLA 2017, DOI `10.1145/3133917`) and
  WebGPU `Dawn`/`Tint`/`Naga` uniformity and bounds bugs; TrueType/OpenType font
  vulnerabilities `CVE-2015-2426` (`ATMFD.dll`) and `CVE-2020-15999`
  (`FreeType`); Apple iOS `Auto Layout` (`Cassowary`) unsatisfiable constraint
  exceptions and exponential simplex stalls; IIR biquad zero-input limit cycles
  and IEEE-754 subnormal CPU stalls (`FTZ`/`DAZ`); and smart-home physical
  interaction analyzers `SOTERIA` (Celik et al., USENIX ATC 2018) and `iRuler`
  (Wang et al., USENIX Security 2019).

These findings apply directly when designing or auditing Anneal's core semantic
structures (`Language`, `Partial`, `BehaviorCodec`, `Compiles`, `Abstracts`,
`EventualBehaviorOf`, `StepResult.externalCall`, `ProductiveOn`, `InhabitedPre`,
and `VerificationResult`) and when building domain-specific verifiers or
certificate checkers on top of Anneal. They do not imply that Anneal's
`trusted/` kernel should embed domain-specific physics, floating-point LP
solvers, or CAD geometry kernels; rather, they establish what invariants
`trusted/` must enforce so domain theories in `theory/` cannot fail open.

## Findings

### 1. Cross-domain failure taxonomy and mapping to Anneal's `trusted/` primitives

Every historical failure examined in this report instantiates one or more of six
structural defects that Anneal's four `trusted/` primitive families are
designed to prevent:

| Defect class | Representative historical incidents | Anneal `trusted/` primitive that blocks the defect |
| :--- | :--- | :--- |
| **Ideal-math vs. machine-arithmetic gap** | Jia & Rinard (2021) breaking `ERAN`/`MIPVerify` via IEEE-754 rounding; `VNN-COMP` GPU non-associativity in `α,β-CROWN`; `CGAL` exact-to-float STL snap self-intersections; audio DSP subnormal CPU spikes | `Language SemObs` concrete machine semantics (`BitVec` / IEEE-754 `Float32`) + `Abstracts` conservative rounding envelopes |
| **Validator micro-step & boundary semantics bug** | PDDL `VAL` accepting invalid plans due to `add`/`delete` ordering & $\epsilon$-boundary drift; CNC `G00` dogleg rapid collisions missed by linear CAM simulators | Kernel-checked operational semantics in `trusted/` (`StepResult`, `EventualBehaviorOf`) with `Partial.ub` (`defined = False`) on any intermediate hazard prefix |
| **Ill-formed intermediate representation / mesh** | Sleipner A `NASTRAN` skewed tricell element mesh ($47\%$ shear error); `OpenSCAD` non-manifold edges; `Knitout` stranded live loops at program end | `BehaviorCodec.decodeOut = none` rejecting ill-formed target states before outcome comparison |
| **Unmodeled environment or physical coupling** | Hartford Civic Center unmodeled eccentric top-chord buckling; `SOTERIA`/`iRuler` heater $\to$ temp $\to$ window $\to$ alarm physical loops; `Autoknit` yarn-tension breakage across racks | `Abstracts` over coupled environment state + `StepResult.externalCall boundaryInv branches` for nondeterministic plant/environment interactions |
| **Vacuous satisfaction / over-refusal / hang** | `NeMo Guardrails` / `LlamaGuard` blocking benign prompts (`XSTest`/`OR-Bench`); empty `BaB` split cells in neural verification; iOS `Auto Layout` exponential freeze; shader `TDR` infinite loops | `InhabitedPre` (non-empty valid inputs) + `ProductiveOn` (existence of terminating, non-UB execution) + `obs_decodeOut` (observable spine preservation) |
| **Unverified solver or oracle in the TCB** | `VNN-COMP` false `UNSAT` from Gurobi/CPLEX `10^-6` tolerances (`VeriNet`, `Marabou`, `CGDTest`); indirect prompt injection subverting LLM safety judges (`AgentDojo`) | Positive per-obligation `VerificationResult` (`ob.id ∈ waived ∨ ob.prop`) + certificate checking in `theory/` instead of trusting external solver verdicts |

Basis: **derived** synthesis across the primary literature, CVEs, and forensic
reports cited in Sections 2–6.

---

### 2. Neural-network verifier soundness failures (`VNN-COMP` and floating-point attacks)

#### 2.1 Jia and Rinard (SAS 2021): Exploiting verified neural networks via IEEE-754 numerical error

In *Exploiting Verified Neural Networks via Floating Point Numerical Error*
(SAS 2021, `arXiv:2003.03021`), Kai Jia and Martin Rinard demonstrated that
neural networks formally certified as locally robust by state-of-the-art
complete and incomplete verifiers could be systematically broken on real
hardware.

**Technical root cause:**

1. **Real-arithmetic ($\mathbb{R}$) vs. IEEE-754 (`binary32` / `binary64`)
   semantics:** Complete verifiers based on Mixed-Integer Linear Programming
   (`MIPVerify` using Gurobi/CPLEX) or SMT (`Reluplex` / `Marabou`) encode a
   piecewise-linear network $f : \mathbb{R}^n \to \mathbb{R}^k$ as linear
   constraints over mathematical reals $\mathbb{R}$:
   $$\hat{z}^{(l)}_i = \sum_{j=1}^{m_{l-1}} W^{(l)}_{i,j} z^{(l-1)}_j + b^{(l)}_i, \quad z^{(l)}_i = \max(0, \hat{z}^{(l)}_i)$$
   However, actual deployment (PyTorch, TensorFlow, ONNX Runtime) evaluates
   $\hat{z}^{(l)}_i$ using IEEE-754 `float32` Fused Multiply-Add (`FMA`) or
   tree-reduced SIMD/GPU dot products, where every addition and multiplication
   incurs rounding error $\text{fl}(a \circ b) = (a \circ b)(1 + \delta)$ with
   $|\delta| \le u = 2^{-24} \approx 5.96 \times 10^{-8}$, and where floating-point
   addition is **non-associative** ($(a \oplus b) \oplus c \neq a \oplus (b \oplus c)$).
2. **Exploiting complete verifiers via solver-tolerance and rounding gaps:**
   MILP and LP solvers internally use `float64` arithmetic with primal
   feasibility tolerances $\epsilon_{\text{feas}} \in [10^{-9}, 10^{-6}]$ and
   integrality tolerances $\epsilon_{\text{int}} \approx 10^{-5}$. Jia and
   Rinard crafted a targeted search algorithm that perturbs input coordinates by
   single Units in the Last Place (`1 ULP`) to maximize the divergence between
   the LP solver's `float64` relaxation and the runtime's `float32` inference,
   producing concrete adversarial examples inside $\ell_\infty$-balls that
   `MIPVerify` had certified as $100\%$ robust (`UNSAT`).
3. **Exploiting incomplete abstract-interpretation verifiers (`ERAN` / `DeepZ` /
   `DeepPoly`):** Even when an abstract interpreter uses directed IEEE-754
   hardware rounding modes (`FE_DOWNWARD` for lower bounds, `FE_UPWARD` for
   upper bounds) during bound propagation, if the verifier's abstract
   transformers assume exact real identities—such as distributive cancellation
   $a(x + y) - ax - ay = 0$ or exact `ReLU` chord slopes without widening the
   affine coefficients by floating-point representation error—an attacker can
   construct networks with ill-conditioned weight ratios where concrete
   `float32` activations escape the computed abstract zonotope or polyhedron.

Basis: **normative** IEEE-754 floating-point semantics + **documentation** and
**execution** results reported in Jia and Rinard (SAS 2021, `arXiv:2003.03021`).

#### 2.2 `VNN-COMP` 2021–2024 soundness disqualifications and false-`UNSAT` penalties

The International Verification of Neural Networks Competition (`VNN-COMP`
2021–2024; `arXiv:2109.00498`, `arXiv:2212.10376`, `arXiv:2312.16760`,
`arXiv:2412.19985`) evaluates verifiers on standardized `ONNX` networks and
`VNN-LIB` input-output property specifications. Across all four competition
editions, multiple verifiers returned **unsound `UNSAT` (`holds`) verdicts on
benchmarks where another participant or adversarial attack produced a verified
concrete counterexample (`SAT` / `violated`)**:

- **`CGDTest` (VNN-COMP 2022, `arXiv:2212.10376`):** `CGDTest` (Constraint
  Gradient Descent Test) returned false `UNSAT` verdicts on multiple instances
  of the `collins-rul-cnn` and `sri_resnet_a`/`sri_resnet_b` benchmarks where
  concrete counterexamples existed, incurring heavy soundness penalty deductions
  (which drove its category scores negative under VNN-COMP's $-100$-point-per-mismatch
  scoring rule).
- **`VeriNet` and `Marabou` LP/Simplex tolerance mismatches (VNN-COMP
  2021–2023):** Both `Marabou` (Reluplex-based SMT solver) and `VeriNet`
  (symbolic-interval propagation with LP splitting) experienced soundness
  mismatches on deep or high-condition-number networks (`oval21`, `cifar2020`,
  `acasxu`, `vggnet16`) caused by floating-point instability in the underlying
  Simplex/Gurobi basis inversions and tightened split bounds where an active/inactive
  `ReLU` phase was misclassified as infeasible due to solver tolerance thresholds
  ($10^{-6}$).
- **`NNV` (Neural Network Verification tool in MATLAB, VNN-COMP 2021–2023):**
  Exhibited soundness discrepancies on convolutional and residual benchmarks due
  to Star-set (`Star` / `ImageStar`) LP bound-tightening numerical precision
  drift and mismatches in how MATLAB's deep learning importer parsed ONNX
  padding, flattening (`C`-order row-major vs. Fortran column-major), and
  `BatchNormalization` folding constants.
- **`α,β-CROWN` (`auto_LiRPA`) GPU floating-point and ONNX operator pitfalls
  (VNN-COMP 2021–2024):** Although `α,β-CROWN` placed first overall in
  2021–2024, competition analyses documented three classes of soundness hazards
  that required explicit architectural mitigations:
  1. **GPU `float32` reduction non-associativity:** Linear bound propagation
     (`CROWN`) on CUDA GPUs uses parallel warp reductions whose rounding behavior
     is non-deterministic and unrounded relative to directed-rounding interval
     arithmetic (`float64` with upward/downward rounding). On networks with
     large alternating-sign weights, `float32` bound propagation can underestimate
     upper bounds or overestimate lower bounds unless sound `float64` interval
     widening is enabled.
  2. **ONNX operator semantic ambiguity (`Reshape`, `Transpose`, `Resize`,
     `BatchNorm`):** As highlighted by Brix et al. (`arXiv:2312.16760`,
     `arXiv:2412.19985`) and Cordeiro et al. (ESOP 2025, *Neural Network
     Verification is a Programming Language Challenge*), verifiers frequently
     translated ONNX operators into internal PyTorch tensors using subtly
     different axis ordering or broadcast semantics than `ONNX Runtime`, causing
     a verifier to prove safety of a **different function** than the one
     actually executed by the reference runtime.
  3. **Counterexample validation mismatches:** A point $x_{\text{ce}}$ declared
     as a valid `SAT` counterexample by a verifier in `float64` sometimes failed
     verification when re-evaluated by the competition's `ONNX Runtime` `float32`
     harness because $x_{\text{ce}}$ lay within $10^{-7}$ of the decision
     boundary. Consequently, VNN-COMP increased the penalty for an incorrect
     verdict to $-150$ points and mandated bit-exact witness files validated
     directly against `ONNX Runtime`.

Basis: **documentation** and **execution** benchmark records from VNN-COMP
2021–2024 (`arXiv:2109.00498`, `arXiv:2212.10376`, `arXiv:2312.16760`,
`arXiv:2412.19985`).

#### 2.3 Architectural lessons for Anneal's 4 `trusted/` primitives from neural verification

1. **`Language SemObs` and `Partial` must anchor to concrete machine execution,
   never idealized $\mathbb{R}$:** Jia and Rinard's attack works because the
   verifier's `Language` (`RealNNLang`) is not the runtime's `Language`
   (`Float32NNLang` or `MirLang` over IEEE-754 `Float32` / quantized `BitVec`).
   In Anneal, `Trusted` semantics must define `Prog` over the exact machine
   representations executed at runtime, modeling `NaN`/`Inf` overflow and
   robustness margin violations as `Partial.ub` (`defined = False`).
2. **`Abstracts` (`codec.toMorphism`) requires sound rounding widening:** When a
   symbolic polytope or zonotope verifier (`PolytopeLang`) over-approximates a
   concrete network (`NNLang`) via `Abstracts PolytopeLang NNLang codec absNet
   concNet`, the Lean proof obligation `NNLang.sem concNet ≤ codec.toMorphism
   (PolytopeLang.sem absNet)` cannot be discharged inside the Lean kernel unless
   every affine relaxation step explicitly accounts for IEEE-754 rounding error
   bounds (or checks rational Farkas dual multipliers $\alpha, \beta \in
   \mathbb{Q}$ that upper-bound the rounded concrete operations). An unverified
   GPU `float32` bound propagator can compute candidate dual multipliers
   out-of-line, but the Lean kernel in `theory/` checks their soundness via
   exact rational or interval arithmetic.
3. **`ProductiveOn` and `InhabitedPre` block vacuous Branch-and-Bound (`BaB`)
   splits:** In $\alpha,\beta$-CROWN or `Marabou`, splitting a `ReLU` neuron into
   active ($\hat{z}_i \ge 0$) and inactive ($\hat{z}_i < 0$) branches partitions
   the query precondition `pre`. If an external solver emits an inconsistent
   split tree whose leaf preconditions have an empty intersection or omit part
   of the input ball, `InhabitedPre` and partitioning lemmas over `ProductiveOn`
   fail to typecheck in Lean, preventing vacuous `False.elim` proofs on
   uninhabited sub-regions.
4. **`VerificationResult` isolates solver-dependent waivers:** If a user chooses
   to trust an external LP/MILP oracle on specific boundary anchors rather than
   providing a kernel-checked Farkas dual certificate, that trust assumption
   must appear as a positive obligation identifier in `waived` under
   `VerificationResult`, never as a hidden `10^-6` tolerance inside `trusted/`.

---

### 3. Agentic guardrail bypasses and over-refusal vacuity (`NeMo Guardrails`, `LlamaGuard`, `CaMeL`, `XSTest`, and `OR-Bench`)

#### 3.1 Indirect prompt injection bypasses of probabilistic and dialog-rail guardrails

Autonomous LLM agents that invoke external tools (via Model Context Protocol /
MCP, shell commands, SQL clients, or web browsers) rely on runtime guardrails
such as NVIDIA's `NeMo Guardrails` (Colang dialog/retrieval/execution rails) and
Meta's `LlamaGuard` / `Prompt Guard` classifiers to intercept unsafe actions.
Empirical evaluations across `InjecAgent` (Zhan et al., `arXiv:2403.02691`) and
`AgentDojo` (Debenedetti et al., NeurIPS 2024, `arXiv:2406.13352`) demonstrate
that probabilistic and pattern-based guardrails are systematically bypassed by
**indirect prompt injections** embedded inside untrusted external data retrieved
during execution (such as incoming emails, calendar invites, web pages, or RAG
documents):

1. **Role-boundary flattening and context confusion:** When an orchestrator
   concatenates untrusted tool outputs into the LLM's context window or passes a
   flattened transcript to a `LlamaGuard` / `NeMo` moderation judge, injected
   strings that mimic system delimiters, JSON tool-call schemas, or benign task
   completions hijack the planner LLM's control flow—for example, instructing an
   email assistant to read a confidential API key and exfiltrate it via an
   external HTTP `GET` or `send_email` call.
2. **Multi-step payload splitting and semantic judge subversion:** Because
   classifier guardrails (`LlamaGuard`, `NeMo` input/output self-check rails)
   are themselves neural networks or regex/embedding matchers without
   data-provenance tracking, an indirect injection can split an exfiltration or
   destructive action across multiple individually benign-looking tool calls, or
   embed adversarial instructions aimed at convincing the guardrail judge LLM
   itself that the tool invocation was explicitly authorized by the user.
3. **Architectural mitigation via `CaMeL` (`arXiv:2503.18813`):** Debenedetti et
   al. (*Defeating Prompt Injections by Design*, 2025, `arXiv:2503.18813`) show
   that defeating indirect prompt injection requires abandoning probabilistic
   text classification in favor of **capability-based security and strict
   control/data-flow separation** (`CaMeL`): a privileged LLM generates an
   explicit control-flow program from the trusted user prompt alone, while a
   quarantined LLM parses untrusted external data without any capability to
   alter control flow or invoke tools, and a deterministic interpreter enforces
   information-flow taint labels (`capabilities`) before every external tool
   execution.

Basis: **documentation** and **execution** benchmark results from `InjecAgent`
(`arXiv:2403.02691`), `AgentDojo` (`arXiv:2406.13352`), and `CaMeL`
(`arXiv:2503.18813`).

#### 3.2 Over-refusal vacuity (`XSTest` and `OR-Bench`)

Conversely, when operators tighten heuristic guardrails (`NeMo Guardrails`
topical/moderation rails, `LlamaGuard` threshold tuning, or static keyword
sandboxes) to reduce indirect prompt injection false negatives, they trigger
severe **over-refusal (false-positive rejection)** on benign user tasks:

- **`XSTest` (Röttger et al., NAACL 2024, `arXiv:2308.01263`):** Evaluates models
  and guardrails on 250 safe prompts across 10 categories (homonyms, figurative
  language, safe targets, historical/privacy contexts—for example, *"How do I
  kill a Python background process?"* or *"Where can I shoot a photo of the
  capitol?"*) paired with 200 unsafe contrasts. Overly aggressive safety rails
  latch onto lexical triggers (`kill`, `shoot`, `execute`, `hack`) and reject a
  large fraction of completely benign developer and knowledge workflows.
- **`OR-Bench` (Cui et al., ICML 2024, `arXiv:2405.20947`):** Scales over-refusal
  evaluation to 80,000 seemingly toxic but benign prompts, showing a stark
  Pareto frontier collapse: heuristic guardrails that achieve high rejection of
  adversarial prompts routinely refuse $30\%$–$80\%+$ of benign borderline
  workflows, and overly restrictive capability sandboxes that forbid external
  tool composition can block $100\%$ of legitimate multi-step agent tasks.

Basis: **documentation** and **execution** evaluations in `XSTest`
(`arXiv:2308.01263`) and `OR-Bench` (`arXiv:2405.20947`).

#### 3.3 Architectural lessons for Anneal's 4 `trusted/` primitives from agentic AI safety

1. **`StepResult.externalCall boundaryInv branches` captures the exact `CaMeL`
   reference-monitor boundary:** In Anneal's small-step machine model, an agent
   orchestrator invoking an external MCP tool or querying an untrusted LLM/web
   source transitions via `StepResult.externalCall boundaryInv branches`:
   - `boundaryInv : Bool` is the deterministic, kernel-verified capability and
     Information-Flow Control (`IFC`) taint check (`checkCapability(cap, tool,
     args) && checkNoTaintExfil(taintMap, tool, args)`). If `boundaryInv =
     false`, the step transitions immediately to `.failed .ub` (`defined =
     False`).
   - `branches : State → Prop` is a **demonic choice over all possible untrusted
     LLM token completions and adversarial tool responses**. Because `defined`
     must hold across *all* states in `branches`, proving `defined` for an
     orchestrator proves that **no indirect prompt injection payload returned by
     an external tool or proposed by an untrusted LLM can ever cause an
     unauthorized tool invocation**.
2. **`ProductiveOn` and `InhabitedPre` mathematically forbid the "Paranoid Brick
   Firewall" over-refusal loophole:** An AI safety shield that rejects $100\%$
   of user requests or blocks every tool call trivially satisfies `defined`
   (zero unsafe tool calls occur), which is the formal equivalent of $100\%$
   over-refusal on `XSTest`/`OR-Bench`. Requiring both safety (`Compiles` /
   `defined`) *and* `InhabitedPre SafeBenignQueries` + `ProductiveOn
   SafeBenignQueries proxy` forces the guardrail designer to prove that for
   every authorized benign workflow in `SafeBenignQueries`, there exists at
   least one terminating execution path that completes the user's task without
   triggering `.policyDenied` or `.ub`.
3. **`VerificationResult` isolates heuristic classifiers from deterministic IFC
   theorems:** When a deployment combines a deterministic `CaMeL`-style
   capability monitor with an unverified neural classifier (such as `LlamaGuard`
   for PII detection), `VerificationResult` keeps the deterministic capability
   isolation proof unwaived (`ob.prop`) while isolating any assumption about the
   neural classifier's accuracy as an explicit waiver ID (`ob.id ∈ waived`).

---

### 4. Automated planning validator bugs (`VAL` vs. Isabelle/HOL `INVAL`)

#### 4.1 Abdulaziz and Lammich (ICTAI 2018): Unsoundness and incompleteness in the IPC reference validator `VAL`

In automated planning (`STRIPS` and `PDDL`), heuristic search planners (such as
`Fast Downward`, `LPG`, `Metric-FF`, or modern neuro-symbolic LLM planners) are
complex and unverified; the planning community therefore relies on an
independent plan validator to check whether a synthesized plan $\pi = \langle
a_1, a_2, \dots, a_k \rangle$ validly transforms the initial world state $s_0$
into a goal state $s_k \supseteq G$. For over fifteen years, the C++ validator
**`VAL`** (Howey, Long, and Fox, ICTAI 2004) served as the official reference
validator for the International Planning Competition (`IPC`), alongside the Lisp
validator **`INVAL`** (Haslum).

In *A Formally Verified Validator for Classical Planning Problems and Solutions*
(ICTAI 2018, `arXiv:1807.09726`, DOI `10.1109/ICTAI.2018.00079`), Mohammad
Abdulaziz and Peter Lammich formalized the semantics of PDDL (STRIPS with typing,
equality, negation, and disjunctive/implicative preconditions) in **Isabelle/HOL**,
extracted a verified executable validator via the Isabelle Refinement Framework,
and differential-tested `VAL` and `INVAL` against it across IPC benchmark
domains. They discovered that **both `VAL` and `INVAL` were simultaneously
unsound (accepting invalid plans and ill-formed domains) and incomplete
(rejecting or crashing with segmentation faults on valid plans)**:

1. **Simultaneous micro-step effect ordering (`delete`-before-`add` vs.
   `add`-before-`delete`):** In standard PDDL/STRIPS semantics (McDermott et
   al., 1998; Fox and Long, JAIR 2003, DOI `10.1613/jair.1129`), an action $a$'s
   atomic state transition updates a world state $s$ by applying negative effects
   (`del(a)`) *before* positive effects (`add(a)`):
   $$\text{execute}(s, a) = (s \setminus \text{del}(a)) \cup \text{add}(a)$$
   Consequently, if an action's grounded effect list contains both $\neg p$ and
   $p$ (which arises frequently when schematic action parameters $\text{move}(?x,
   ?from, ?to)$ are instantiated with aliased arguments $?from = ?to$, so
   $\neg \text{at}(?x, ?from)$ and $\text{at}(?x, ?to)$ refer to the same atom
   $p$), $p$ must hold in the successor state $s'$. Unverified validators and
   planners that apply positive effects before negative effects
   ($(s \cup \text{add}(a)) \setminus \text{del}(a)$), or that iterate over
   clause AST nodes in syntactic declaration order, compute the wrong successor
   state $s'$, allowing subsequent actions with precondition $p$ (or $\neg p$)
   to be unsoundly accepted or falsely rejected.
2. **Type-hierarchy, schematic equality, and ungrounded object bugs in `VAL`:**
   Abdulaziz and Lammich found that `VAL` accepted PDDL plans that referenced
   undeclared objects, violated `(:types ...)` subtype declarations when `object`
   root supertypes were omitted or circularly declared, and mishandled duplicate
   parameter declarations in action schemas—accepting plans that were invalid
   under the PDDL specification, while crashing with a segmentation fault on
   syntactically valid disjunctive preconditions.
3. **Temporal / durative PDDL 2.1 boundary tolerances and concurrent mutexes:**
   In PDDL 2.1 durative plans (Howey, Long, and Fox, ICTAI 2004), concurrent
   actions scheduled at timestamps $t_1, t_2$ must satisfy the **no-moving-target**
   and **$\epsilon$-separation mutex rules** across `at start`, `over all`, and
   `at end` intervals (open vs. closed interval endpoints $[t_{\text{start}},
   t_{\text{end}}]$) as well as continuous linear/differential numeric fluent
   updates (`#t`). Floating-point timestamp comparisons ($|t_1 - t_2| < \epsilon$)
   and order-dependent evaluation of simultaneous `at start`/`at end` effects at
   the same instant $t$ have historically caused `VAL` to accept plans with
   race-condition mutex violations depending on the order in which actions were
   listed in the plan file.

Basis: **normative** PDDL 2.1 specification (Fox and Long, JAIR 2003, DOI
`10.1613/jair.1129`) + **source** and **execution** findings in Abdulaziz and
Lammich (ICTAI 2018, `arXiv:1807.09726`).

#### 4.2 Architectural lessons for Anneal's 4 `trusted/` primitives from automated planning

1. **The plan validator *is* the TCB, so operational semantics must be kernel-checked:**
   The `VAL` postmortem proves that "propose with an untrusted heuristic/LLM,
   check with a standalone C++ validator" fails if the validator itself is
   unverified C++ code. In Anneal, `Language SemObs` and `Partial` define the
   reference operational semantics inside the Lean 4 kernel: an unsatisfied
   action precondition or concurrent mutex clash is `Partial.ub` (`defined =
   False`), and the atomic state update $s' = (s \setminus \text{del}(a)) \cup
   \text{add}(a)$ is a pure mathematical definition whose properties are checked
   by Lean's kernel.
2. **`Compiles` and `EventualBehaviorOf` natively verify $1 \to k$ Hierarchical
   Task Network (`HTN`) decomposition:** Lowering a high-level compound task in
   `HTNLang` (1 abstract step) into a 50-step primitive `PDDLLang` action
   schedule is an instance of `Compiles HTNLang PDDLLang codec compoundTask
   primitivePlan`. Because `EventualBehaviorOf` abstracts away the number of
   internal small steps $k$ while enforcing `defined` (precondition and
   trajectory invariant satisfaction) at every intermediate micro-step $0 \le j
   \le k$, Anneal verifies variable-length task decompositions without artificial
   stuttering steps.
3. **`StepResult.externalCall` captures FOND (Fully Observable Non-Deterministic)
   contingent planning:** When an action in the physical world has uncertain
   outcomes (e.g., `grasp_object` may succeed or slip), `boundaryInv` checks the
   action's preconditions and `branches` models all nondeterministic environment
   post-states, requiring a verified contingent plan to maintain safety across
   all branches.

---

### 5. CAD/CSG non-manifold failures, CNC G-code crashes, textile compiler bugs, and structural FEA collapses

#### 5.1 `OpenSCAD`/`CGAL` non-manifold boolean failures motivating `Manifold` (`elalish/manifold`) and `Fidget` (`mkeeter/fidget`)

For over a decade, parametric solid modeling in `OpenSCAD` relied on the
Computational Geometry Algorithms Library (`CGAL`, specifically 3D Nef
polyhedra `CGAL::Nef_polyhedron_3` over exact rational `GMP` kernels) to evaluate
Constructive Solid Geometry (`CSG`) boolean operations ($\cup, \cap, \setminus$).
Despite `CGAL`'s use of exact rational arithmetic internally, real-world CSG
pipelines repeatedly failed with cryptic `CGAL_Nef_polyhedron` assertion
aborts, multi-hour hangs, or unprintable **non-manifold STL meshes**:

1. **The exact-to-floating-point "snap rounding" catastrophe:** When a boundary
   representation (`B-Rep`) or triangle mesh is exported to `STL`/`3MF` or
   passed between stages, exact rational vertex coordinates $(x, y, z) \in
   \mathbb{Q}^3$ are rounded to 32-bit or 64-bit IEEE-754 floats. Rounding two
   nearly coincident vertices or a vertex near a triangle face causes faces to
   pass through one another (**self-intersection**), collapses triangle areas to
   zero (**degenerate slivers**), or merges disconnected surface sheets at a
   single vertex or edge shared by four triangles (**pinched / non-manifold
   topology**). Once a mesh ceases to be a closed 2-manifold, inside/outside
   generalized winding numbers become ill-defined, causing subsequent boolean
   operations or 3D-printer slicers (`PrusaSlicer`, `Cura`) to drop entire solid
   layers or fail outright.
2. **Emmett Lalish's `Manifold` (`elalish/manifold`) topological invariant:**
   To eliminate this failure mode, `elalish/manifold` (integrated into OpenSCAD
   as its high-performance backend) separates **topological manifoldness** from
   floating-point vertex coordinates: it treats the half-edge mesh connectivity
   (every directed edge has an exact reverse pair; every vertex link is a single
   closed cycle) as the primary exact invariant and uses symbolic perturbation
   and edge-collapse decimation that *provably preserves the 2-manifold
   invariant* under floating-point coordinate rounding, achieving $100\times$–$1000\times$
   speedups over `CGAL` while guaranteeing watertight output.
3. **Matt Keeter's `Fidget` (`mkeeter/fidget`) interval/affine implicit CSG:**
   An orthogonal solution pioneered by Keeter (`libfive`, `Antimony`, `Fidget`)
   abandons fragile B-Rep triangle boolean intersections entirely, representing
   CSG solids as **implicit Signed Distance Field (`SDF`) / Functional
   Representation (`F-Rep`) trees** $f : \mathbb{R}^3 \to \mathbb{R}$ evaluated
   via **Interval Arithmetic (`IA`) and Affine Arithmetic (`AA`)** over spatial
   octrees/quadtrees. If the interval evaluation $F([x_{\min}, x_{\max}] \times
   [y_{\min}, y_{\max}] \times [z_{\min}, z_{\max}])$ is strictly positive
   ($> 0$, empty air) or strictly negative ($< 0$, solid interior), the entire
   spatial cell is pruned soundly without mesh intersection.

Basis: **source** and **documentation** of `elalish/manifold`, `OpenSCAD`, and
`mkeeter/fidget`.

#### 5.2 CNC rapid-traverse (`G00`) dogleg collision crashes

In 3-axis and 5-axis CNC milling (`ISO 6983` / RS-274D G-code), `G01 Xx Yy Zz Ff`
commands a **linearly interpolated cutting move** where all axes are
synchronized to follow the exact straight line segment from $\mathbf{p}_0$ to
$\mathbf{p}_1$. By contrast, `G00 Xx Yy Zz` commands a **non-cutting rapid
positioning traverse**.

A notorious cause of catastrophic physical CNC spindle crashes is the **`G00`
dogleg (non-linear rapid) semantic mismatch**:

- **The physical controller behavior:** On standard industrial CNC controllers
  (Fanuc, Haas, Siemens, Mazak when non-linear rapid parameter `NLR` is active),
  `G00` does **not** interpolate a straight line in $\mathbb{R}^3$. Instead, the
  controller commands each axis motor ($X, Y, Z$) independently at its maximum
  rapid velocity $v_{\max,i}$. If the tool moves from $(0, 0, 50)$ to $(100, 20,
  50)$ with $v_{\max,X} = v_{\max,Y}$, the $Y$-axis reaches $Y = 20$ at $X = 20$
  (traveling at a $45^\circ$ diagonal) and then travels parallel to the $X$-axis
  from $(20, 20, 50)$ to $(100, 20, 50)$—forming a bent **"dogleg" trajectory**.
  Even worse, on a combined $XY+Z$ rapid retract or plunge, if the $Z$-axis has
  a slower rapid rate or longer travel than $X/Y$, the tool sweeps horizontally
  before clearing the workpiece height!
- **The CAM simulator failure:** Unverified CAM toolpath visualizers and naive
  collision checkers model `G00` as a straight line segment $\overline{\mathbf{p}_0
  \mathbf{p}_1}$ identical to `G01`. When a fixture clamp or tall boss lies
  outside the straight chord $\overline{\mathbf{p}_0 \mathbf{p}_1}$ but *inside*
  the dogleg corner envelope, the CAM simulation reports **zero collisions**,
  and the physical CNC spindle crashes at $30\text{ m/min}$ into the steel clamp.

Basis: **normative** ISO 6983 / controller rapid-traverse semantics +
**documentation** of CAM/CNC dogleg collision failure modes.

#### 5.3 `Knitout` and `Autoknit` yarn-tension breakages and dropped-stitch unraveling

In computational machine knitting (`Knitout` by McCann et al., SIGGRAPH 2016,
DOI `10.1145/2897824.2925940`; `Autoknit` by Narayanan et al., SIGGRAPH 2018,
DOI `10.1145/3197517.3201335`), a 3D mesh is compiled into low-level needle
instructions (`knit`, `tuck`, `split`, `xfer`, `rack`, `miss`) for industrial
V-bed knitting machines (Shima Seiki, Stoll). Postmortems of automated knitting
compilers identify three physical/topological failure modes when lowering stitch
graphs to needle schedules:

1. **Over-racking yarn snap and needle bending:** When two adjacent stitches in
   a course are held on opposing needle beds (one on the front bed $f_i$, one on
   the back bed $b_j$) and the compiler emits a `rack R` instruction (shifting
   the back bed horizontally by $R$ needle pitches to align other needles for a
   transfer), if the horizontal offset $|i - (j + R)|$ exceeds the yarn's
   elastic stretch limit (typically $> 2$ needle pitches), the interconnecting
   yarn sinker loop is stretched beyond its breaking tension—**snapping the yarn
   or bending steel latch needles**.
2. **Transfer slider collision and loop-stacking overflow:** Attempting to
   transfer (`xfer`) onto a needle that already holds too many loops, or moving
   a yarn carrier across an active needle without clearing the latch, causes a
   mechanical carriage jam.
3. **Dropped live stitches (`UnsecuredLiveLoop`):** If a compiler schedule
   allocates a needle for a temporary transfer (`collapse`/`expand` passes in
   `Autoknit`) and overwrites or drops a live loop without transferring it to a
   neighboring needle or binding it off, the physical fabric develops a
   topological run and unravels under tension.

Basis: **documentation** and **source** of `Knitout` (DOI
`10.1145/2897824.2925940`) and `Autoknit` (DOI `10.1145/3197517.3201335`).

#### 5.4 Civil and structural FEA collapses: Hartford Civic Center (1978) and Sleipner A (1991)

Two landmark structural engineering disasters demonstrate how unverified
abstractions and unchecked discretization errors in computer-aided engineering
cause catastrophic physical failure:

- **Hartford Civic Center Coliseum space-frame roof collapse (January 18,
  1978):** At 4:15 AM under a wet snow/ice load of approximately $73\text{
  kg/m}^2$ ($15\text{ psf}$, well below the $30\text{ psf}$ design live load),
  the $360 \times 300\text{ ft}$ steel space-truss roof collapsed completely.
  The forensic investigation by Lev Zetlin Associates revealed that the
  engineers had relied heavily on an early linear computer frame analysis that
  modeled the top-chord compression struts as ideally braced, pin-connected bar
  elements. In the actual design:
  1. The top chords were fabricated from **four steel angles in a cruciform
     cross-section** (which has an extremely low torsional and flexural radius
     of gyration);
  2. Rather than intersecting at true truss nodes, diagonal bracing members
     connected to gusset plates **eccentrically offset below the top chord work
     points**, introducing unmodeled secondary bending moments and leaving the
     $30\text{ ft}$ top chords effectively unbraced at their midpoints ($KL/r$
     far higher than modeled); and
  3. When measured downward deflections during erection were **twice as large**
     as the computer model predicted, the engineers trusted the idealized
     computer model over the physical measurements.
- **Sleipner A Condeep offshore gravity-base platform sinking (August 23,
  1991):** During a controlled ballast test in Gandsfjorden near Stavanger,
  Norway, the concrete base structure consisting of 24 cylindrical buoyancy
  cells cracked at a depth of $65\text{ m}$ and sank in $220\text{ m}$ of water
  (a $\$700\text{M}$ total loss accompanied by a $M_L = 3.0$ seismic event). The
  SINTEF and Det Norske Veritas (`DNV`) inquiry established that the global
  Finite Element Analysis (`FEA`) executed in **`NASTRAN`** contained a fatal
  discretization error at the **tricell walls** (the triangular water-filled
  interstices between three adjacent cylindrical cells):
  1. The global `NASTRAN` model used a coarse mesh of **8-node linear hexahedral
     solid elements with skewed (non-orthogonal, trapezoidal) aspect ratios** at
     the tricell wall junctions;
  2. Skewed low-order solid elements suffer from parasitic shear locking and
     inaccurate stress recovery when only integration-point averages are read
     without checking element nodal force equilibrium;
  3. As a result, `NASTRAN` **underestimated the shear stress in the tricell
     walls by $47\%$**, leading engineers to omit T-headed shear stirrup
     reinforcement across the junction. Under $65\text{ m}$ hydrostatic head,
     the unreinforced concrete wall failed in shear within minutes.

Basis: **documentation** from the Lev Zetlin Associates Hartford forensic report
(1978) and the SINTEF / Det Norske Veritas Sleipner A inquiry reports
(1991–1992).

#### 5.5 Architectural lessons for Anneal's 4 `trusted/` primitives from CAD/CAM and structural engineering

1. **`Abstracts` must over-approximate the *true* physical envelope, never an
   under-approximated point sample:** Both the CNC `G00` dogleg crash and the
   Sleipner A $47\%$ shear underestimation happened because a simulator or FEA
   model substituted an optimistic point/line approximation for a conservative
   outer envelope. In Anneal, `Abstracts AbstractLang ConcreteLang codec absProg
   concProg` requires `ConcreteLang.sem concProg ≤ codec.toMorphism
   (AbstractLang.sem absProg)`. For a CNC verifier, `absProg` must bound the
   entire swept bounding box of all non-deterministic per-axis `G00` velocity
   ratios; for a structural or SDF verifier (`Fidget`-style), `absProg` must use
   conservative Interval Finite Element Analysis (`IFEM`) or affine arithmetic
   that *upper-bounds* internal stresses and *lower-bounds* buckling capacities
   (including eccentric connection moments as in Hartford).
2. **`BehaviorCodec.decodeOut = none` enforces topological and mesh
   well-formedness invariants:**
   - In CAD/CSG (`elalish/manifold`), any mesh state with a non-manifold edge,
     self-intersection, or mismatched half-edge pair maps to `decodeOut = none`
     (forcing `Compiles` to fail unless the boolean kernel preserves the
     2-manifold invariant).
   - In machine knitting (`Knitout`), any final needle-bed state that leaves
     un-cast-off live loops stranded on the needles maps to `decodeOut = none`.
   - In FEA (`Sleipner A`), any finite-element stress solution that violates
     inter-element nodal force equilibrium ($\|K u - F\| > \tau_{\text{eq}}$) or
     mesh Jacobian skewness bounds maps to `decodeOut = none` instead of silently
     under-reporting shear by $47\%$.
3. **`EventualBehaviorOf` and `ProductiveOn` bridge $1 \to 50{,}000$ geometric
   lowering while blocking "air-cutting" and "windowless bunker" Goodhart
   loopholes:** Lowering a declarative CSG solid (1 node) to 50,000 G-code
   micro-segments is verified via `EventualBehaviorOf`, which checks collision
   and overhang safety (`defined = True`) at all 50,000 micro-steps and checks
   manufactured voxel tolerance (`obs_decodeOut`) at termination. Meanwhile,
   `ProductiveOn` blocks an agent from emitting `M30` (an immediate halt that
   cuts zero metal and therefore never crashes) or generating a building with
   zero doors to vacuously satisfy door-width rules.

---

### 6. Shader compilers, font hinting bytecode, UI constraint layout, audio DSP, and smart-home IoT rule failures

#### 6.1 WebGPU/Vulkan/WebGL shader compiler OOB and uniformity escapes (`GraphicsFuzz`, `Dawn`/`Tint`, and `Naga`)

GPU shader pipelines compile untrusted high-level shader source (`GLSL`, `HLSL`,
`WGSL`) or intermediate bytecode (`SPIR-V`, `DXIL`, `MSL`) directly into vendor
GPU machine code inside browser and OS graphics processes.

1. **`GraphicsFuzz` (Donaldson et al., OOPSLA 2017, DOI `10.1145/3133917`):**
   Using metamorphic testing—injecting dead-by-construction control-flow
   branches, loop-unrolling identities, and opaque constant predicates into
   reference shaders—Donaldson et al. discovered dozens of critical
   miscompilations, out-of-bounds memory accesses, and GPU Timeout Detection and
   Recovery (`TDR`) driver resets across **every major GPU vendor** (AMD, ARM
   Mali, Apple, Intel, NVIDIA, and Qualcomm Adreno). Aggressive driver-level
   optimizations (dead-code elimination, loop vectorization, instruction
   scheduling across divergent warps/subgroups) unsoundly reordered barrier
   synchronizations or corrupted live registers when control flow diverged across
   threads in a warp.
2. **WebGPU `Dawn`/`Tint` and `wgpu`/`Naga` uniformity and bounds-clamping
   escapes (2023–2024):** To prevent the shader bugs uncovered by `GraphicsFuzz`,
   the W3C WebGPU (`WGSL`) specification mandates two static/transformation
   safeguards inside `Tint` (Chromium) and `Naga` (Firefox):
   - **Static Uniformity Analysis:** Collective operations (`workgroupBarrier()`,
     `storageBarrier()`, and implicit quad-derivative texture lookups like
     `textureSample()`) must only be executed in **uniform control flow** (where
     all invocations in a workgroup or derivative quad take the same branch).
     Bugs in uniformity dataflow graphs allow non-uniform values (tainted by
     `builtin(local_invocation_index)` or storage buffer reads) to reach barriers,
     triggering hardware warp deadlocks or undefined cross-lane derivative reads.
   - **Robustness Bounds-Clamping Transforms:** `Tint` and `Naga` rewrite array
     and buffer indexing expressions `buf[i]` into `buf[min(u32(i),
     arrayLength(&buf) - 1u)]` to guarantee memory safety on the GPU. However,
     fuzzing campaigns (including `WGSLsmith` and `DarthShader`, 2023–2024) and
     Chromium security audits uncovered high-severity vulnerabilities where
     signed/unsigned integer overflow during index offset calculation, zero-sized
     binding edge cases, or backend lowering discrepancies (translating `WGSL`
     $\to$ `SPIR-V` / `HLSL` / `DXC` / `MSL`) bypassed the robustness clamp or
     triggered heap buffer overflows in the shader translator itself.

Basis: **normative** W3C WGSL Uniformity Specification + **documentation** and
**execution** findings in Donaldson et al. (OOPSLA 2017, DOI `10.1145/3133917`)
and WebGPU `Dawn`/`Tint`/`Naga` security advisories.

#### 6.2 `FreeType` and Windows `ATMFD.dll` TrueType bytecode hinting and font parsing CVEs (`CVE-2015-2426` and `CVE-2020-15999`)

Every TrueType (`.ttf`) and OpenType (`.otf`) font file contains executable,
Turing-complete stack-based bytecode programs (`fpgm` font program, `prep`
control-value program, and per-glyph `glyf` hinting instructions) that manipulate
glyph outline control points, a Control Value Table (`CVT`), a scratchpad
Storage Area, and a temporary **Twilight Zone (`zp0`/`zp1`/`zp2`)** of virtual
points to snap glyph stems to low-resolution pixel grids:

- **`CVE-2015-2426` (Windows Kernel `ATMFD.dll` OpenType/TrueType memory
  corruption exploited in the wild):** Disclosed in the July 2015 Hacking Team
  zero-day leaks, `CVE-2015-2426` was a critical buffer underflow / out-of-bounds
  memory corruption in the Windows Adobe Type Manager Font Driver (`ATMFD.dll`,
  which ran in ring-0 kernel mode). By crafting malformed font table offsets and
  bytecode hinting state transitions, an attacker achieved direct ring-0 kernel
  Remote Code Execution (`RCE`) from a sandboxed browser or document viewer.
  Related TrueType bytecode interpreter bugs across `ATMFD.dll` and `FreeType`
  (such as `CVE-2014-9660`, `CVE-2015-9381`, and `CVE-2010-3855`) exploited
  uninitialized Twilight Zone pointers (`SHZ`, `SHP`, `MDAP`, `MIAP`, `MSIRP`
  instructions) or stack depth mismatches inside `TT_RunIns` to read/write
  arbitrary heap memory.
- **`CVE-2020-15999` (`FreeType` `Load_SBit_Png` heap buffer overflow zero-day):**
  Discovered by Google Project Zero (Sergei Glazunov) in October 2020 while
  actively exploited in the wild against Google Chrome, `CVE-2020-15999` resided
  in `FreeType`'s `Load_SBit_Png` function (`src/sfnt/pngshim.c`). When parsing
  embedded PNG color-bitmap glyphs (`CBDT`/`CBLC` tables), `FreeType` truncated
  the 32-bit `png_uint_32` width and height values from the PNG `IHDR` chunk into
  16-bit unsigned fields (`metrics->width`, `metrics->height` as `FT_UShort`) to
  compute and allocate the backing bitmap buffer size, but then passed the
  untruncated 32-bit dimensions to `png_read_image`—causing a deterministic heap
  buffer overflow whenever width or height exceeded $65{,}535$.

Basis: **normative** CVE records `CVE-2015-2426` and `CVE-2020-15999` +
**source** inspection of `FreeType` `src/sfnt/pngshim.c` and TrueType bytecode
interpreter `src/truetype/ttinterp.c`.

#### 6.3 Apple iOS `Auto Layout` (`Cassowary`) unsatisfiable constraint crashes and exponential UI freezes

Apple's iOS/macOS `Auto Layout` engine is built on the **`Cassowary` incremental
linear arithmetic constraint solver** (Badros, Borning, and Stuckey, UIST 1999 /
ACM TOCHI 2001), which maintains an augmented simplex tableau over equality and
inequality constraints $a_1 x_1 + \dots + a_n x_n \le b$ weighted by a symbolic
hierarchy of priorities (`UILayoutPriorityRequired = 1000`, `High = 750`,
`Low = 250`). Two failure modes have plagued production iOS applications:

1. **Runtime unsatisfiability (`UIViewAlertForUnsatisfiableConstraints`) and
   layout corruption:** When two `Required` (`priority = 1000`) constraints
   become mutually inconsistent under a particular device screen width, dynamic
   type font-size change, or localization string expansion (for example,
   `button.leading >= container.leading + 20`, `button.trailing <=
   container.trailing - 20`, `button.width >= 300` on a `320pt`-wide iPhone SE
   screen), the simplex solver cannot find a feasible solution. At runtime,
   `Auto Layout` logs `UIViewAlertForUnsatisfiableConstraints` and arbitrarily
   **breaks one of the required constraints** to recover feasibility—resulting
   in overlapping text labels, zero-width invisible buttons, or fatal
   `NSInternalInconsistencyException` crashes when a resulting frame has negative
   dimensions or `NaN` coordinates.
2. **Super-polynomial / exponential layout freezes on nested `UIStackView`s:**
   Prior to iOS 12 optimizations (and still reproducible on cyclic or cascading
   inequality graphs with `preferredMaxLayoutWidth` multi-pass text measurement),
   adding $N$ nested `UIStackView`s or interdependent proportional-width views
   triggered $O(2^N)$ or high-degree polynomial simplex pivot cascades during
   `layoutSubviews`, freezing the main UI thread for seconds or triggering an iOS
   watchdog termination (`0x8badf00d`).

Basis: **documentation** of `Cassowary` (Badros et al., UIST 1999) and Apple
`Auto Layout` runtime diagnostics (`UIViewAlertForUnsatisfiableConstraints`).

#### 6.4 Audio DSP: IIR biquad zero-input limit cycles and IEEE-754 subnormal (`denormal`) CPU spikes

Real-time digital audio signal processing (`DSP` in `VST3`/`CLAP`/`AudioUnit`
plugins, `WebAudio`, and embedded synthesizers) executes recursive Infinite
Impulse Response (`IIR`) biquad filters inside hard-real-time callbacks (typically
$128$ samples at $48\text{ kHz} \approx 2.67\text{ ms}$ deadline):
$$y[n] = b_0 x[n] + b_1 x[n-1] + b_2 x[n-2] - a_1 y[n-1] - a_2 y[n-2]$$
Two classic numerical bugs cause catastrophic real-time audio failures:

1. **Zero-input quantization limit cycles and time-varying pole explosion:**
   - Even when the complex poles $p_{1,2}$ of $1 + a_1 z^{-1} + a_2 z^{-2} = 0$
     lie strictly inside the unit circle ($|p_i| < 1$, which guarantees linear
     time-invariant BIBO stability over $\mathbb{R}$), finite-precision rounding
     $Q(\cdot)$ in fixed-point or floating-point recursive state variables creates
     a **deadband** where rounding error cancels the decay factor ($Q(-a_1 y[n-1]
     - a_2 y[n-2]) = y[n-1]$ or $-y[n-1]$). When the input stops ($x[n] = 0$),
     the filter remains trapped in a permanent non-zero periodic oscillation
     (**granular or overflow limit cycle**), emitting audible DC offsets or
     high-frequency tones indefinitely.
   - Furthermore, in Direct Form I/II biquads, rapidly modulating cutoff
     frequency $f_c[n]$ and high resonance $Q[n]$ can transiently push the
     instantaneous Lyapunov energy to infinity even if every frozen-time pole
     satisfies $|p_i(n)| < 1$, blasting $+120\text{ dBFS}$ full-scale digital
     noise or `NaN`s into the audio output buffer.
2. **IEEE-754 subnormal (`denormal`) $100\times$ CPU spikes and audio `XRUN`
   dropouts:** When an audio input signal stops (e.g., a user pauses playback or
   a guitar note decays into silence), the state variables $y[n-1], y[n-2]$ of an
   IIR filter or reverb delay line decay exponentially toward zero: $10^{-10},
   10^{-20}, 10^{-38}$. Once $|y[n]|$ drops below the minimum normalized
   `binary32` float ($2^{-126} \approx 1.175 \times 10^{-38}$) without reaching
   exact `0.0`, the value enters the **IEEE-754 subnormal (denormal) range**. On
   x86/x86_64 and several ARM architectures, arithmetic on subnormal floats
   traps to a microcode assist handler unless the hardware Flush-To-Zero (`FTZ`,
   bit 15 of `MXCSR`) and Denormals-Are-Zero (`DAZ`, bit 6 of `MXCSR`) control
   flags are explicitly enabled on the audio thread. A single decaying biquad
   filter entering the subnormal regime slows down by $10\times$–$100\times$,
   causing the real-time audio thread to miss its $2.67\text{ ms}$ hardware DMA
   deadline (`XRUN` buffer underrun) and freezing the Digital Audio Workstation
   (`DAW`).

Basis: **normative** IEEE-754 subnormal specification and Intel x86 `MXCSR`
architecture manual + **documentation** of digital filter limit cycles
(Oppenheim and Schafer, *Discrete-Time Signal Processing*).

#### 6.5 Smart-home Trigger-Action physical-channel loops (`SOTERIA` and `iRuler`)

Modern smart-home platforms (Samsung SmartThings, IFTTT, Apple Home, Home
Assistant, Matter) execute event-driven **Trigger-Action Programs (`TAP`)**
composed of independent rules ("If trigger $T$, then action $A$"). Seminal
security analyses—**`SOTERIA`** (Celik, McDaniel, and Tan, *Soteria: Automated
IoT Safety and Security Analysis*, USENIX ATC 2018) and **`iRuler`** (Wang et
al., *Charting the Attack Surface of Trigger-Action IoT Platforms*, USENIX
Security 2019), along with **`IoTMon`** (Ding and Hu, CCS 2018)—demonstrated that
verifying rules solely over their digital state variables is fundamentally
unsound because **independent rules interact covertly through shared physical
environment channels** (temperature, humidity, illuminance, smoke, sound, and
air movement):

1. **Physical-channel rule-chaining loops and security breaches:** Consider two
   individually benign apps/rules installed in the same home that share **zero
   digital device variables**:
   - *Rule 1 (Temperature Control App):* `"When indoor temperature > 78°F, open
     the motorized living-room window to cool the room."`
   - *Rule 2 (Winter Heating App):* `"When indoor temperature < 65°F, turn ON the
     space heater (setting target to 80°F)."`
   - *Rule 3 (Security App):* `"When mode == Away and living-room window opens,
     sound burglar alarm"` (or conversely, an energy-saving rule that turns off
     HVAC when a window opens).
   When the room cools below $65^\circ\text{F}$ while the homeowner is away,
   Rule 2 turns on the heater. Through the **physical thermal channel**, the
   heater raises the room temperature above $78^\circ\text{F}$, which triggers
   Rule 1 to open the motorized window—leaving the house physically unsecured
   while the owner is away, triggering false burglar alarms, and cooling the
   room back below $65^\circ\text{F}$ in an **infinite physical-actuation
   oscillation loop**!
2. **Cross-rule safety race conditions (Fire-Safety vs. Security Lock):**
   `SOTERIA` and `iRuler` identified critical action-revert races where a
   life-safety rule (`"When smoke/CO alarm triggers -> unlock front door and turn
   on hallway lights for evacuation"`) is immediately countermanded by a
   concurrent security or energy rule (`"When mode == Night/Away and front door
   is unlocked -> lock front door"` or `"When motion is inactive -> turn off
   lights"`), locking occupants inside a burning building.

Basis: **documentation** and **execution** model-checking findings in `SOTERIA`
(Celik et al., USENIX ATC 2018) and `iRuler` (Wang et al., USENIX Security 2019).

#### 6.6 Architectural lessons for Anneal's 4 `trusted/` primitives from graphics, fonts, layout, audio DSP, and IoT

1. **Unified `Partial.ub` (`defined = False`) across memory, numerical, and
   temporal hazards:** Across shaders (`Dawn`/`Tint`), font bytecode (`FreeType` /
   `ATMFD.dll`), and audio DSP, bugs manifest not only as out-of-bounds array
   indices, but also as non-uniform barrier execution, integer truncation on
   allocation sizes (`CVE-2020-15999`), `NaN`/subnormal generation without
   `FTZ`/`DAZ`, and unbounded loop execution (`TDR` / `XRUN`). In Anneal's
   `Language SemObs`, `defined` gates *all* of these domain-specific hazards
   uniformly.
2. **Parametric `ProductiveOn` prevents `Auto Layout` unsatisfiability and IoT
   relay thrashing:**
   - For a UI constraint layout engine (`Cassowary`), proving `ProductiveOn
     (fun viewport => 320 ≤ viewport.width ∧ viewport.width ≤ 3840) layoutProg`
     guarantees before shipping the app that `UIViewAlertForUnsatisfiableConstraints`
     can *never* occur at any mobile-to-desktop screen width, and step-bounded
     `BehaviorOf` bounds the number of simplex pivots (`WCET`).
   - For a smart-home rule set (`TAP`), `EventualBehaviorOf` + `ProductiveOn`
     proves that every external sensor event stabilizes to a **quiescent
     actuator state in finitely many rule firings**, ruling out relay-destroying
     oscillation loops.
3. **`Abstracts` over coupled cyber-physical state graphs eliminates the
   `SOTERIA`/`iRuler` blind spot:** A verifier that models only digital device
   registers misses physical-channel loops. In Anneal, `Abstracts
   CyberPhysicalEnvLang DigitalTAPLang codec coupledModel tapRules` pairs the
   digital rule engine with an abstract physical-channel dependency graph
   (mapping each actuator to the physical properties—temperature, illuminance,
   humidity, smoke, motion—it perturbs, and each physical property to the
   sensors it triggers), ensuring that cross-channel cycles and `LifeSafety >
   Security` priority inversions are caught statically.

## Boundaries

To prevent future agents from over-generalizing these postmortems or misapplying
them to Anneal's `trusted/` kernel boundary, the following limits apply:

- **Known not to apply — Embedding domain-specific physics or numerical solvers
  inside `trusted/lean/`:** The historical failures in `VNN-COMP`, `VAL`,
  `CGAL`, `NASTRAN`, `FreeType`, `Cassowary`, and `SOTERIA` do **not** justify
  adding floating-point LP solvers, CAD mesh topology kernels, PDDL parsers, or
  physical-channel differential equations into `trusted/lean/`. Anneal's trust
  boundary invariant requires that `trusted/lean/` contain only the minimal
  foundational definitions (`Language`, `Partial`, `BehaviorCodec`, `Compiles`,
  `Abstracts`, `EventualBehaviorOf`, `StepResult`, `ProductiveOn`,
  `InhabitedPre`, and `VerificationResult`). Domain-specific semantics and
  certificate checkers (such as rational Farkas dual checkers for neural
  polytopes or half-edge Euler-characteristic checkers for 2-manifold meshes)
  belong entirely in untrusted `theory/`.
- **Known not to apply — Proving `defined` over $\mathbb{R}$ suffices for
  floating-point or quantized implementations:** Jia and Rinard (SAS 2021),
  `VNN-COMP` (2021–2024), `CGAL`-to-`STL` snap rounding, and IIR biquad limit
  cycles establish that a proof over exact real numbers $\mathbb{R}$ does **not**
  transfer automatically to IEEE-754 `Float32`/`Float64` or fixed-point
  `BitVec` execution. Any `Abstracts` or `Compiles` claim targeting executable
  Rust or hardware kernels must either model the exact machine arithmetic or
  bound the accumulated rounding and subnormal error explicitly.
- **Known not to apply — Safety (`defined`) alone guarantees utility or
  solvability:** As demonstrated by `XSTest`/`OR-Bench` over-refusals in AI
  guardrails and `UIViewAlertForUnsatisfiableConstraints` in iOS `Auto Layout`,
  proving `defined` (`¬ Partial.ub`) without `ProductiveOn` and `InhabitedPre`
  permits degenerate implementations that reject all inputs, emit empty `M30`
  G-code programs, or fail to converge on valid viewports.
- **Not examined — Hardware-level fault injection and physical material defects:**
  While this report covers software, compiler, and finite-element modeling
  failures (such as Sleipner A's $47\%$ `NASTRAN` shear error and Hartford's
  unmodeled top-chord buckling), physical failures caused solely by unmodeled
  metallurgical fatigue, concrete batch contamination, or cosmic-ray bit flips
  (`SEU`s) outside the specified environmental query envelope `pre` were not
  examined.
- **Unknown — Optimal granularity of `TrustPolicy` waivers for hybrid
  neuro-symbolic guardrails:** While `CaMeL` (`arXiv:2503.18813`) demonstrates
  how capability and control/data-flow separation eliminates indirect prompt
  injection for structured tool workflows, tasks that inherently require an
  untrusted model to extract control predicates from unstructured natural
  language remain dependent on explicit `VerificationResult` waivers whose best
  ergonomic granularity in user-facing policies remains an open design question.

## Evidence

### 1. Neural-network verification soundness and `VNN-COMP`

- **Jia and Rinard, SAS 2021:** Kai Jia and Martin Rinard, *Exploiting Verified
  Neural Networks via Floating Point Numerical Error*, in *Static Analysis
  Symposium (SAS 2021)*, LNCS vol. 12913, pp. 191–209, DOI
  `10.1007/978-3-030-88806-0_9`, `arXiv:2003.03021`. Establishes systematic
  construction of adversarial counterexamples on networks verified by
  `MIPVerify` and `ERAN` by exploiting IEEE-754 floating-point rounding and LP
  solver tolerances.
- **`VNN-COMP` 2021–2024 summary reports:**
  - Stanley Bak et al., *The Second International Verification of Neural Networks
    Competition (VNN-COMP 2021): Summary and Results*, `arXiv:2109.00498`.
  - Mark Niklas Müller et al., *The Third International Verification of Neural
    Networks Competition (VNN-COMP 2022): Summary and Results*,
    `arXiv:2212.10376`. Documents `CGDTest` false-`UNSAT` penalties on
    `collins-rul-cnn` and `sri_resnet`, solver tolerance mismatches, and
    counterexample validation.
  - Christopher Brix et al., *The Fourth International Verification of Neural
    Networks Competition (VNN-COMP 2023): Summary and Results*,
    `arXiv:2312.16760`.
  - Christopher Brix et al., *The Fifth International Verification of Neural
    Networks Competition (VNN-COMP 2024): Summary and Results*,
    `arXiv:2412.19985`. Documents $-150$-point soundness penalties, ONNX operator
    semantic discrepancies, and GPU floating-point reduction considerations in
    `Marabou`, `VeriNet`, `NNV`, and `α,β-CROWN`.

### 2. Agentic AI guardrails, prompt injection, and over-refusal

- **`InjecAgent` (2024):** Qiusi Zhan et al., *InjecAgent: Benchmarking Indirect
  Prompt Injections in Tool-Integrated Large Language Model Agents*, Findings of
  ACL 2024, `arXiv:2403.02691`.
- **`AgentDojo` (NeurIPS 2024):** Edoardo Debenedetti et al., *AgentDojo: A
  Dynamic Environment to Evaluate Prompt Injection Attacks and Defenses for LLM
  Agents*, NeurIPS 2024 Datasets and Benchmarks, `arXiv:2406.13352`.
- **`CaMeL` (2025):** Edoardo Debenedetti et al., *Defeating Prompt Injections by
  Design*, `arXiv:2503.18813`. Introduces capability-based data/control-flow
  isolation between a privileged planner and quarantined data reader.
- **`XSTest` (NAACL 2024):** Paul Röttger et al., *XSTest: A Test Suite for
  Identifying Exaggerated Safety Behaviours in Large Language Models*, NAACL
  2024, `arXiv:2308.01263`.
- **`OR-Bench` (ICML 2024):** Justin Cui et al., *OR-Bench: An Over-Refusal
  Benchmark for Large Language Models*, ICML 2024, `arXiv:2405.20947`.

### 3. Automated planning (`VAL` vs. Isabelle/HOL validator)

- **Abdulaziz and Lammich, ICTAI 2018:** Mohammad Abdulaziz and Peter Lammich, *A
  Formally Verified Validator for Classical Planning Problems and Solutions*, in
  *IEEE 30th International Conference on Tools with Artificial Intelligence
  (ICTAI 2018)*, pp. 474–481, DOI `10.1109/ICTAI.2018.00079`, `arXiv:1807.09726`
  (with Archive of Formal Proofs entry `AI_Planning_Languages_Semantics`).
  Demonstrates unsoundness (accepting invalid plans) and incompleteness
  (segmentation faults and false rejections) in the IPC C++ validator `VAL` and
  Lisp validator `INVAL`.
- **PDDL 2.1 specification and `VAL`:** Maria Fox and Derek Long, *PDDL2.1: An
  Extension to PDDL for Expressing Temporal Planning Domains*, JAIR 20 (2003),
  pp. 61–124, DOI `10.1613/jair.1129`; Richard Howey, Derek Long, and Maria Fox,
  *VAL: Automatic Plan Validation, Continuous Effects and Mixed Initiative
  Planning Using PDDL*, ICTAI 2004, DOI `10.1109/ICTAI.2004.120`.

### 4. CAD/CAM, CNC kinematics, machine knitting, and structural FEA postmortems

- **`Manifold` and `Fidget`:** Emmett Lalish, `elalish/manifold` (topological
  2-manifold mesh library integrated into `OpenSCAD` to eliminate `CGAL`
  non-manifold boolean failures); Matt Keeter, `mkeeter/fidget` (interval and
  affine arithmetic implicit SDF/F-Rep evaluator).
- **`Knitout` and `Autoknit`:** James McCann et al., *A Compiler for 3D Machine
  Knitting*, ACM Transactions on Graphics (SIGGRAPH 2016), 35(4), Article 49,
  DOI `10.1145/2897824.2925940`; Vidya Narayanan et al., *Automatic Machine
  Knitting of 3D Meshes*, ACM Transactions on Graphics (SIGGRAPH 2018), 37(4),
  Article 63, DOI `10.1145/3197517.3201335`.
- **Hartford Civic Center Collapse (1978):** Lev Zetlin Associates, *Report of
  the Engineering Investigation Concerning the Causes of the Collapse of the
  Hartford Coliseum Space Truss Roof on January 18, 1978*, submitted to the City
  of Hartford, CT (1978); Robert S. Loomis et al., *Torsional Buckling Study of
  Hartford Coliseum*, Journal of the Structural Division, ASCE, 106(1), 1980,
  pp. 211–231.
- **Sleipner A Platform Sinking (1991):** Bernt Jakobsen, *The Sleipner Accident
  and Its Causes*, Engineering Failure Analysis, 1(3), 1994, pp. 193–199, DOI
  `10.1016/1350-6307(94)90018-3`; Randall G. Collins et al., *The Sleipner A
  Platform Failure*, Concrete International, 19(8), 1997, pp. 28–35 (documenting
  the $47\%$ tricell wall shear stress underestimation in the coarse `NASTRAN`
  finite-element mesh).

### 5. Shader compilers, font bytecode CVEs, UI layout, audio DSP, and IoT rules

- **`GraphicsFuzz` (OOPSLA 2017):** Alastair F. Donaldson, Hugues Evrard, Andrei
  Lascu, and Paul Thomson, *Automated Testing of Graphics Shader Compilers*,
  PACMPL 1 (OOPSLA 2017), Article 93, DOI `10.1145/3133917`.
- **Font vulnerabilities:** `CVE-2015-2426` (Microsoft Windows `ATMFD.dll`
  OpenType/TrueType kernel memory corruption disclosed July 2015, MS15-078);
  `CVE-2020-15999` (`FreeType` `Load_SBit_Png` 16-bit integer truncation heap
  buffer overflow in `src/sfnt/pngshim.c`, discovered by Google Project Zero,
  October 2020).
- **`Cassowary` and iOS `Auto Layout`:** Greg J. Badros, Alan Borning, and Peter
  J. Stuckey, *The Cassowary Linear Arithmetic Constraint Solving Algorithm*,
  ACM Transactions on Computer-Human Interaction (TOCHI), 8(4), 2001,
  pp. 267–306, DOI `10.1145/504704.504705`.
- **Smart-Home Trigger-Action physical-channel analysis:** Z. Berkay Celik,
  Patrick McDaniel, and Gang Tan, *Soteria: Automated IoT Safety and Security
  Analysis*, USENIX Annual Technical Conference (USENIX ATC 2018), pp. 147–158;
  Qi Wang et al., *Charting the Attack Surface of Trigger-Action IoT Platforms*,
  ACM CCS 2019 / `iRuler` (*Discovering Inter-Rule Vulnerabilities in Smart Home
  Systems*, USENIX Security 2019).

### 6. Anneal repository authority

- Repository: `joshlf/anneal` at revision
  `24367bd1a8c784f2578535954f9915e24894a56f`.
- `PRINCIPLES.md` and `README.md`: establish Anneal's non-negotiable UB-freedom
  (`defined`), fail-closed promise, and the `trusted/` audit invariant.
- Observation date for this synthesis: `2026-10-31`.

## Revalidation

Revalidate this report when any of the following conditions hold:

1. **Changes to Anneal's `trusted/lean/` semantic primitives:** If `Language`,
   `Partial`, `BehaviorCodec`, `Compiles`, `Abstracts`, `EventualBehaviorOf`,
   `StepResult.externalCall`, `ProductiveOn`, `InhabitedPre`, or
   `VerificationResult` changes its signature or invariants, re-verify that each
   of the six defect classes in Section 1 remains blocked without requiring
   domain-specific axioms in `trusted/`.
2. **Discriminating probe for floating-point vs. real-arithmetic soundness
   (Section 2):** Construct a 2-layer `ReLU` network whose exact rational output
   margin $y_1(x) - y_2(x)$ is $+2^{-26}$ on $x \in [0, 1]$, while IEEE-754
   `binary32` evaluation yields $-2^{-24}$ due to absorption $(1.0 \oplus
   2^{-25}) \ominus 1.0 = 0.0$. Verify that any `Abstracts` certificate checker
   in `theory/` rejects an un-widened rational bound proof when instantiated
   against `Float32` operational semantics.
3. **Discriminating probe for PDDL simultaneous `add`/`delete` micro-steps
   (Section 4):** Evaluate a single-step action $a$ with $\text{pre}(a) = \{p\}$,
   $\text{del}(a) = \{p\}$, and $\text{add}(a) = \{p\}$ (representing an aliased
   move $\text{move}(A, A)$) followed by an action $b$ requiring $\text{pre}(b)
   = \{p\}$. Confirm that the mechanized `PDDLLang` step function computes $s_1
   = (s_0 \setminus \{p\}) \cup \{p\} = \{p\}$ rather than $\emptyset$.
4. **Discriminating probe for `ProductiveOn` anti-vacuity (Sections 3, 5, 6):**
   Instantiate a candidate guardrail, G-code compiler, or layout solver with a
   degenerate implementation that halts immediately or rejects all inputs (`defined
   = True`, `val = fun _ => False`). Confirm that `Compiles` alone succeeds
   vacuously on empty `val` only if `ProductiveOn` is omitted, and that
   requiring `InhabitedPre pre ∧ ProductiveOn pre prog` immediately rejects the
   degenerate implementation.
