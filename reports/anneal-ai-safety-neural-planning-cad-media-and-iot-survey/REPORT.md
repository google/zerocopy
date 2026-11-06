# Real-World Verification Tools and Historical Failure Postmortems Across AI Safety, Neural Certification, Automated Planning, CAD/CAM, Fabrication, Civil/BIM, Graphics/Media, and Smart-Home IoT

## Summary

### Part I — Real-World Verification, Synthesis, and Compilation Tool Landscape

Across ten application domains outside traditional systems software—agentic AI
action firewalls, neural-network certification, automated planning (`PDDL` and
`HTN`), CAD/CSG solid modeling and G-code slicing, programmable textiles and
sheet/origami folding, civil/structural and `BIM`/`IFC` compliance, GPU shaders
and UI/typography layout, music theory and audio `DSP`, game solvability and
virtual economies, and smart-home/IoT trigger-action rules—production and
research toolchains converge on four structural verification mechanisms:

1. **Explicit partiality and domain-specific undefined behavior (`Language
   SemObs` and `Partial`):** Every examined verifier separates well-defined
   domain executions (`defined = True`) from catastrophic domain hazards
   (`Partial.ub`, `defined = False`), while projecting concrete executions
   through an observation function (`obs : Out → SemObs`) that erases internal
   representation state (such as LLM `KV`-cache tensors, branch-and-bound split
   histories, `Knitout` front/back bed transfer shuffles, or `SPIR-V` register
   allocations).
2. **Bidirectional representation codecs with fail-closed decoding
   (`BehaviorCodec`, `Compiles`, and `Abstracts`):** Downward compilation
   passes (such as `Cedar` policy lowering, `HTN`-to-`PDDL` task decomposition,
   `CSG`-to-G-code slicing, `Autoknit` stitch-graph scheduling, or `Faust`
   block-diagram codegen) instantiate `Compiles`, whereas upward sound
   over-approximations (such as `DeepPoly`/`α,β-CROWN` polytope propagation,
   `Fast Downward` unsolvability certificates, swept-volume octrees, Interval
   `FEM`, or `Astrée` digital-filter ellipsoids) instantiate `Abstracts`. In
   both directions, malformed target states (`NaN`/`Inf` floats, unclosed mesh
   manifolds, stranded live knitting loops, or schema-invalid tool calls) map to
   `decodeOut = none` (`False` under `BehaviorCodec.toMorphism`), preventing
   fail-open deserialization or vacuous target refinement.
3. **Anti-vacuity, multi-step temporal decoupling, and demonic environment
   boundaries (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`):** Unconstrained optimization and automated
   synthesis routinely exploit vacuity—producing paranoid AI firewalls that
   reject 100% of benign prompts, CNC G-code programs that cut only empty air,
   windowless buildings with zero doors, layout engines that hide overflowing
   text via `display: none`, or puzzle generators that emit unsolvable boards.
   Pairing `InhabitedPre` with `ProductiveOn` over `EventualBehaviorOf` blocks
   these vacuous solutions and decouples $1 \to k$ compilation scales (such as
   one `CSG` node lowering to $50{,}000$ `G-01` micro-segments), while
   `StepResult.externalCall boundaryInv branches` models open-world transitions
   against demonic environment nondeterminism (untrusted LLM token proposals,
   `FOND` contingent environment outcomes, CNC touch-probe readings, or
   cyber-physical sensor feedback).
4. **Positive per-obligation waiver accounting (`VerificationResult policy
   waived obligations`):** Rather than placing unverified neural heuristics,
   floating-point geometry kernels, or empirical physics constants on the left
   side of an implication (`hTcb → Safe`)—where any inconsistency discharges
   all obligations via `False.elim`—sound neuro-symbolic and engineering
   pipelines isolate each unproved assumption as a positive obligation identifier
   in `waived` (`ob.id ∈ waived ∨ ob.prop`), preserving machine-checked proofs
   for all non-waived obligations.

Basis: normative + documentation + source + derived.

### Part II — Historical Verification, Compiler, and Operational Failure Postmortems

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
   3D CNC simulators modeled `G-00` rapid traverses as straight lines while
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

### Part I — Real-World Verification and Compilation Tools Applicability

This report applies to the design of domain-specific verification, compilation,
and certification layers atop Anneal's `trusted/lean/` semantic kernel, and
specifically evaluates how 88 real-world tools and standards across ten
application domains map onto Anneal's four foundational primitives:

- **Primitive 1 (`Language SemObs` & `Partial`):** Parameterized language
  semantics `Prog → Query → Partial (Out → Prop)` equipped with an observation
  projection `obs : Out → SemObs` and a strict separation between well-defined
  executions (`defined : Prop`) and undefined behavior (`Partial.ub`).
- **Primitive 2 (`BehaviorCodec L₁ L₂`, `Compiles`, & `Abstracts`):**
  Cross-language refinement (`Compiles`) and sound over-approximation
  (`Abstracts`) mediated by query/output codecs with round-trip laws
  (`decodeQuery_encodeQuery`, `decodeOut_encodeOut`, `encodeOut_of_decodeOut`),
  observation preservation (`obs_decodeOut`), and fail-closed rejection of
  invalid target states (`decodeOut = none`).
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`):** Total/productive execution guarantees over
  non-empty preconditions, fuel-independent trace semantics, and gated external
  interactions with demonic environment branching.
- **Primitive 4 (`VerificationResult policy waived obligations`):** Positive
  disjunctive waiver envelopes (`ob.id ∈ waived ∨ ob.prop`) gated by a
  `TrustPolicy`.

The subjects listed in `REPORT.json` are examined as a comparative structural
matrix: each concrete external tool or specification is analyzed in terms of
its native verification boundary, its Trusted Computing Base (`TCB`), and its
exact mathematical correspondence to Anneal's four primitives. Claims about
external tools reflect their published specifications, open-source repositories,
and peer-reviewed literature as of `2026-10-31`.

### Part II — Historical Verification and Operational Failures Applicability

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
  `elalish/manifold` and `mkeeter/fidget`; CNC `G-00` rapid-traverse dogleg
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

### 3.1 Cross-Domain Structural Synthesis: Anneal's Four Primitives

Before examining individual domains, we record the exact correspondence law
that governs all ten tool ecosystems:

1. **The Propose-and-Verify (Modulo) Pattern:** In all ten domains, synthesis
   or search (by an LLM, a gradient-based topology optimizer, an `MILP`/`SMT`
   solver, a heuristic `A*` planner, or an e-graph equality saturation engine)
   is computationally expensive or probabilistic, whereas checking a candidate
   artifact or dual certificate (`VAL` plan validation, `α,β-CROWN` dual bounds,
   `spirv-val` dominance/type checking, `Knitout` needle simulation) is
   deterministic and polynomial-time.
2. **Why `ProductiveOn` and `obs_decodeOut` Are Load-Bearing:** Whenever a
   verifier checks only safety (`defined`), an automated generator can satisfy
   the specification trivially by emitting a degenerate artifact (`M-30` empty
   G-code, `0.0` silent audio, `deny all` firewall policy, or an unreachable
   goal state). Requiring `InhabitedPre pre`, `ProductiveOn pre prog`, and
   `obs_decodeOut` forces the artifact to achieve the domain's positive
   functional spine on all valid inputs.
3. **Why Positive Waivers (`VerificationResult`) Prevent Neuro-Symbolic
   Collapse:** Every domain mixes kernel-checkable invariants with empirical or
   heuristic boundaries (such as `PromptGuard` classifier recall, floating-point
   mesh tolerances, or `AHJ` building-code variances). Encoding those boundaries
   as positive `Obligation Id` entries in `waived` prevents a single flawed
   external oracle from silently invalidating unrelated mathematical proofs.

Basis: derived.

---

### 3.2 Domain 1: Agentic AI Sandboxes, Action Firewalls, and Constrained Decoding

#### 1. Goals and Target Users
Agentic AI sandboxes, action firewalls, and constrained-decoding engines protect
tool-using Large Language Model (`LLM`) and Vision-Language Model (`VLM`) agents
against **indirect prompt injection**, **confused-deputy privilege escalation**,
**private data exfiltration**, and **schema-violating or unsafe code/tool
invocations**. Target users include enterprise AI platform engineers, security
architects deploying Model Context Protocol (`MCP`) tool servers, and application
developers integrating untrusted retrieval-augmented generation (`RAG`) data
with high-privilege APIs (email, shell, SQL, cloud IAM, and payment systems).

#### 2. Concrete Tool Lineage and Technical Architecture
- **`CaMeL` (`google-research/camel-prompt-injection`, Debenedetti et al.,
  2025):** Introduces *CApabilities for MachinE Learning* by refactoring the
  dual-LLM pattern into a capability-tracked Python subset interpreter. A
  privileged **Quarantined/Control LLM** translates the trusted user prompt
  into a deterministic dataflow graph/program, while an unprivileged reader LLM
  extracts structured values from untrusted documents without ever influencing
  control-flow branches or tool selection. Every variable carries a capability
  tag (provenance + authorized readers/sinks) checked deterministically at every
  tool invocation boundary.
- **`FIDES` (Microsoft Research, Costa et al., 2025):** The *Flow Integrity
  Deterministic Enforcement System* formalizes dynamic **Information-Flow
  Control (`IFC`)** over confidentiality and integrity lattices for autonomous
  agents. `FIDES` tracks taint labels across multi-turn planner state and
  introduces selective information-hiding primitives (quarantined summarization
  and declassification gates) so an agent can process low-integrity web/email
  content without tainting high-integrity tool-call arguments.
- **`SEAgent` (2025) & `AirGapAgent` (Bagdasarian et al., ACM CCS 2024):**
  `SEAgent` enforces Mandatory Access Control (`MAC`) and Attribute-Based
  Access Control (`ABAC`) across multi-agent workflows and `SEMemory` `RAG`
  stores, preventing transitive privilege escalation across agent delegation
  chains. `AirGapAgent` formalizes Nissenbaum's *Contextual Integrity* as a
  two-stage architecture where a trusted data-minimization gate projects user
  vault data down to the minimal task-relevant slice before an air-gapped
  conversational agent interacts with untrusted third-party inputs.
- **`Invariant Guardrails` (`invariantlabs-ai/invariant`, ETH Zurich /
  Invariant Labs):** A trace-based policy language (`IPL`) and runtime
  reference monitor for `MCP` and agent trajectories. Policies match temporal
  and dataflow patterns over message traces (`raise PolicyViolation(...) if
  (call: ToolCall) -> ...` where untrusted input flows into an external sink).
- **`Cedar` (`cedar-policy/cedar-spec`, Cutler et al., OOPSLA 2024) & `OPA`
  (`open-policy-agent/opa`, Rego):** General-purpose declarative authorization
  engines increasingly used as deterministic policy decision points (`PDP`s) for
  agent tool gateways. `Cedar` is designed for automated reasoning and has a
  mechanized formal model and differential verification suite in **Lean 4**
  (`cedar-spec`) plus SMT-based policy analysis (`Cedar` symposium verifier).
  `OPA` evaluates Datalog-derived `Rego` policies over hierarchical JSON context
  documents.
- **`NeMo Guardrails` / `Colang` (`NVIDIA/NeMo-Guardrails`) & `LlamaFirewall` /
  `CodeShield` (`meta-llama/PurpleLlama`, Meta 2025):** `NeMo Guardrails` uses
  an event-driven modeling language (`Colang 1.0/2.0`) to define canonical
  conversational flows and action rails. `LlamaFirewall` orchestrates three
  layered guards: `PromptGuard 2` (a DeBERTa classifier for direct/indirect
  jailbreaks), `AlignmentCheck` (a chain-of-thought semantic auditor detecting
  goal hijacking), and `CodeShield` (static analysis via Semgrep and regex rules
  blocking insecure code generation).
- **`LMQL` (`eth-sri/lmql`, Beurer-Kellner et al., PLDI 2023), `Guidance`
  (`guidance-ai/guidance`), `Outlines` (`dottxt-ai/outlines`, Willard & Louf
  2023), & `OpenSandbox`:** Constrained-decoding engines (`LMQL`, `Guidance`,
  `Outlines`) compile regular expressions, context-free grammars (`CFG`s), JSON
  schemas, or token-level logical predicates into deterministic finite-state
  automata (`DFA`s) or pushdown masks that zero out invalid token logits
  ($p(t_i) = -\infty$) during autoregressive generation. Container/microVM
  sandboxes (`OpenSandbox`) isolate OS-level side effects (filesystem, network
  namespaces, `seccomp-bpf`) when executing agent-generated code.

#### 3. Design Philosophy and Tradeoffs
The central engineering divide separates **probabilistic semantic filters**
(`PromptGuard 2`, `AlignmentCheck`, LLM-as-a-judge rails) from **architectural
information-flow and capability systems** (`CaMeL`, `FIDES`, `SEAgent`,
`Cedar`, `Outlines`). Probabilistic classifiers inspect unstructured natural
language and retain high flexibility on open-ended tasks, but suffer from
non-zero false-negative rates under adaptive adversarial attacks and false
positives that degrade utility. Conversely, `CaMeL` and `FIDES` achieve
deterministic non-interference—untrusted data *cannot* alter control flow or
exfiltrate to unauthorized sinks even if the reader LLM is 100% subverted—at
the cost of requiring upfront workflow planning or explicit declassification
prompts when control flow genuinely depends on retrieved data.

#### 4. Ecosystem Comparisons
- **Control/Data Separation vs. Trace Auditing:** `CaMeL` and `FIDES` enforce
  dataflow isolation *by construction* inside the execution interpreter,
  whereas `Invariant Guardrails` inspects the sequence of `MCP` tool events
  retrospectively/inline at the proxy boundary.
- **Mechanized Policy Engines (`Cedar` vs. `OPA`/`Rego`):** `Cedar` restricts
  recursion and unbounded loops so every policy terminates in bounded time and
  admits complete SMT encoding and Lean 4 formalization (`cedar-spec`), whereas
  `Rego` provides fuller Datalog expressiveness without mechanized kernel
  equivalence proofs.
- **Token-Masking (`Outlines`/`Guidance`/`LMQL`) vs. Post-Generation Parsing:**
  `Outlines` pre-compiles JSON schemas into indexable vocabulary masks over the
  tokenizer's byte-level `DFA`, guaranteeing 100% syntactically well-formed
  output on termination without retry loops.

#### 5. Formal Theory and TCB Analysis
- **`Cedar`:** Formalized in Lean 4 (`cedar-spec`), with mechanized proofs of
  evaluator soundness, termination, and `disallow-by-default` safety; its
  production Rust implementation (`cedar-policy`) is differentially tested and
  verified against the Lean specification.
- **`CaMeL` / `FIDES`:** Grounded in Denning-style lattice Information-Flow
  Control ($\text{Low} \sqsubseteq \text{High}$ confidentiality,
  $\text{Trusted} \sqsubseteq \text{Untrusted}$ integrity) and capability
  security; enforcement relies on an unverified Python/Rust runtime interpreter
  TCB.
- **`Outlines` / `LMQL`:** Grounded in Brzozowski derivatives and pushdown
  automaton intersection with subword token vocabularies; the TCB includes the
  regex-to-`DFA` compiler and floating-point logit-masking kernel.

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `PolicyLang.Prog`: Declarative capability + `IFC` lattice policy (`Cedar` /
    `CaMeL` / `FIDES` specification).
  - `OrchestratorLang.Prog`: Concrete stateful agent proxy / `MCP` reference
    monitor + token-masking automaton.
  - `Query`: Initial user principal capability token, initial taint-label map
    over data stores, and user prompt.
  - `Out` & `SemObs` (`obs`): `Out` is `EventualOut ToolTrace (AgentResponse ×
    SandboxState)`. `obs` projects out internal LLM `KV`-cache tensors and
    chain-of-thought scratchpads, retaining the externally visible sequence of
    tool calls, capability tokens, and taint classifications.
  - `Partial.ub` (`defined = False`): Any execution prefix that invokes a tool
    without a valid capability, passes `Untrusted`-tainted or `Secret` data to
    an unauthorized external sink (exfiltration), violates an `Outlines` schema
    invariant, or exceeds a rate/spending budget.
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Compiles PolicyLang OrchestratorLang codec policy proxy`: Proves that the
    compiled Rust/Wasm `MCP` action firewall refines the declarative capability
    specification across all possible LLM completions.
  - `Abstracts TaintLatticeLang OrchestratorLang codec taintSummary proxy`:
    Soundly over-approximates dynamic taint propagation across `RAG` memory
    reads and writes (`FIDES` / `SEAgent`).
  - `decodeOut = none`: Rejects malformed JSON tool payloads (`Outlines`
    unterminated strings) or forged capability MACs (`False`), while
    `obs_decodeOut` guarantees that the concrete orchestrator cannot hide or
    reorder external side-effecting tool calls.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **Blocks the "Paranoid Brick Firewall" Goodhart loophole:** A firewall that
    rejects 100% of user prompts satisfies `defined = True` (zero unsafe tool
    calls) vacuously. `InhabitedPre SafeBenignQueries` and `ProductiveOn
    SafeBenignQueries proxy` prove that every authorized benign user workflow
    admits at least one productive execution path to normal completion.
  - **`StepResult.externalCall boundaryInv branches`:** Models both external
    tool calls (`boundaryInv` = runtime capability + taint check) and untrusted
    LLM token generation / web retrieval (`branches` = demonic choice over all
    adversarial LLM outputs or prompt-injected payloads). Proving `defined`
    over `externalCall` guarantees safety regardless of what the LLM proposes.
- **`VerificationResult` & `TrustPolicy`:**
  - Separates deterministic capability and `IFC` non-interference obligations
    (proved with zero waivers) from statistical classifier assumptions (such as
    `PromptGuard 2` or `AlignmentCheck` recall, recorded as explicit waiver IDs
    `.heuristicJailbreakClassifierSound` in `waived`).

Basis: documentation + source + derived.

---

### 3.3 Domain 2: Neural-Network Certification, Abstract Interpretation, and Specification Compilers

#### 1. Goals and Target Users
Neural-network certification tools mathematically prove that every input within
a high-dimensional perturbation region (such as an $\ell_\infty$ ball
$B_\infty(x_0, \epsilon)$, a geometric sensor transformation, or a demographic
counterfactual neighborhood) maps exclusively to safe output classes or control
commands, free of adversarial misclassification or numerical overflow. Target
users include aerospace and autonomous-vehicle safety engineers (certifying
`ACAS Xu` collision avoidance or lane-keeping controllers), ML robustness
researchers (`VNN-COMP` participants), and high-assurance embedded engineers
deploying quantized neural networks.

#### 2. Concrete Tool Lineage and Technical Architecture
- **`α,β-CROWN` (`Verified-Intelligence/alpha-beta-CROWN`, Zhang, Wang, Xu,
  Hsieh et al.):** The perennial winner of the International Verification of
  Neural Networks Competition (`VNN-COMP` 2021–2025). Combines GPU-accelerated
  backward linear bound propagation (`CROWN` / `LiRPA`) with optimizable slopes
  $\alpha$ (for unstable activation relaxations) and Lagrangian split
  multipliers $\beta$ (encoding branch-and-bound `BaB` neuron/input split
  constraints directly into the dual objective).
- **`Marabou` (`NeuralNetworkVerification/Marabou`, Katz et al., CAV 2019 /
  2024, successor to `Reluplex`, CAV 2017):** An SMT-based verifier extending
  the simplex algorithm with native piecewise-linear activation constraints
  (`ReLU`, `Max`, `AbsoluteValue`), tightening bounds via symbolic DeepPoly/CROWN
  passes and parallel Split-and-Conquer (`SnC`).
- **`ERAN` (`eth-sri/eran`, Vechev group at ETH Zurich: `DeepZ`, `DeepPoly`,
  `GPUPoly`, `PRIMA`) & `MN-BaB` (`eth-sri/mn-bab`):** Abstract interpretation
  engines over specialized numerical domains: `DeepZ` (zonotopes with affine
  noise symbols $\epsilon_i \in [-1, 1]$), `DeepPoly` / `GPUPoly` (each neuron
  bounded by one lower and one upper symbolic linear combination of preceding
  neurons plus concrete intervals), `PRIMA` (convex hull approximations over
  multi-neuron groups capturing cross-neuron dependencies), and `MN-BaB`
  (combining multi-neuron `PRIMA` constraints with GPU branch-and-bound).
- **`nnenum` (`stanleybak/nnenum`, Bak, CAV 2021) & `NNV` (`verivital/nnv`,
  Tran, Manzanas Lopez, Johnson et al., CAV 2020):** Geometric set-propagation
  verifiers based on **Star Sets** (generalized zonotopes represented as an
  affine transformation of a polytope $x = c + V \alpha$ where $C \alpha \le d$,
  enabling exact single-step split representation and fast LP/zonotope
  pre-filtering). `NNV` extends star-set reachability to convolutional networks,
  Neural ODEs, and closed-loop Simulink/Cyber-Physical control systems.
- **`OVAL` (`oval-group/oval-bab`, Oxford), `VeriNet` (Imperial College),
  `PyRAT` (CEA List), & `SAVer`:** `OVAL` pioneers Lagrangian decomposition and
  proximal/active-set dual solvers for `BaB`. `VeriNet` combines symbolic
  interval propagation with dynamic splitting. `PyRAT` (*Python Reachability
  Assessment Tool*, CEA List) provides modular abstract domains (intervals,
  zonotopes, polyhedra) tailored for industrial AI safety qualification. `SAVer`
  applies abstraction-refinement to support-vector machines (`SVM`s) and tree
  ensembles.
- **`VNN-LIB` (`VNNLIB/VNNLIB-Standard`), `Vehicle` (`vehicle-lang/vehicle`,
  Daggitt, Atkey, Kokke et al.), & `CAISAR` (`git.frama-c.com/pub/caisar`, CEA
  List):** Specification and compilation frameworks. `VNN-LIB` (and `VNN-LIB
  2.0`) defines the SMT-LIB-based standard format pairing `ONNX` models with
  input/output linear constraints. `Vehicle` is a high-level functional
  dependently typed specification language that compiles specifications to (1)
  differentiable training loss functions, (2) low-level `VNN-LIB` / `Marabou`
  queries, and (3) mechanized proof scripts in **Agda, Rocq/Coq, and
  Isabelle/HOL** that bridge the "embedding gap" between domain types (such as
  real-world velocities and angles) and normalized tensor vectors. `CAISAR` uses
  `WhyML` (from `Why3`) to specify multi-model ML pipelines and translates them
  via graph transformations into `VNN-LIB` and `SMT-LIB` queries.
- **`FairSquare` (Albarghouthi et al., OOPSLA 2017) & `VeriFair` (Bastani et
  al., OOPSLA 2019):** Probabilistic and relational fairness verifiers proving
  demographic parity or individual fairness across decision trees and neural
  networks via symbolic volume computation (`FairSquare`) or adaptive
  concentration inequalities (`VeriFair`).
- **`Verisig` (`verisig/verisig`, Ivanov et al., HSCC 2019) & `ReachNN*` (Huang
  et al.):** Closed-loop neural-network controller verifiers that transform
  sigmoid/tanh/ReLU networks into hybrid automata (`Verisig`, solved via
  `Flow*` Taylor models) or Bernstein polynomial approximations (`ReachNN*`)
  coupled with continuous plant ODEs.

#### 3. Design Philosophy and Tradeoffs
Complete SMT/MIP solvers (`Marabou`, MIP formulations) decide piecewise-linear
verification queries exactly on small networks but face $2^N$ worst-case
combinatorial blowup as `ReLU` counts scale to millions. Pure single-pass
abstract interpreters (`DeepZ`, `DeepPoly`) run in polynomial time on GPUs but
accumulate over-approximation error ("wrapping effect") across deep layers,
failing to prove tight boundaries. Modern engines (`α,β-CROWN`, `MN-BaB`,
`PyRAT`) bridge both regimes via **Incomplete Verification + Branch-and-Bound
(`BaB`)**: fast symbolic linear relaxations prune 99% of branches on GPUs while
Lagrangian multipliers ($\beta$) refine the remaining hard sub-problems.
However, almost all GPU verifiers compute bounds in IEEE-754 `FP32`/`FP64`
arithmetic, creating floating-point soundness gaps unless checked by an exact
rational/interval certificate checker.

#### 4. Ecosystem Comparisons
- **Bound Propagation vs. Geometric Star Sets:** `α,β-CROWN` and `DeepPoly`
  propagate backward symbolic linear inequalities (scaling to large vision and
  transformer blocks), whereas `nnenum` and `NNV` propagate forward `Star` sets
  that excel on low-dimensional control networks (`ACAS Xu`, `Verisig`
  benchmarks) with many layers.
- **Specification Level (`VNN-LIB` vs. `Vehicle`/`CAISAR`):** Raw `VNN-LIB`
  operates over flat normalized tensor indices (`X_0, X_1, Y_0`) and cannot
  express multi-network composition or domain unnormalization invariants,
  forcing users to trust ad-hoc Python wrapper scripts; `Vehicle` and `CAISAR`
  compile typed domain specifications into `VNN-LIB` while tracking the
  translation proof (`Vehicle` exports to Agda/Rocq).

#### 5. Formal Theory and TCB Analysis
- **Mathematical Core:** Galois connections $(\alpha, \gamma)$ between concrete
  power-set semantics $\mathcal{P}(\mathbb{R}^n)$ and abstract domains
  (zonotopes, `DeepPoly` symbolic intervals, Star sets), plus Lagrangian strong
  duality ($\max_{\alpha, \beta \ge 0} \min_{x \in B} \mathcal{L}(x, \alpha,
  \beta) \le \min_{x \in B, \text{split}} c^\top y(x)$).
- **TCB Vulnerability:** Standard `VNN-COMP` solvers have large unverified
  Python/PyTorch/C++/CUDA TCBs, floating-point rounding in dual bound
  evaluations, and unverified `ONNX`-to-internal-graph loaders. `Vehicle`
  reduces the specification-lowering TCB via ITP backend extraction, but still
  treats the external `VNN-LIB` solver as an oracle unless a dual certificate is
  checked in the theorem prover.

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `NNLang.Prog`: Concrete neural network computational graph (weights, biases,
    activations over $\mathbb{Q}$, IEEE-754 floats, or quantized `BitVec`s).
  - `PolytopeLang.Prog`: Abstract symbolic bound propagator (`DeepPoly` /
    `α,β-CROWN` dual tree / `Star` set transformer).
  - `Query`: Input region specification $B_\infty(x_0, \epsilon)$ (or relational
    fairness pair $(x, x')$).
  - `Out` & `SemObs` (`obs`): Concrete logit vector $y \in \mathbb{Q}^k$ (or
    abstract bounding box $[l, u] \subseteq \mathbb{Q}^k$); `obs` extracts the
    top-1 class decision $\arg\max_i y_i$ or safe-control region indicator.
  - `Partial.ub` (`defined = False`): Adversarial robustness violation ($\exists
    x \in B_\infty(x_0, \epsilon)$ with $y_{\text{true}}(x) - y_{\text{adv}}(x)
    \le 0$), individual fairness violation, or `NaN`/`Inf`/quantized accumulator
    overflow.
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Abstracts PolytopeLang NNLang codec crownCert concreteNet`: **Sound
    abstract interpretation!** Because `Abstracts` requires `NNLang.sem
    concreteNet ≤ codec.toMorphism (PolytopeLang.sem crownCert)`, an untrusted
    GPU run of `α,β-CROWN` or `PyRAT` can emit its dual multipliers $(\alpha,
    \beta)$ and `BaB` split tree, which a compact Lean checker in `theory/`
    verifies in exact rational/interval arithmetic to prove `Abstracts`.
  - `Compiles SpecLang VNNLibLang codec vehicleSpec vnnlibQuery`: Formalizes
    `Vehicle` and `CAISAR` compilation so the "embedding gap" between domain
    units and tensor coordinates is verified via `BehaviorCodec`.
  - `decodeOut = none`: Rejects `NaN`/`Inf` floating-point outputs or
    out-of-range quantized activations (`False`).
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **Blocks vacuous `BaB` splits and empty $\epsilon$-balls:** In `BaB`
    solvers, contradictory `ReLU` split constraints ($z_i \ge 0 \land z_i < 0$)
    or malformed `VNN-LIB` input bounds make a sub-problem's input set empty
    (`¬ InhabitedPre`). `InhabitedPre` ensures the input perturbation region is
    non-empty, and `ProductiveOn` proves the concrete network evaluates totally
    without numerical fault.
  - **`StepResult.externalCall boundaryInv branches`:** Captures closed-loop
    hybrid verification (`Verisig` / `ReachNN*` / `NNV`): at each sampling step,
    the neural controller emits an action checked by `boundaryInv` (safety
    barrier / actuator saturation), and `branches` models the continuous ODE
    plant evolution (`Flow*` Taylor flowpipe) under bounded disturbances.
- **`VerificationResult` & `TrustPolicy`:**
  - Tracks each local robustness anchor $(x_i, \epsilon_i)$ or floating-point
    GPU solver oracle call (`waived := [.unverifiedGpuFloatBabSolver]`) as an
    explicit `Obligation Id` when exact rational dual-certificate replay is not
    yet enabled.

Basis: normative + documentation + source + derived.

---

### 3.4 Domain 3: Automated Planning, PDDL Validators, HTN Refinement, and Neuro-Symbolic Moduli

#### 1. Goals and Target Users
Automated planning systems and plan validators synthesize or certify action
schedules (`STRIPS`, `PDDL 2.1+` durative/numeric actions, Hierarchical Task
Networks `HTN`/`HDDL`, and Fully Observable Non-Deterministic `FOND` policies)
that transition an environment from an initial state $s_0$ to a goal state
$G$. Target users include autonomous robotics and spacecraft mission engineers,
industrial logistics schedulers, International Planning Competition (`IPC`)
organizers, and AI engineers building neuro-symbolic **LLM-Modulo** pipelines
where an untrusted LLM proposes plans or PDDL models checked by a formal
validator.

#### 2. Concrete Tool Lineage and Technical Architecture
- **`VAL` (`KCL-Planning/VAL`, Howey, Long, & Fox, King's College London, ICTAI
  2004) & `INVAL` (`patrikhaslum/INVAL`, Haslum, ANU):** The reference `IPC`
  plan validators. `VAL` (in C++) validates classical `STRIPS`/`ADL`, `PDDL 2.1`
  durative actions, continuous linear processes (`#t`), events, and `PDDL 3.0`
  state-trajectory constraints (`always`, `sometime`, `at-most-once`), checking
  epsilon-separation against concurrent mutex interference. `INVAL` (in Common
  Lisp) provides an independent validation oracle built specifically to cross-check
  `VAL` edge cases in conditional effects, axioms/derived predicates, and numeric
  fluents.
- **Isabelle/HOL Verified PDDL Validator (Abdulaziz & Lammich, ITP 2018; Archive
  of Formal Proofs `AI_Planning_Languages_Semantics`):** Formalizes the syntax,
  well-formedness typing rules, and operational semantics of `STRIPS`/`ADL` and
  multi-valued `SAS+` inside Isabelle/HOL, proving soundness and completeness of
  an executable plan checker extracted to Standard ML (`SML`). Exposed concrete
  soundness bugs in unverified `VAL` and `INVAL` handling of schematic types and
  duplicate precondition/effect interactions.
- **`Fast Downward` Unsolvability Certificates & `helve` (`aibasel/downward`,
  Eriksson, Röger, & Helmert, ICAPS 2017 / 2018):** Extends the `Fast Downward`
  planning system to emit machine-checkable **unsolvability certificates** (proof
  trees of inductive state-set invariants $I$ represented as BDDs, Horn clauses,
  or union/progression steps proving $s_0 \in I$, $\text{succ}(I) \subseteq I$,
  and $I \cap G = \emptyset$). The standalone certificate checker `helve`
  verifies these proof logs independently of the heuristic search engine.
- **`PANDA` / `pandaPIValidator` (`panda-planner-dev/pandaPIValidator`, Höller,
  Behnke, Bercher, & Biundo, Ulm University) & `SHOP3` (`shop-planner/shop3`,
  Goldman & Kuter, SIFT):** Hierarchical Task Network (`HTN`) systems. `PANDA`
  parses `HDDL` (Hierarchical Domain Definition Language) and `pandaPIValidator`
  verifies that a primitive action sequence can be derived from the initial
  abstract task network via a valid tree of method decompositions (reducing HTN
  plan validation to context-free grammar parsing / CYK-style chart parsing).
  `SHOP3` is a Common Lisp ordered-task-network planner supporting numeric rules
  and theorem-proving axioms.
- **`PRP` (*Planner for Relevant Policies*, Muise, McIlraith, & Beck, ICAPS
  2012):** State-of-the-art `FOND` planner that compiles non-deterministic
  actions (`oneof (effect_1) (effect_2)`) into classical replanning queries and
  synthesizes compact **strong-cyclic policy graphs** guaranteed to reach the
  goal under fair demonic environment nondeterminism without entering inescapable
  dead-end traps.
- **`Unified Planning` (`aiplan4eu/unified-planning`, AIPlan4EU) & `ENHSP` /
  `POPF` (Scala et al., Coles et al.):** `Unified Planning` is a Python middle-end
  providing a typed AST for classical, numeric, temporal, and hierarchical
  planning with uniform compilation passes (such as removing conditional effects
  or grounding) and multi-validator dispatch (`VAL`, `tamer`, `aries`). `ENHSP`
  (*Expressive Numeric Heuristic Search Planner*) and `POPF` (*Partial-Order
  Planning Forwards*) solve non-linear numeric and continuous temporal `PDDL+`
  domains.
- **`LLM-Modulo` Frameworks (Kambhampati et al., ICML 2024, *"LLMs Can't Plan,
  But Can Help Planning in LLM-Modulo Frameworks"*):** Formalizes the
  generate-test-critique loop where autoregressive LLMs propose candidate plans,
  domain models, or decompositions, and sound symbolic critics (`VAL`,
  `pandaPIValidator`, SMT solvers) either certify the candidate or return minimum
  unsatisfied precondition/invariant diagnostics for iterative repair.

#### 3. Design Philosophy and Tradeoffs
Classical planners (`Fast Downward`) and `LLM-Modulo` generators optimize for
search speed using aggressive state abstractions, delete relaxations ($h^+$),
landmark heuristics, or neural priors—techniques that are complex and error-prone.
Decoupling **plan search** from **plan validation** (`VAL`, Abdulaziz & Lammich's
Isabelle validator, `pandaPIValidator`, `helve`) shrinks the trusted code base
by two orders of magnitude: verifying a candidate sequential plan of length $k$
takes $O(k)$ state transitions, verifying an `HTN` decomposition takes
polynomial parsing time, and checking a `helve` unsolvability certificate avoids
trusting `Fast Downward`'s C++ search heuristics.

#### 4. Ecosystem Comparisons
- **Unverified C++ (`VAL`) vs. Mechanized HOL (`Abdulaziz & Lammich`):** `VAL`
  supports the broadest `PDDL 2.1/3.0/+` surface syntax (including continuous
  ODE/linear processes), whereas the Isabelle/HOL validator sacrifices continuous
  `PDDL+` features to guarantee kernel-checked soundness on grounded and
  schematic discrete `PDDL` / `SAS+`.
- **Sequential Validation (`VAL`) vs. Hierarchical Validation
  (`pandaPIValidator`):** In `HTN` planning, a plan that satisfies all primitive
  action preconditions and achieves the state goal $G$ can still be **invalid**
  if it violates the hierarchical method grammar (for example, delivering a
  package without following the mandated security-inspection subtask protocol);
  `pandaPIValidator` verifies the refinement derivation tree itself.

#### 5. Formal Theory and TCB Analysis
- **Operational Semantics:** State-transition systems $\langle S, s_0, G, A
  \rangle$ where action $a = (\text{pre}, \text{del}, \text{add})$ is applicable
  in $s$ iff $\text{pre} \subseteq s$, yielding $s' = (s \setminus \text{del})
  \cup \text{add}$ (with well-definedness conditions on simultaneous add/delete
  and parallel non-interference).
- **HTN Refinement:** Formal language inclusion between the yield of a
  partially ordered task network $(T, \prec, \alpha)$ under method rules $M$ and
  executable traces of the underlying transition system.
- **TCB:** For `Abdulaziz & Lammich`, the TCB is the Isabelle/HOL kernel, code
  generator, and SML runtime; for `Fast Downward + helve`, the TCB is the
  `PDDL`-to-`SAS+` grounder plus the `helve` BDD/Horn certificate checker.

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `HTNLang.Prog` / `GoalSpecLang.Prog`: High-level compound task network
    (`HDDL`) or declarative goal/trajectory specification.
  - `PDDLLang.Prog`: Grounded sequential, temporal (`POPF`/`ENHSP`), or `FOND`
    policy (`PRP`) schedule.
  - `Query`: Initial world state $s_0$ (propositional facts + numeric fluents).
  - `Out` & `SemObs` (`obs`): `EventualOut ActionTrace FinalWorldState`; `obs`
    projects to goal satisfaction (`GoalReached : Bool`), milestone sequence,
    and cost/makespan bound.
  - `Partial.ub` (`defined = False`): Executing any action $a_i$ whose
    precondition fails in current state $s_{i-1}$, concurrent mutex interference
    in temporal `PDDL 2.1`, violation of a `PDDL 3.0` `always` trajectory
    constraint, or numeric division by zero.
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Compiles HTNLang PDDLLang codec compoundTask primitivePlan`: **HTN task
    decomposition (`PANDA` / `pandaPIValidator` / `SHOP3`) is directly
    `Compiles`!** The primitive plan refines the compound task specification,
    preserving all trajectory invariants (`defined`) and milestone observations
    (`obs_decodeOut`).
  - `Abstracts InductiveInvariantLang PDDLLang codec helveCert domain`:
    **Unsolvability certificates (`helve`) are directly `Abstracts`!** The
    certificate language over-approximates the reachable state set via inductive
    invariant $I \supseteq \text{Reach}(s_0)$ and proves $I \cap G = \emptyset$.
  - `decodeOut = none`: Rejects physically inconsistent world states violating
    domain mutex axioms (e.g., `at(rover, A) ∧ at(rover, B)` for $A \neq B$).
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **$1 \to k$ HTN Expansion via `EventualBehaviorOf`:** A single abstract
    compound task in `HTNLang` expands to $k$ primitive actions in `PDDLLang`;
    `EventualBehaviorOf` compares the completed trace outcomes without artificial
    step-index alignment.
  - **Blocks dead-end plans and vacuous initial states:** `InhabitedPre` proves
    $s_0$ satisfies static domain invariants, and `ProductiveOn` proves the plan
    reaches a valid goal state rather than stalling or looping forever.
  - **`StepResult.externalCall boundaryInv branches`:** Captures `FOND` (`PRP`)
    contingent planning: `boundaryInv` verifies action preconditions, and
    `branches` models the environment's demonic `oneof` outcome selection.
- **`VerificationResult` & `TrustPolicy`:**
  - Implements **LLM-Modulo (`Kambhampati et al.`)**: an untrusted LLM proposes
    a candidate plan or `HTN` refinement; Anneal's Lean kernel runs an
    `Abdulaziz & Lammich`-style verified checker to discharge
    `Obligation.planValid` with zero waivers on the LLM itself.

Basis: normative + documentation + source + derived.

---

### 3.5 Domain 4: CAD/CSG Solid Modeling, E-Graph Decompilers, and CNC/3D-Printing G-Code Slicers

#### 1. Goals and Target Users
Computational geometry kernels, CAD compilers/decompilers, CNC machining
verifiers, and 3D-printing slicers translate between high-level solid models
(Constructive Solid Geometry `CSG`, implicit Signed Distance Fields `SDF`s /
`F-Rep`, and watertight boundary meshes `B-Rep`) and physical machine toolpaths
(`G-00`/`G-01`/`G-02`/`G-03` G-code). Target users include mechanical and aerospace
manufacturing engineers (preventing 5-axis CNC spindle crashes and part
gouging), additive manufacturing engineers, and programming-languages researchers
building verified geometry pipelines.

#### 2. Concrete Tool Lineage and Technical Architecture
- **`Reincarnate` / `λCAD` (`uwplse/reincarnate`, Nandi et al., ICFP 2018),
  `Szalinski` (`uwplse/szalinski`, Nandi, Willsey, Anderson, Danh, Darulova,
   Pothier, & Tatlock, PLDI 2020), & `Caviar` (Kourta et al., OOPSLA 2022):**
  The UW PLSE verified CAD and e-graph lineage. In *Functional Programming for
  Compiling and Decompiling Computer-Aided Design* (ICFP 2018), Nandi et al.
  formalize **`λCAD`**, a functional CSG language, and prove in **Rocq/Coq** the
  correctness of a CSG-to-triangle-mesh compiler before building `Reincarnate`
  to decompile raw 3D printer triangle meshes back into `λCAD` programs.
  `Szalinski` uses `egg` equality saturation and inverse affine transformations
  to compress flat, repetitive CSG trees output by `Reincarnate` into structured
  programs with `Tabulate`/`Map`/`Fold` loops. `Caviar` (OOPSLA 2022) implements
  a verified e-graph term-rewriting system in **Rocq/Coq** (targeting algebraic
  and `Halide`-style compiler rewrites) to eliminate e-graph rewrite soundness
  bugs.
- **`Fidget` (`mkeeter/fidget`) & `Libfive` (`libfive/libfive`, Matt Keeter):**
  High-performance functional representation (`F-Rep`) and implicit surface
  evaluation kernels ($f(x, y, z) \le 0$). `Libfive` and `Fidget` (in Rust)
  compile deep CSG expression DAGs into SIMD/JIT/VM bytecode evaluated over
  adaptive **3D Interval Arithmetic (`IA`)** and **Affine Arithmetic** octrees,
  pruning empty (`f > 0`) and solid (`f < 0`) octree cells analytically and
  specializing active expression subtrees ("tape pushing") as subdivision
  descends.
- **`Manifold` (`elalish/manifold`, Emmett Lalish / Google) & `OpenSCAD`
  (`openscad/openscad`) / `ImplicitCAD` / `Curv` (`curv3d/curv`):** `Manifold`
  replaces brittle CGAL exact-rational Nef polyhedra with a topological
  **guaranteed-manifold** mesh boolean algorithm that separates combinatorial
  mesh topology (exact integer edge/face connectivity) from floating-point
  vertex geometry, achieving $100\times$–$1000\times$ speedups in `OpenSCAD`
  while guaranteeing watertight 2-manifold output. `ImplicitCAD` (in Haskell)
  and `Curv` (by Doug Moen, compiling functional SDFs to GLSL/SPIR-V) represent
  solids as exact implicit functions with rounded CSG booleans.
- **`VERICUT` (CGTech), `NCSimul` (Hexagon), `CAMotics`
  (`CauldronDevelopmentLLC/CAMotics`), & `LinuxCNC` (`LinuxCNC/linuxcnc`):**
  Subtractive CNC verification and real-time motion control. `VERICUT` and
  `NCSimul` are industrial digital-twin simulators that parse post-processed
  machine G-code (`Fanuc`, `Siemens 840D`, `Heidenhain`), simulate full 5-axis
  machine-tool kinematics and dexel/voxel swept-volume material removal, and
  detect **gouging** (cutter penetrating design solid), **holder/spindle
  collisions** with stock or fixtures, and **rapid-traverse (`G-00`) stock
  impacts**. `CAMotics` provides open-source 3-axis octree/isosurface swept-volume
  simulation. `LinuxCNC` runs a hard-real-time trajectory planner (`tp`) that
  enforces trapezoidal acceleration and blending tolerances (`G-64 Pq`) across
  coupled kinematic joints.
- **`PrusaSlicer` (`prusa3d/PrusaSlicer`), `OrcaSlicer`, `Cura` (`Ultimaker/CuraEngine`),
  `IceSL` (Inria/LORIA, Lefebvre et al.), & `FullControl GCode`
  (`FullControlXYZ/fullcontrol`, Gleadall, Loughborough Univ.):** Additive
  manufacturing slicers and direct toolpath compilers. `PrusaSlicer`,
  `OrcaSlicer`, and `CuraEngine` slice 3D meshes into planar 2D polygon layers
  (`Clipper2` integer polygon clipping), generate perimeters, infill, and
  support trees for overhangs exceeding critical angle $\theta_{\max}$, and
  regulate volumetric flow ($E \times F$). `IceSL` combines a Lua CSG/implicit
  modeler with GPU-accelerated slicing and progressive infill. `FullControl`
  bypasses mesh slicing entirely, compiling mathematical parametric curves
  directly into non-planar 3D G-code with explicit extrusion-width/height state
  tracking.

#### 3. Design Philosophy and Tradeoffs
- **B-Rep / Triangle Meshes (`Manifold`, `PrusaSlicer`) vs. F-Rep Interval
  Octrees (`Fidget`, `Libfive`, `Curv`):** Triangle meshes suffer from
  self-intersection, non-manifold edges, and discretization error prior to
  slicing (`Manifold` solves topological validity via topological Symbolic
  Perturbation), whereas `Fidget`/`Libfive` evaluate exact mathematical
  surfaces via Interval Arithmetic ($f([x_{\min}, x_{\max}], \dots) \subseteq
  [l, u]$), providing **sound conservative spatial bounds** ideal for formal
  collision and gouge verification.
- **Mesh Slicing (`PrusaSlicer`) vs. Direct Toolpath Compilation
  (`FullControl`):** Slicing via intermediate `.stl` triangle meshes loses
  semantic intent (thread pitches, thin-wall structural grain, non-planar layer
  normal vectors), whereas `FullControl` preserves parametric intent directly to
  G-code.

#### 4. Ecosystem Comparisons
- **Verified CAD Compilation (`λCAD` in Rocq & `Caviar`) vs. Unverified E-Graph
  Decompilation (`Szalinski`):** `λCAD` proves forward compilation from CSG to
  meshes in Rocq, and `Caviar` verifies e-graph rewrites in Rocq, whereas
  `Szalinski` uses unverified `egg` rules and floating-point inverse-matrix
  solvers that require downstream geometric equivalence checking.
- **Industrial CNC Digital Twins (`VERICUT`) vs. Analytical Interval Certifiers:**
  `VERICUT` discretizes stock into high-resolution dexel/voxel grids (fast on
  GPUs, but subject to grid-aliasing tolerance $\delta$), whereas pairing
  `Fidget`-style 3D interval arithmetic with swept-volume envelopes yields
  mathematically sound continuous collision freedom.

#### 5. Formal Theory and TCB Analysis
- **Set-Theoretic Solid Modeling (Requicha, 1980):** Solids are regularized
  closed subsets of $\mathbb{R}^3$ ($S = \text{closure}(\text{interior}(S))$)
  under regularized Boolean operations ($\cup^*, \cap^*, \setminus^*$).
- **Interval Inclusion Monotonicity (`Fidget` / `Libfive`):** For any interval
  box $B \subseteq \mathbb{R}^3$, the interval extension $F(B)$ satisfies
  $\{f(p) \mid p \in B\} \subseteq F(B)$; hence $0 \notin F(B)$ constitutes a
  sound mathematical proof that the surface $f(p) = 0$ does not intersect $B$.
- **TCB:** In `λCAD` / `Caviar`, the TCB is the Rocq kernel; in `Manifold`,
  `Fidget`, and `VERICUT`, the TCB includes the C++/Rust floating-point/interval
  evaluators and G-code parser.

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `CSGLang.Prog`: Declarative `λCAD` / `Fidget` F-Rep solid $S \subseteq
    \mathbb{R}^3$ with engineering tolerance band $[S_{-\delta}, S_{+\delta}]$.
  - `GCodeLang.Prog`: Concrete CNC (`LinuxCNC`) or 3D-printer (`PrusaSlicer` /
    `FullControl`) G-code instruction sequence.
  - `Query`: Initial stock volume $V_{\text{stock}}$, fixture/clamp volumes
    $V_{\text{fixture}}$, machine kinematic limits, and spatial voxel/box probe.
  - `Out` & `SemObs` (`obs`): `EventualOut MachineTelemetry (FinalVolume ×
    ToolHeadState)`; `obs` extracts the final physical occupancy classification
    and peak mechanical/thermal telemetry envelope.
  - `Partial.ub` (`defined = False`):
    1. **CNC (`VERICUT` / `LinuxCNC`):** Spindle holder/shaft collision with
       stock or fixtures ($V_{\text{holder}}(t) \cap (V_{\text{stock}}(t) \cup
       V_{\text{fixture}}) \neq \emptyset$), rapid-traverse (`G-00`) stock
       impact, part gouging ($V_{\text{swept}}(t) \cap S_{-\delta} \neq
       \emptyset$), or joint velocity/acceleration violation.
    2. **3D Printing (`PrusaSlicer` / `FullControl`):** Extruding an unsupported
       overhang voxel beyond critical angle $\theta_{\max}$, travel-move nozzle
       crash into printed geometry, or volumetric flow exceeding hotend melt
       capacity.
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Compiles CSGLang GCodeLang codec csgSpec gcodeProg`: Certifies that the
    slicer or CAM post-processor produces a crash-free toolpath whose machined
    or printed volume refines the tolerance band $[S_{-\delta}, S_{+\delta}]$.
  - `Compiles CSGLang CSGLang idCodec rawCsg szalinskiCsg`: Certifies horizontal
    e-graph CAD rewrites (`Szalinski` / `Caviar`).
  - `Abstracts IntervalOctreeLang GCodeLang codec fidgetOctree gcodeProg`:
    Uses `Fidget`/`Libfive` 3D interval arithmetic and swept-volume octrees to
    soundly over-approximate toolpath occupancy and prove disjointness from
    fixtures and inner design surfaces.
  - `decodeOut = none`: Rejects non-2-manifold meshes (violating `Manifold`'s
    Euler-characteristic/edge-pairing invariant) or G-code executions that leave
    the spindle un-retracted (`False`).
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **$1 \to 50{,}000$ Step Decoupling via `EventualBehaviorOf`:** A single CSG
    cylinder node in `CSGLang` compiles to $50{,}000$ `G-01` micro-segments in
    `GCodeLang`; `EventualBehaviorOf` verifies prefix safety (`defined`) at all
    $50{,}000$ micro-steps and matches the final geometry at termination.
  - **Blocks the "Air-Cutting / Empty `M-30`" Goodhart Loophole:** An agent asked
    to synthesize "100% crash-free CNC G-code" can emit `M-30` (program end, zero
    cuts) and satisfy `defined = True` trivially. `ProductiveOn` +
    `obs_decodeOut` forces the toolpath to remove stock until the final volume
    lies inside $[S_{-\delta}, S_{+\delta}]$.
  - **`StepResult.externalCall boundaryInv branches`:** Models in-process CNC
    touch-probe cycles (`G-38.2` in `LinuxCNC`), where `boundaryInv` checks safe
    probing approach velocity and `branches` models stock surface variation.
- **`VerificationResult` & `TrustPolicy`:**
  - Isolates floating-point chordal approximation or decorative fillet waivers
    in `waived` while requiring zero-waiver interval proofs for `.noFixtureClash`
    and `.noSpindleGouge`.

Basis: normative + documentation + source + derived.

---

### 3.6 Domain 5: Programmable Textiles (`Knitout`), Sheet-Metal Bending, and Rigid Origami Kinematics

#### 1. Goals and Target Users
Computational textile, sheet-metal, and origami toolchains compile 3D surfaces
and topological crease/stitch graphs into sequential kinematic instructions for
industrial V-bed knitting machines (`Shima Seiki`, `Stoll`), CNC press brakes
(`Trumpf`, `Amada`), and deployable origami structures. Target users include
computational fabrication engineers, textile/apparel CAD developers, aerospace
deployable-array designers, and sheet-metal manufacturing engineers.

#### 2. Concrete Tool Lineage and Technical Architecture
- **`knitout` (`textiles-lab/knitout`), `Autoknit` (`textiles-lab/autoknit`,
  McCann, Albaugh, Narayanan, Hodgins et al., CMU Textiles Lab, SIGGRAPH 2016 /
  2018), & `KnitSpeak` / `KnitPick` (Hofmann, Wu, et al.):**
  - **`knitout` (`.k`):** The portable low-level assembly specification for
    computer-controlled V-bed latch-needle knitting machines. Defines atomic
    machine instructions over front/back needle beds (`fN`, `bN`), racking offset
    $R \in \mathbb{Z}$ (`rack R`), and yarn carriers $c_i$: `inhook`, `releasehook`,
    `out`, `knit d n cs` (pull new loop through existing loops on needle $n$ in
    direction $d \in \{+, -\}$), `tuck d n cs` (add unknitted loop to needle),
    `split d n n2 cs`, `xfer n n2` (transfer all loops from needle $n$ to
    opposing bed needle $n_2$ aligned under current rack $R$), and `drop n`.
  - **`Autoknit`:** Compiles arbitrary 3D triangle meshes into time-aligned
    **stitch meshes** and schedules them onto two-bed `knitout` instructions via
    a collapse-expand-transfer planning algorithm that tracks yarn carrier paths
    and front/back bed needle allocations.
  - **`KnitSpeak`:** A domain-specific language formalizing hand-knitting cable
    and lace notation (`K2tog`, `SSK`, `YO`), parsed into topological
    `KnitGraph` DAGs and compiled down to `knitout` with topological validation.
- **`Radbend` (Hexagon / RADAN) & `TruTops Bend` (TRUMPF):** Industrial
  sheet-metal press-brake CAM compilers. Given a 3D sheet-metal enclosure with
  $N$ flanges, they compute the 2D flat laser-cut blank (applying neutral-axis
  **$K$-factor / Bend Deduction** material stretching formulas) and search over
  the $N!$ bend sequences, punch/die tool profiles, and backgauge finger stop
  positions to find a sequence free of **part-to-punch**, **part-to-die**,
  **part-to-frame**, and **self-flange collisions**, as well as **captive tool
  entrapment** (folding a box around the upper punch so the part cannot be
  removed).
- **`FOLD` (`edemaine/fold`, Demaine, Ku, et al.), `Origami Simulator`
  (`amandaghassaei/OrigamiSimulator`, Ghassaei, Demaine, & Gershenfeld, 2018),
  & `Freeform Origami` (Tomohiro Tachi):**
  - **`FOLD` (*Flexible Origami List Datastructure*):** The standard JSON graph
    schema representing crease patterns (`vertices_coords`, `edges_vertices`,
    `edges_assignment` $\in \{M, V, B, F, U\}$, `edges_foldAngle`, and
    layer-ordering `faceOrders` preventing self-intersection).
  - **`Origami Simulator` & `Freeform Origami`:** Simulate and optimize
    continuous rigid and compliant folding trajectories. `Freeform Origami`
    enforces exact **developability** (Gaussian curvature $\sum \theta_i = 2\pi$
    at every interior vertex) and **local flat-foldability** (Kawasaki's theorem
    $\sum (-1)^i \theta_i = 0$ and Maekawa's theorem $|M - V| = 2$) via
    constrained differential projection so rigid polygonal facets fold without
    stretching or shearing.

#### 3. Design Philosophy and Tradeoffs
In all three fabrication domains, the **target artifact is topological/geometric**,
whereas the **machine execution is heavily state-constrained**:
- On a V-bed knitting machine (`knitout`), a tubular 3D surface must be embedded
  onto two flat 1D rows of steel needles (`front` and `back`). Moving stitches
  left or right by 1 needle to shape a sleeve (`short-row` / `decrease`)
  requires transferring loops to the opposite bed (`xfer`), racking the bed
  laterally (`rack`), and transferring back—while never racking so far that
  adjacent held loops stretch beyond $2$ needle pitches and snap the yarn or
  bend steel needles.
- In sheet-metal bending (`Radbend`) and rigid origami (`Freeform Origami`),
  the initial flat sheet and final 3D shape may both be valid, yet the
  **homotopy path** (bend order or continuous fold trajectory $\theta(t) \in
  [0, 1]$) can self-intersect or trap the press-brake punch.

#### 4. Ecosystem Comparisons
- **Proprietary Machine Formats (`Shima Seiki .dat`, `Stoll M1plus`) vs.
  `knitout`:** Proprietary formats entangle topological intent with machine-specific
  carriage cam passes; `knitout` isolates a clean, deterministic abstract
  state machine of needle loops and carrier positions that can be statically
  verified before translating to `.dat` or `.sin`.
- **Compliant Spring Simulation (`Origami Simulator`) vs. Rigid Kinematic
  Projection (`Freeform Origami`):** `Origami Simulator` relaxes facets into
  compliant axial/hinge springs on a GPU (fast visual exploration, allows slight
  facet stretching), whereas `Freeform Origami` enforces strict isometric
  rigid-panel constraints required for thick-panel aerospace origami.

#### 5. Formal Theory and TCB Analysis
- **Knitting Machine Operational Semantics (`knitout`):** State $\sigma =
  (\text{Loops} : \text{Bed} \times \mathbb{Z} \to \text{List LoopId},\;
  \text{CarrierPos} : \text{Carrier} \to \mathbb{Z},\; R \in \mathbb{Z},\;
  \text{StitchDAG})$. Safety invariants require bounded loop-to-loop needle
  pitch distance $|\text{pos}(u) - \text{pos}(v)| \le \Delta_{\max}$ across all
  edges $(u, v) \in \text{StitchDAG}$ currently held on needles, needle stack
  depth $\le k_{\max}$, and zero unknitted `drop` of live structural loops.
- **Origami Theorems:** **Kawasaki–Justin Theorem** (a single-vertex crease
  pattern is flat-foldable iff alternating sector angles sum to $\pi$),
  **Maekawa–Justin Theorem** ($|M - V| = 2$), and **Justin's Non-Crossing
  Layer Ordering Conditions** (encoded in `FOLD` `faceOrders` to forbid tacos
  intersecting tacos and tortillas intersecting tacos).

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `StitchGraphLang.Prog` / `FOLDLang.Prog`: High-level `KnitSpeak`/`Autoknit`
    stitch-loop topology or `FOLD` crease graph with target fold angles.
  - `KnitoutLang.Prog` / `PressBrakeLang.Prog`: Concrete `.k` `knitout` bytecode
    or `Radbend` press-brake bend sequence.
  - `Query`: Initial needle-bed and yarn carrier configuration, or flat 2D sheet
    blank and punch/die tooling geometry.
  - `Out` & `SemObs` (`obs`): `EventualOut FabricationTrace FinalArtifact`.
    Crucially, `obs` computes the **canonical unlabeled stitch-graph topology**
    (erasing which physical needle number `f5` vs. `b7` temporarily held a loop
    during `xfer` shuffles!) or final 3D flange/facet pose graph.
  - `Partial.ub` (`defined = False`):
    1. **`Knitout`:** Dropping a live loop without binding it off (`drop` on
       non-waste yarn), racking while a loop connected across beds or adjacent
       needles exceeds maximum stretch pitch (yarn snap / needle bend), exceeding
       needle hook capacity, or yarn carrier collision.
    2. **`Radbend` / `FOLD`:** Intermediate flange-to-punch/die collision,
       self-intersection of non-adjacent faces (`faceOrders` cycle violation),
       captive tool lockup, or violation of Kawasaki/Maekawa developability.
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Compiles StitchGraphLang KnitoutLang codec stitchMesh knitoutBytecode`:
    **Certifies `Autoknit` / `KnitSpeak` compilation!** Proves that the scheduled
    sequence of `knit`, `tuck`, `rack`, and `xfer` instructions is needle-safe
    (`defined`) and produces a physical fabric whose stitch topology is
    isomorphic to `stitchMesh` (`obs_decodeOut`).
  - `decodeOut = none`: Rejects any final `Knitout` state where live loops
    remain stranded on the needle bed at program end (incomplete cast-off) or
    any `FOLD` state with violated layer ordering (`False`).
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **$1 \to 12$ Transfer Macro Verification via `EventualBehaviorOf`:**
    Decreasing or shifting a stitch row by 1 needle in `Autoknit` expands to a
    multi-step schoolbus `xfer` $\to$ `rack` $\to$ `xfer` cycle in
    `KnitoutLang`; `EventualBehaviorOf` verifies that the macro completes safely
    and achieves the net topological shift.
  - **`ProductiveOn`:** Blocks transfer schedulers or press-brake planners that
    abort mid-garment/mid-box due to deadlocked needle or flange configurations.
- **`VerificationResult` & `TrustPolicy`:**
  - Separates exact topological loop-preservation and needle-span proofs from
    empirical material waivers (such as `.yarnElasticModulusWithinSpec` or
    sheet-metal `.kFactorSpringbackCalibration`).

Basis: normative + documentation + source + derived.

---

### 3.7 Domain 6: Civil/Structural Engineering, BIM/IFC Building-Code Compliance, and Topology Optimization

#### 1. Goals and Target Users
Civil, architectural, and structural verification tools validate digital
Building Information Models (`BIM` encoded in `ISO 16739` Industry Foundation
Classes `IFC`) and finite-element structural meshes against statutory building
codes (`IBC`, `NFPA 101` Life Safety Code, `ADA` accessibility, `NEC` electrical
ampacity), 3D Mechanical/Electrical/Plumbing (`MEP`) clash freedom, emergency
fire-egress reachability, and structural load/buckling stability. Target users
include structural engineers of record, architectural code-compliance auditors
(`AHJ` reviewers), MEP BIM coordinators, and generative civil-design engineers.

#### 2. Concrete Tool Lineage and Technical Architecture
- **`Solibri Office` (`Solibri Model Checker`, Nemetschek) & `IfcOpenShell` /
  `ifctester` (`IfcOpenShell/IfcOpenShell`, Krijnen et al.):**
  - **`Solibri`:** The flagship commercial BIM rule engine executing
    parameterized spatial and topological rule sets (`SOL/208` Accessible Door
    Rule, `SOL/209` Accessible Stair & Ramp Rule, `SOL/1` 3D Clash Detection
    between structural steel and HVAC/fire-sprinkler trees, and egress
    travel-distance pathfinding over `IfcSpace`/`IfcDoor` graphs).
  - **`IfcOpenShell` & `ifctester`:** The open-source C++/Python geometry and
    validation toolkit implementing the buildingSMART **Information Delivery
    Specification (`IDS` 1.0)** standard. `ifctester` validates `IFC2x3`/`IFC4`/`IFC4.3`
    models against declarative XML/IDS facet contracts (`Entity`, `Attribute`,
    `Property`, `Material`, `Classification`, `PartOf` spatial hierarchy) and
    exports `BCF` (*BIM Collaboration Format*) audit reports.
- **`KBimCode` & `BERA` (*Building Environment Rule and Analysis*, Lee,
  Eastman, et al., Georgia Tech / Hanyang Univ.):** A domain-specific language
  (`BERA`) and compiler (`KBimCode`) designed to translate natural-language
  statutory building codes (such as Korean Building Act clauses and `IBC`
  spatial tables) into executable first-order spatial queries over BIM space
  topologies (`Space`, `Wall`, `Door`, circulation graphs, fire-compartment
  boundaries).
- **`FDS + Evac` (`firemodels/fds`, NIST *Fire Dynamics Simulator* + VTT
  Technical Research Centre of Finland) & `Pathfinder` (Thunderhead
  Engineering):** Coupled fire-and-agent-evacuation simulators. `FDS` solves
  low-Mach-number Navier–Stokes equations for smoke, heat, and toxic gas (`CO`,
  `HCN`, radiative flux, visibility obscuration) transport, while `Evac` and
  `Pathfinder` simulate thousands of autonomous occupants navigating room/door/stair
  graphs via Helbing social-force or steering dynamics to verify that **Available
  Safe Egress Time (`ASET`) strictly exceeds Required Safe Egress Time (`RSET`)**
  ($\text{ASET} - \text{RSET} \ge \Delta t_{\text{safety}}$) before tenability
  limits are breached.
- **`OpenSees` (`OpenSees/OpenSees`, McKenna, Fenves, & Scott, PEER Berkeley) &
  Interval Finite Element Methods (`Interval FEM`, Muhanna & Mullen):**
  `OpenSees` (*Open System for Earthquake Engineering Simulation*) models
  nonlinear structural frames, fiber-section beam-columns, and soil-structure
  interaction under static and seismic ground-motion loads ($M\ddot{u} +
  C\dot{u} + R(u) = F(t)$). **Interval FEM (`IFEM`)** replaces crisp material
  moduli $E \in [E_{\min}, E_{\max}]$ and load vectors $F \in [\underline{F},
  \overline{F}]$ with interval matrices ($K(\alpha) u = F$) solved via
  element-by-element (`EBE`) preconditioning and Krawczyk/Rump interval linear
  system enclosures to bound worst-case displacements and stresses across all
  parameter uncertainties.
- **`TopOpt` (Sigmund 2001, `topopt/TopOpt_in_PETSc`, Aage et al.):**
  Solid Isotropic Material with Penalization (`SIMP`) topology optimization
  engines that distribute a bounded volume fraction $V \le V_{\max}$ across a
  design domain $\Omega$ to minimize compliance $c(\rho) = U^\top K(\rho) U$
  subject to equilibrium $K(\rho) U = F$, minimum length-scale PDE filters
  (preventing checkerboard mesh pathologies), and stress/buckling constraints.

#### 3. Design Philosophy and Tradeoffs
- **Schema/Property Checking (`ifctester`/`IDS`) vs. Topological/Geometric Rule
  Checking (`Solibri`, `BERA`):** `IDS` and `ifctester` verify that every
  `IfcDoor` carries a `FireRating` property and minimum `Width` attribute in
  milliseconds, but cannot verify 3D solid non-intersection or multi-room
  corridor escape paths without a geometric kernel (`IfcOpenShell` OpenCascade /
  CGAL geometry engine or `Solibri` octree/A* pathfinder).
- **Deterministic Code Tables (`IBC` Travel Distance) vs. Performance-Based
  Simulation (`FDS + Evac` / `Pathfinder`):** Prescriptive code rules (`Solibri`
  / `KBimCode`: max travel distance $\le 250\text{ ft}$, minimum two independent
  exits when occupancy $\ge 50$) are decidable graph properties, whereas
  performance-based fire engineering (`FDS + Evac`) handles complex atriums and
  stadiums at the cost of CFD discretization and crowd-parameter uncertainty.

#### 4. Ecosystem Comparisons
- **`Solibri` vs. `IfcOpenShell`/`ifctester`:** `Solibri` provides a rich suite
  of built-in geometric/egress rules in a closed commercial engine;
  `IfcOpenShell` + `ifctester` provides an open, scriptable C++/Python kernel
  standardized around buildingSMART `IDS`.
- **Unverified `TopOpt` vs. Interval `FEM` (`IFEM`) Certification:** Gradient-based
  `TopOpt` (`SIMP`) can produce thin hinge-like members that appear optimal under
  a single nominal load vector $F$ yet buckle catastrophically under slight load
  angle perturbations or manufacturing thickness tolerances; verifying the
  optimized mesh with `IFEM` certifies worst-case stress and Euler buckling
  across the entire load/tolerance box.

#### 5. Formal Theory and TCB Analysis
- **Graph Reachability & $N-1$ Fault Tolerance (Egress):** Let $G = (V_{\text{spaces}},
  E_{\text{doors}})$ be the building circulation graph. Egress compliance
  requires that from every habitable room $v \in V$, under any single blocked
  non-pressurized corridor segment $e_{\text{fire}} \in E$, there exists a path
  $\pi$ in $G \setminus \{e_{\text{fire}}\}$ to an exterior `IfcExit` with
  length $\sum_{e \in \pi} d(e) \le D_{\max}$ and capacity $\min_{e \in \pi}
  w(e) \ge \text{Occ}(v) \cdot c_{\text{factor}}$.
- **Interval Linear Systems (Rump / Krawczyk Inclusion):** Given interval
  stiffness matrix $[K]$ and load $[F]$, an interval displacement vector $[u]$
  is verified if the Krawczyk operator maps $[u]$ strictly inside its own
  interior, proving simultaneously that every $K \in [K]$ is non-singular (the
  structure is not a kinematic mechanism!) and $K^{-1} F \in [u]$.

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `ArchProgramLang.Prog`: Declarative architectural space program, occupancy
    loads, and structural/MEP service specifications.
  - `BIMLang.Prog`: Concrete 3D `IFC` building model (`IfcSpace`, `IfcDoor`,
    `IfcWall`, structural frame, and MEP routing trees) or `TopOpt` mesh.
  - `Query`: Full rated room occupancy distribution + single-corridor fire/smoke
    contingency (`FDS + Evac`), or `IBC`/`ASCE 7` structural load combination
    ($1.2D + 1.6L + 0.5S$) and peak MEP fixture demand.
  - `Out` & `SemObs` (`obs`): Evacuation clearance trace (`RSET` per room) or
    structural stress/deflection distribution; `obs` extracts room program
    satisfaction, maximum egress time bucket, and structural safety factors.
  - `Partial.ub` (`defined = False`):
    1. **Life Safety (`Solibri` / `KBimCode` / `Pathfinder`):** Any occupant
       trapped in a dead-end corridor without an exterior exit path, travel
       distance $> D_{\max}$, door swinging against egress for $\ge 50$
       occupants, or $\text{RSET} > \text{ASET}$.
    2. **MEP (`Solibri` / `IfcOpenShell`):** 3D solid clash between disjoint
       systems ($V_{\text{duct}} \cap V_{\text{beam}} \neq \emptyset$), gravity
       drain back-slope ($\Delta z / \Delta s > -1/48$), or NEC breaker
       over-current.
    3. **Structural (`OpenSees` / `IFEM` / `TopOpt`):** Singular stiffness
       matrix ($\det K = 0$, unbraced mechanism), von Mises stress exceeding
       allowable yield $\sigma_y / \gamma$, or Euler buckling eigenvalue
       $\lambda_{\text{crit}} \le 1$.
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Compiles ArchProgramLang BIMLang codec spaceSpec ifcModel`: Proves that a
    generative floorplan/MEP layout compiler refines the architectural space
    program into a clash-free, egress-compliant `IFC` model.
  - `Abstracts IntervalFEMLang ContinuousFrameLang codec krawczykCert frame`:
    Certifies via Interval `FEM` (`Abstracts`) that all concrete displacements
    and member stresses across material/load tolerances lie inside the verified
    interval box.
  - `decodeOut = none`: Rejects kinematically unstable structures ($\det K = 0$)
    or disconnected MEP trees (`False`).
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **Blocks the "Windowless Bunker / Zero-Door Room" Goodhart Loophole:** A
    naive compliance rule $\forall d \in \text{Doors},\; \text{width}(d) \ge
    32\text{ in}$ is satisfied vacuously by generating a building with **zero
    doors**, and an egress check is satisfied vacuously by setting room
    occupancy to **zero** (`¬ InhabitedPre`). Requiring `InhabitedPre
    FullRatedOccupancy` and `ProductiveOn FullRatedOccupancy ifcModel` forces
    every occupant in every habitable room to have a constructive, terminating
    evacuation path to the exterior public way!
  - **`StepResult.externalCall boundaryInv branches`:** Captures active fire
    interlocks (alarm triggers damper closure and mag-lock release, checked by
    `boundaryInv`) against demonic smoke spread and crowd routing (`branches`).
- **`VerificationResult` & `TrustPolicy`:**
  - Directly models **Authority Having Jurisdiction (`AHJ`) Building Variances**:
    standard `IBC`/`NFPA 101`/`IDS` clauses are machine-checked obligations,
    while site-specific historical-building variances or performance-based CFD
    assumptions are explicitly recorded in `waived` and audited against
    `TrustPolicy`.

Basis: normative + documentation + source + derived.

---

### 3.8 Domain 7: GPU Shaders, Color-Space Codecs, Typography, and UI Constraint Layout

#### 1. Goals and Target Users
Graphics, color-management, typography, and UI layout engines compile and verify
GPU compute/fragment shaders (`SPIR-V`, `WGSL`, `HLSL`, `Slang`), color-space
transfer pipelines (`OpenColorIO`/`ACES`), vector font hinting bytecode
(`TrueType` VM), and 2D constraint/box layouts (`CSS` Flexbox/Grid, `Cassowary`,
`Knuth–Plass` line breaking). Target users include browser engine developers
(Chromium `Blink`/`Dawn`, Firefox `Gecko`/`wgpu`, WebKit), game/VFX engine
architects, font engineers, and UI framework authors.

#### 2. Concrete Tool Lineage and Technical Architecture
- **`spirv-val` (`KhronosGroup/SPIRV-Tools`), `Naga` (`gfx-rs/wgpu`), & `Tint`
  (`dawn/tint`, Chromium WebGPU):**
  - **`spirv-val`:** The official Khronos validator for `SPIR-V` SSA bytecode,
    enforcing structural CFG dominance, structured control-flow merge headers
    (`OpSelectionMerge`, `OpLoopMerge` required to prevent GPU SIMT reconvergence
    deadlocks), type/pointer storage-class rules, and capability declarations.
  - **`Naga` (in Rust) & `Tint` (in C++):** The WebGPU (`WGSL`) shader compilers
    that parse `WGSL`/`SPIR-V`/`GLSL`, perform static uniformity analysis
    (proving barrier and derivative operations `dpdx` execute only in uniform
    control flow across a workgroup/quad), and inject automatic bounds clamping
    or zeroing so out-of-bounds GPU buffer/texture accesses never read/write
    cross-process VRAM, before lowering to `SPIR-V`, `MSL`, `HLSL`, or `DXIL`.
- **`GPUVerify` (Betts, Chong, Donaldson, Qadeer, & Thomson, OOPSLA 2012),
  `Faial` (`umb-svl/faial`, Cogumbreiro, Lange, Liew, & Zicarelli, CAV 2021),
  & `GraphicsFuzz` (Donaldson et al., OOPSLA 2017):**
  - **`GPUVerify`:** Translates `OpenCL`/`CUDA` SIMT kernels into sequential
    2-thread Boogie programs (`lockstep` pairwise execution) to verify
    data-race freedom (`DRF`) and barrier divergence freedom via SMT (`Z3`/`CVC5`).
  - **`Faial`:** Introduces **Memory Access Protocols** (a behavioral type
    system formalized and proved sound in **Rocq/Coq**) that decouples thread
    indexing from control flow, achieving linear-time compositional `DRF`
    verification on GPU kernels where `GPUVerify` times out.
  - **`GraphicsFuzz`:** Applies metamorphic testing (semantics-preserving
    shader mutations using dead-code injection and opaque predicates) to expose
    miscompilation and GPU `TDR` (*Timeout Detection and Recovery*) hang bugs in
    proprietary mobile/desktop shader compilers.
- **`Slang` (`shader-slang/slang`), `Halide` (`halide/Halide`, Ragan-Kelley et
  al., PLDI 2013), & `Gator` (`cucapra/gator`, Dietrich et al., Cornell Capra,
  OOPSLA 2020):**
  - **`Slang`:** Modular shader compiler supporting checked generics interfaces
    and automatic forward/backward differentiation (`[Differentiable]`).
  - **`Halide`:** Decouples pure functional image/tensor **algorithms** from
    execution **schedules** (`tile`, `vectorize`, `parallel`, `compute_at`),
    using a large term-rewriting system (`TRS`, partially verified in Coq/SMT
    by Newcomb et al., OOPSLA 2020, and `Caviar`, OOPSLA 2022) to prove bounds
    and simplify index arithmetic without changing pixel values.
  - **`Gator`:** A geometry-typed shader language that encodes coordinate
    reference frames (`model`, `world`, `view`, `clip`) and geometric entities
    (`point`, `vector`, `normal`, `direction`) into a linear/parametric type
    system, statically forbidding spatial frame mixing (e.g., adding a
    world-space vector to a view-space point or transforming a surface normal by
    $M$ instead of $(M^{-1})^\top$).
- **`OpenColorIO` (`AcademySoftwareFoundation/OpenColorIO`, `OCIO v2`) & `ACES`
  (*Academy Color Encoding System*, SMPTE ST 2065-1):** Manages bijective and
  gamut-mapped color-space transformations across scene-referred linear
  primaries (`ACES2065-1` AP0, `ACEScg` AP1) and display-referred spaces (`sRGB`,
  `Rec.2020`, `PQ` ST 2084) via chains of $3\times 3$ matrices, parametric
  transfer curves, and 1D/3D LUTs.
- **`Cassowary` / `Kiwi` (`nucleic/kiwi`, Badros, Borning, & Stuckey, TOCHI
  2001), `Cassius` / `VizAssert` (`uwplse/cassius`, Panchekha, Torlak, et al.,
  PLDI 2018 / OOPSLA 2019), & `Taffy` (`DioxusLabs/taffy`) / `Yoga`
  (`facebook/yoga`):**
  - **`Cassowary` & `Kiwi`:** Incremental dual-simplex linear constraint solvers
    underlying Apple `AutoLayout` and modern UI toolkits, solving systems of
    required (`==`, `<=`, `>=`) and weighted stay/edit linear inequalities with
    deterministic tie-breaking.
  - **`Cassius` & `VizAssert`:** Formalizes the W3C CSS 2.1/Flexbox visual
    formatting model in quantifier-free linear real arithmetic (`QF_LRA` in
    Rosette/Z3) to automatically verify responsive web layouts against visual
    accessibility assertions (no overlapping sibling text, no child clipped
    outside non-scrollable container, consistent alignment across viewport
    widths $W \in [320, 3840]$).
  - **`Taffy` (in Rust) & `Yoga` (in C++):** Cross-platform implementations of
    CSS Flexbox, CSS Grid, and Block layout algorithms.
- **`Knuth–Plass` Line Breaking (Knuth & Plass, *Software: Practice and
  Experience* 1981), `Typst` (`typst/typst`), `FreeType` (`freetype/freetype`),
  & `FontBakery` (`fonttools/fontbakery`):**
  - **`Knuth–Plass` & `Typst`:** Models paragraph justification as dynamic
    programming over `Box`, `Glue` (width $w$, stretch $y$, shrink $z$), and
    `Penalty` items, minimizing total cubed badness $\sum r_l^3 + p_l^3$. `Typst`
    modernizes this pipeline with a pure incremental functional markup compiler
    in Rust.
  - **`FreeType` & `FontBakery`:** `FreeType` executes stack-based `TrueType`
    glyph hinting bytecode (`fpgm`, `prep`, `glyf`) inside a bounded virtual
    machine to grid-fit Bézier outlines at low pixel densities (`ppem`), while
    `FontBakery` runs static QA checks over OpenType tables (`glyf`, `gvar`,
    `STAT`, `cmap`, winding orders, and out-of-bounds contour metrics).

#### 3. Design Philosophy and Tradeoffs
- **WebGPU Sandboxing (`Naga`/`Tint`) vs. Static Proof (`Faial`/`GPUVerify`):**
  Browsers must compile untrusted `WGSL` shaders in milliseconds at page load,
  so `Naga` and `Tint` enforce uniformity statically and inject runtime index
  clamping (`min(idx, len - 1)`) for memory safety; high-assurance compute
  kernels (`Faial`) prove exact index bounds and data-race freedom statically so
  zero runtime clamping overhead is incurred.
- **Imperative Tree Passes (`Taffy`/`Yoga`) vs. Relational SMT Semantics
  (`Cassius`):** `Taffy` executes a fast deterministic multi-pass measure/layout
  tree traversal for a single concrete viewport $(W, H)$, whereas `Cassius`
  encodes the layout relation symbolically in `QF_LRA` to verify properties
  across *all* $(W, H)$ in a continuous interval.

#### 4. Ecosystem Comparisons
- **`Halide` Schedule Separation vs. Monolithic Shaders:** In `GLSL`/`WGSL`,
  optimizing shared-memory tiling requires rewriting the mathematical algorithm
  (risking race conditions tracked by `Faial`); in `Halide`, the schedule is a
  separate specification whose lowering is a horizontal `Compiles` pass.
- **`Gator` vs. Untyped `vec4` Shaders:** Standard `GLSL`/`WGSL` represents all
  3D points, normals, and colors as `vec3<f32>`, whereas `Gator` makes frame
  mismatches unrepresentable in the source language and erases frame tags during
  compilation.

#### 5. Formal Theory and TCB Analysis
- **Memory Access Protocols (`Faial`, Coq-verified):** Projects shared-memory
  array traces onto thread-local symbolic access sets and checks pairwise
  disjointness $\forall t_1 \neq t_2 \in \text{Workgroup},\; W(t_1) \cap
  (R(t_2) \cup W(t_2)) = \emptyset$ within each barrier phase.
- **Coordinate Frame Parametricity (`Gator`):** Affine spaces and dual covector
  spaces (normals transform via inverse-transpose $(M^{-1})^\top$); type safety
  guarantees representation independence under frame change.
- **Color Codec Invertibility (`OCIO`/`ACES`):** Scene-referred linear transforms
  form a group under matrix multiplication ($M_{B \leftarrow A} = M_{A
  \leftarrow B}^{-1}$) up to IEEE-754 half/single-precision rounding and gamut
  clipping.

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `Prog`: `Halide`/`Gator` shader lowered to `WGSL`/`SPIR-V` (`Naga`/`Tint`);
    or `CSS`/`Cassowary` DOM specification lowered to positioned 2D boxes
    (`Taffy`); or `TrueType` hinting bytecode (`FreeType`).
  - `Query`: Viewport dimensions $(W, H) \in [W_{\min}, W_{\max}] \times
    [H_{\min}, H_{\max}]$, pixel/workgroup coordinates, or font `ppem` size.
  - `Out` & `SemObs` (`obs`): Shaded pixel tensor / positioned 2D box tree /
    hinted glyph outline. `obs` projects UI layouts to the **reading-order text
    spine and containment hierarchy**, and shaders to pixel radiance intervals.
  - `Partial.ub` (`defined = False`):
    1. **Shaders (`Faial` / `spirv-val` / `Naga`):** Shared-memory data race,
       barrier divergence across non-uniform control flow, out-of-bounds buffer
       index, `NaN`/`Inf` generation (`normalize(0)`), or non-terminating loop
       (GPU `TDR` reset).
    2. **UI Layout (`Cassius` / `VizAssert` / `Taffy`):** Overlapping sibling
       text boxes ($\text{int}(B_i) \cap \text{int}(B_j) \neq \emptyset$), child
       overflowing non-scrollable parent, or negative dimensions.
    3. **Fonts (`FreeType` / `FontBakery`):** `TrueType` VM stack/CVT/zone
       out-of-bounds access, infinite loop, or stem-width dropout/winding
       inversion.
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Compiles HalideFuncLang SpirvLang codec pureFunc scheduledKernel`:
    Certifies `Halide` schedule lowering and `Caviar` e-graph rewrites.
  - `Compiles GatorLang WgslLang codec typedShader rawWgsl`: Certifies frame-tag
    erasure and `Naga` lowering.
  - **`OpenColorIO` / `ACES` IS Literally a `BehaviorCodec`!** The color-space
    transform pair $(\text{encode}_{\text{AP0}\to\text{AP1}},
    \text{decode}_{\text{AP1}\to\text{AP0}})$ satisfies `decodeOut_encodeOut`
    and `encodeOut_of_decodeOut` on in-gamut scene-referred radiance values,
    while out-of-gamut negative/NaN values map to `decodeOut = none` (`False`)!
  - `Abstracts FaialProtocolLang SpirvLang codec accessProtocol gpuKernel`:
    Certifies `Faial`'s Coq-verified memory-access protocol abstraction over SIMT
    shared-memory traces.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **Blocks the "`display: none` / Blank Page / Zero-Opacity" Goodhart
    Loophole:** A layout synthesizer asked to eliminate text overlap (`VizAssert`
    `defined = True`) can trivially hide every text node (`display: none`) or
    set font size to `0px`. `ProductiveOn ResponsiveViewports layout` paired
    with `obs_decodeOut` (preserving the complete visible character spine)
    forbids dropping text and proves the layout engine resolves a valid 2D box
    tree across the entire $[320\text{px}, 3840\text{px}]$ viewport continuum.
  - **`EventualBehaviorOf`:** Proves shader loop termination (preventing GPU
    `TDR` hangs) and `TrueType` bytecode termination.
- **`VerificationResult` & `TrustPolicy`:**
  - Separates exact `QF_LRA` layout non-overlap (`Cassius`) and `Faial`
    race-freedom proofs from hardware driver waivers (`.gpuDriverFollowsSpirvSpec`)
    or `Knuth–Plass` overfull-box emergency stretch waivers.

Basis: normative + documentation + source + derived.

---

### 3.9 Domain 8: Music Theory Counterpoint and Audio DSP Filter Stability

#### 1. Goals and Target Users
Audio DSP compilers, filter verifiers, and symbolic music composition engines
ensure that real-time digital audio kernels (recursive `IIR` filters, physical
waveguides, modular synthesizer patches) are Bounded-Input Bounded-Output
(`BIBO`) stable, free of fixed-point/floating-point limit cycles or `NaN`
explosions, and non-blocking on real-time audio threads, while symbolic music
engines enforce strict polyphonic voice-leading and harmonic constraints.
Target users include audio plugin/synthesizer developers (`VST3`/`CLAP`/embedded
DSP), broadcast audio engineers (`ITU-R BS.1770`), and computational musicologists.

#### 2. Concrete Tool Lineage and Technical Architecture
- **`Faust` (`grame-cncm/faust`, Orlarey, Fober, & Letz, GRAME Lyon) & `ChucK`
  / `Kronos` (Wang & Cook; Norilo):**
  - **`Faust` (*Functional Audio Stream*):** A pure functional synchronous
    dataflow language based on a **Block-Diagram Algebra** (`:` sequential, `,`
    parallel, `<:` split, `:>` merge, `~` recursive feedback with implicit
    1-sample delay $z^{-1}$). The `Faust` compiler checks causality (rejecting
    instantaneous delay-free algebraic loops), computes symbolic signal interval
    bounds (`[min, max]` propagation used to size fixed-point integers and prove
    array index safety in delay lines), and compiles to allocation-free C, Rust,
    LLVM IR, and WebAssembly SIMD.
  - **`ChucK` & `Kronos`:** Strongly timed (`now` sample-accurate logical clock
    advancement in `ChucK`) and multi-rate functional (`Kronos`) audio languages.
- **`rtsan` (*RealtimeSanitizer*, LLVM/Clang `compiler-rt/lib/rtsan`, 2024):**
  Upstreamed into LLVM/Clang 20, `rtsan` instruments functions annotated with
  `[[clang::nonblocking]]` (such as real-time audio `process()` callbacks) and
  intercepts libc/OS calls (`malloc`, `free`, `pthread_mutex_lock`, `open`,
  `read`, `usleep`, page-faulting syscalls) to deterministically trap real-time
  priority-inversion and XRUN glitch hazards.
- **`DSVerifier` (`ssvlab/dsverifier`, Ismail, Bessa, Cordeiro, et al.,
  University of Manchester / UFAM, *ACM TECS* 2017) & `Astrée` Digital Filter
  Abstract Domains (Feret, ESOP 2004; Cousot et al., PLDI 2005):**
  - **`DSVerifier`:** A Bounded Model Checking (`BMC`) tool backed by `CBMC` /
    `ESBMC` (`Z3`/`Boolector`) that verifies fixed-point and floating-point
    digital `IIR`/`FIR` filters and controllers (Direct Form I, Direct Form II,
    transposed, cascade, lattice) against **accumulator overflow**, **zero-input
    limit-cycle oscillations**, **pole/zero stability** (Jury criterion $|p_i| <
    1$ under finite-word-length `FXP` coefficient quantization), and minimum
    phase / settling time.
  - **`Astrée` Digital Filter Ellipsoid Domain (Feret, ESOP 2004):** To prove
    absence of runtime floating-point overflow across millions of iterations of
    recursive 2nd-order biquad filters ($y_n = a_1 y_{n-1} + a_2 y_{n-2} + b_0
    x_n + \dots$) where standard interval/octagon domains diverge to $[-\infty,
    +\infty]$ because of rotational complex conjugate poles, Feret designed a
    relational **quadratic ellipsoid abstract domain** ($s_n^\top P s_n \le c$,
    effectively a discrete-time Lyapunov energy invariant) that proves invariant
    boundedness in a single fixed-point pass!
- **`Strasheela` (`tanders/strasheela`, Torsten Anders, PhD Thesis 2007) &
  `Kulitta` (Donya Quick & Paul Hudak, Yale, ICMC/FARM 2013–2015):**
  - **`Strasheela`:** A constraint logic programming (`CLP` over finite domains
    in Mozart/Oz) composition system that encodes Fux species counterpoint,
    Schoenberg harmony, and microtonal tuning rules as declarative finite-domain
    constraints solved via branch-and-propagate search.
  - **`Kulitta` (in Haskell):** Formalizes tonal music composition as a
    generative grammar (`Musical Grammars`) lowered through chord spaces
    (Callender–Quinn–Tymoczko `OPTIC` voice-leading quotients) and constraint
    solvers to polyphonic scores satisfying parallel-fifth/octave prohibition
    and voice-range invariants.
- **`ITU-R BS.1770` / `EBU R-128` Loudness & True-Peak Specification:** The
  international normative broadcast audio standard defining `LKFS`/`LUFS`
  K-weighted loudness integration (a pre-filter high-shelf stage + RLB
  high-pass biquad stage followed by mean-square gating) and $4\times$
  oversampled polyphase FIR **True-Peak (`dBTP`)** metering to prevent
  inter-sample DAC reconstruction clipping.

#### 3. Design Philosophy and Tradeoffs
- **Non-Relational Intervals (`Faust` compiler) vs. Relational Ellipsoid / BMC
  Domains (`Astrée`, `DSVerifier`):** `Faust`'s built-in interval propagation is
  fast and compositional on non-recursive (`FIR`/waveshaper) graphs, but
  frequently reports `[ -inf, +inf ]` on stable recursive `IIR` filters because
  intervals cannot capture the phase cancellation between $y_{n-1}$ and
  $y_{n-2}$. `Astrée`'s ellipsoid domain captures that quadratic Lyapunov
  coupling soundly across infinite time, while `DSVerifier` finds exact bit-accurate
  fixed-point limit cycles over bounded horizons.
- **Runtime Interception (`rtsan`) vs. Static Call-Graph Verification:** `rtsan`
  catches blocking calls along executed test paths at runtime, whereas static
  verification over Rust `MIR` proves `[[nonblocking]]` across *all* branches
  prior to deployment.

#### 4. Ecosystem Comparisons
- **`Faust` Block-Diagram Algebra vs. Imperative DSP C++ (`JUCE`):** In `Faust`,
  every program is an algebraic expression built from 5 combinators whose
  sample-delay semantics are mathematically defined; imperative C++ DSP code
  manually manages circular buffer indices and state variables prone to
  off-by-one wraparound and uninitialized state bugs.
- **`Strasheela` Constraint Search vs. `Kulitta` Generative Grammars + Quotient
  Spaces:** `Strasheela` treats the entire score as a global CSP, whereas
  `Kulitta` refines high-level harmonic trees into concrete voice leadings step
  by step (`Compiles`).

#### 5. Formal Theory and TCB Analysis
- **Discrete-Time `BIBO` Stability & Lyapunov Ellipsoids (`Astrée` /
  `DSVerifier`):** A linear time-invariant filter $s_{n+1} = A s_n + B x_n$ is
  asymptotically stable iff all eigenvalues of $A$ satisfy $|\lambda_i(A)| < 1$
  (checked algebraically via the **Jury table** on the characteristic polynomial
  without computing complex roots!), which is equivalent to the existence of a
  symmetric positive-definite matrix $P \succ 0$ satisfying the Stein /
  discrete Lyapunov inequality $A^\top P A - P \prec 0$.
- **Counterpoint Relational Invariants (`Strasheela`/`Kulitta`):** 2-step trace
  predicates over voice tuples $(v_1(t), \dots, v_k(t)) \in \mathbb{Z}^k$
  requiring $v_1(t) \ge v_2(t) \ge \dots \ge v_k(t)$ (no voice crossing) and
  forbidding parallel perfect consonances ($\forall i < j,\; (v_i(t) - v_j(t) \equiv
  0, 7 \pmod{12} \land v_i(t+1) - v_j(t+1) = v_i(t) - v_j(t)) \implies
  v_i(t+1) = v_i(t)$).

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `FaustLang.Prog` / `HarmonicGrammarLang.Prog`: Declarative `Faust` block
    diagram or `Kulitta` harmonic progression.
  - `MirDspLang.Prog` / `PolyphonicScoreLang.Prog`: Compiled Rust/SIMD sample
    loop or 4-voice polyphonic MIDI score.
  - `Query`: Bounded input audio stream ($\forall n,\, |x[n]| \le 1.0$) and
    parameter trajectory, or cantus firmus / figured-bass input.
  - `Out` & `SemObs` (`obs`): Output sample stream $y[n]$ (with `obs` computing
    sample equivalence up to $\epsilon$ and `ITU-R BS.1770` `LUFS`/`dBTP`
    compliance), or 4-voice note matrix (with `obs` projecting to the Roman-numeral
    harmonic progression spine).
  - `Partial.ub` (`defined = False`):
    1. **Audio DSP:** Output or internal filter state overflow ($|y[n]| >
       \text{MaxHeadroom}$ or fixed-point wraparound in `DSVerifier`), `NaN`/denormal
       generation, delay-free feedback loop, or invoking any blocking/allocating
       primitive flagged by `rtsan` inside the real-time callback.
    2. **Music Theory (`Strasheela`/`Kulitta`):** Parallel fifths/octaves, voice
       crossing, out-of-range vocal pitch, or unresolved dissonance.
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Compiles FaustLang MirDspLang codec faustDiagram rustSimdKernel`: Certifies
    that `Faust` compilation to Rust `MIR` preserves sample stream semantics and
    introduces zero `rtsan` blocking operations or delay-line out-of-bounds
    accesses.
  - `Compiles HarmonicGrammarLang PolyphonicScoreLang codec chordTree score`:
    Formalizes `Kulitta` / `Strasheela` chorale harmonization as a verified
    refinement pass!
  - `Abstracts EllipsoidDomainLang MirDspLang codec lyapunovP biquadCascade`:
    Formalizes Feret's `Astrée` ellipsoid domain (`Abstracts`) in `theory/`,
    checking $A^\top P A - P \prec 0$ in exact rational arithmetic to certify
    infinite-horizon `BIBO` stability and absence of overflow.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **Blocks the "4'33\" Total Silence / Dead-End Cadence" Goodhart Loophole:**
    A DSP kernel that outputs `y[n] = 0.0` is trivially `BIBO`-stable, never
    clips `ITU-R BS.1770` true-peak limits, and never overflows, while an empty
    musical score commits zero parallel fifths! `ProductiveOn` paired with
    `obs_decodeOut` guarantees non-trivial transfer realization and guarantees
    that a counterpoint solver reaches the final cadence without backtracking
    into a dead-end bar where no valid continuation exists.
- **`VerificationResult` & `TrustPolicy`:**
  - Captures **Artistic License (`Strasheela`)** and **Modulation Slew Bounds
    (`DSP`)**: a composer can explicitly waive a single ornamental dissonance or
    unequal fifth (`waived := [.parallelFifths (Bar 12) .Tenor .Bass]`) under an
    `.artisticLicense` policy while certifying the remaining 99.9% of the score.

Basis: normative + documentation + source + derived.

---

### 3.10 Domain 9: Game Mechanics, Puzzle Solvability, TCG Rule Engines, and Virtual Economies

#### 1. Goals and Target Users
Game rule engines, puzzle-solvability verifiers, multi-world randomizer logic
solvers, and virtual-economy analyzers model discrete interactive state machines
to ensure that procedural levels and randomized item placements are **100%
beatable without soft-locks**, that complex Trading Card Game (`TCG`) trigger
interactions are deterministic and loop-bounded, and that virtual economies are
free of infinite-currency arbitrage cycles. Target users include game systems
designers, procedural content generation (`PCG`) engineers, multi-game
randomizer developers (`Archipelago`), and digital board/card game engineers.

#### 2. Concrete Tool Lineage and Technical Architecture
- **`PuzzleScript` (`increpare/PuzzleScript`, Stephen Lavelle, 2013) & `Ceptre`
  (`chrisamaphone/ceptre`, Chris Martens, CMU, AIIDE 2015):**
  - **`PuzzleScript`:** A declarative 2D grid-rewriting engine (`[ > Player |
    Crate ] -> [ > Player | > Crate ]`) compiled to bitvector cellular-automaton
    transition tables, widely used as a target for automated `BFS`/`A*`/SAT
    puzzle synthesis and minimum-step solvability verification.
  - **`Ceptre`:** A rule-based specification language founded on **Forward-Chaining
    Linear Logic (`Celf` / multiset rewriting)** where game state predicates
    (inventory keys, stamina tokens, room locations, narrative flags) are
    **linear hypotheses consumed upon rule firing** ($A \otimes B \multimap C
    \otimes D$), organized into stage blocks with quiescence transitions. Linear
    logic guarantees resource conservation by construction and supports forward
    trace generation and invariant checking.
- **`Ludii` (`Ludeme/Ludii`, Cameron Browne et al., Maastricht Univ. Digital
  Ludeme Project) & `Machinations` (Joris Dormans, PhD Thesis 2012):**
  - **`Ludii`:** A general game description language based on compositional
    *ludemes* capable of expressing $>1{,}000$ historical and modern board
    games, compiling game trees to optimized Java bytecode for Monte Carlo Tree
    Search (`MCTS`) playout and balance analysis (draw rates, first-player
    advantage, termination).
  - **`Machinations`:** Models internal game economies and progression loops as
    typed directed multigraphs ( closely related to **Petri nets** with Pools,
    Sources, Drains, Converters, Gates, and State Connections) paired with
    mission-grammar to space-grammar compilation for lock-and-key dungeons.
- **`Archipelago` (`ArchipelagoMW/Archipelago`) & `ALttPR` (*A Link to the Past
  Randomizer*) Logic Solvers:** Multi-world item randomizers partition game
  worlds into `Regions`, `Locations`, and `Entrances` guarded by monotone
  Boolean/counted item-Inventory accessibility predicates (`lambda state:
  state.has("Hookshot") and state.has("SmallKey", 3)`). To guarantee every
  generated seed is solvable without soft-locks, the **Assumed Fill** algorithm
  places progression items and iteratively expands the reachable item sphere
  from the remaining pool, verifying special **Small-Key Lock-In / Boss-Room
  Escape** invariants (proving that even if a player spends consumable keys in
  the worst possible order, they cannot permanently lock out the remaining keys).
- **`XMage` (`magefree/mage`) & `Forge` (`Card-Forge/forge`):** Open-source
  rule engines implementing the $>290$-page *Magic: The Gathering* (`MTG`)
  Comprehensive Rules: the 7-layer continuous effect system (`Rule 613`:
  copy $\to$ control $\to$ text $\to$ type $\to$ color $\to$ abilities $\to$
  power/toughness with timestamp and dependency topological sorting), the
  `APNAP` (*Active Player, Non-Active Player*) triggered-ability stack,
  replacement-effect self-application prevention (`Rule 614.5`), and
  state-based actions (`SBA` fixpoint loop).
- **`Festival` Sokoban Solver (Yaron Shoham & Jonathan Schaeffer, IJCAI 2021):**
  Championship `PSPACE`-complete Sokoban solver combining **FESS** (*Feature
  Space Search*) with hierarchical **deadlock detection**: static dead squares,
  $2\times 2$ freeze deadlocks (two adjacent boxes blocked along both axes),
  **corral deadlocks** (unreachable empty regions bounded by boxes that cannot
  be pushed inward or outward without creating a freeze), and bipartite matching
  lower bounds between boxes and target goals.

#### 3. Design Philosophy and Tradeoffs
- **Monotone Accessibility (`Archipelago`) vs. Non-Monotone Resource Consumption
  (`Ceptre` / `Festival`):** In `Archipelago`, permanent progression items
  (`Hookshot`, `Flippers`) induce a **monotone** state lattice ($I \subseteq I'
  \implies \text{Reach}(I) \subseteq \text{Reach}(I')$), reducing beatability to
  a polynomial-time least-fixed-point (`LFP`) sphere calculation! As soon as a
  game introduces **non-monotone transitions**—such as pushing a Sokoban box
  into a corner (`Festival`), spending a consumable small key, or dropping a
  one-way bridge (`Ceptre`)—reachability jumps from `P` to `PSPACE`-complete,
  requiring inductive deadlock/trap certificates or $\mathsf{AG}(\mathsf{EF}\;
  \mathsf{Win})$ verification.
- **Stochastic Monte Carlo Simulation (`Machinations` / `Ludii`) vs. Algebraic
  Conservation Proofs:** Running 1,000 Monte Carlo playouts in `Machinations`
  estimates average progression speed, but frequently misses a 4-step arbitrage
  cycle (`Craft A -> Salvage B -> Trade C -> Buy A + 10 Gold`) that a player or
  Linear Programming (`LP`) Farkas certificate detects immediately.

#### 4. Ecosystem Comparisons
- **`PuzzleScript` vs. `Ceptre`:** `PuzzleScript` embeds spatial 2D grid adjacency
  directly into rewrite syntax, whereas `Ceptre` represents arbitrary graph
  topologies, narrative states, and economic recipes via linear multiset
  rewriting.
- **`XMage` / `Forge` Imperative Rule Engines vs. Declarative Rule Verification:**
  `XMage` implements each of $>27{,}000$ cards as a Java class registering event
  listeners and replacement modifiers; subtle interactions between dependency
  loops in Layer 4/6 (`Blood Moon` + `Urborg` + `Opalescence`) or mandatory
  infinite trigger loops (`3 Oblivion Rings`) can only be verified systematically
  by abstracting the `Rule 613` layer engine and `SBA` loop as a transition
  system.

#### 5. Formal Theory and TCB Analysis
- **No-Soft-Lock as Branching-Time $\mathsf{AG}(\mathsf{EF}\;\mathsf{Win})$:**
  A game level $\langle S, s_0, \to, W \rangle$ is **solvable** iff $s_0 \models
  \mathsf{EF}\;W$ ($\exists s^* \in W,\; s_0 \to^* s^*$), and **soft-lock-free**
  iff $s_0 \models \mathsf{AG}(\mathsf{EF}\;W)$ ($\forall s,\; s_0 \to^* s
  \implies \exists s^* \in W,\; s \to^* s^*$). A `Festival` deadlock detector is
  a sound over-approximating trap predicate $D \subseteq S$ such that $\text{succ}(D)
  \subseteq D$ and $D \cap W = \emptyset$.
- **Economic No-Arbitrage via Farkas' Lemma (`Machinations` Petri Nets):** Given
  a stoichiometry/recipe transition matrix $M \in \mathbb{Z}^{m \times r}$ where
  column $j$ represents the net resource delta of recipe $j$ and column $0$ is
  premium currency, no repeatable sequence of recipes $x \ge 0$ can generate net
  positive wealth ($M x > 0$) iff there exists a positive shadow-price potential
  vector $w \in \mathbb{Q}_{>0}^m$ such that $w^\top M \le 0$.

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `MissionGraphLang.Prog`: Declarative Dormans/Archipelago lock-and-key
    progression graph or card-rule DSL specification.
  - `LevelLang.Prog`: Concrete `PuzzleScript`/`Ceptre` level, `Archipelago` seed,
    `XMage` card-interaction state machine, or `Machinations` economy graph.
  - `Query`: Initial spawn state $s_0$ (starting inventory, board state, or
    player wallet).
  - `Out` & `SemObs` (`obs`): `EventualOut GameplayTrace TerminalGameState`;
    `obs` maps outcomes to `.victory`, `.cleanDefeat`, `.mandatoryLoopDraw`, or
    milestone achievement sequences.
  - `Partial.ub` (`defined = False`):
    1. **Progression / Puzzles (`Archipelago` / `Festival` / `PuzzleScript`):**
       Entering a **soft-lock / deadlock trap** ($s \in D$ where no path to
       `.victory` exists).
    2. **TCG Engine (`XMage` / `Forge`):** Zone-conservation violation (card
       duplicated or lost across zones), unresolved `Rule 613` layer dependency
       violation, or unflagged mandatory infinite loop.
    3. **Virtual Economy (`Machinations`):** Reaching net wealth exceeding the
       initial endowment + bounded time-sink inflow (`ArbitrageExploit`).
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Compiles MissionGraphLang LevelLang codec lockKeyGraph concreteTilemap`:
    Proves that compiling a `Machinations`/`Archipelago` lock-and-key mission
    graph into a concrete 2D tilemap preserves exact progression gating (zero
    unintended sequence breaks and zero impossible jumps!).
  - `Abstracts DeadlockTrapLang LevelLang codec festivalCorral sokobanBoard`:
    Formalizes `Festival`'s freeze and corral deadlock detectors (`Abstracts`)
    as inductive trap sets proving unsolvability of pruned search branches.
  - `Abstracts FarkasPriceLang EconomyLang codec shadowPriceVector recipeNet`:
    Certifies absence of infinite-money crafting/vendor arbitrage loops in
    `theory/` via a dot-product check $w^\top M \le 0$.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **The Ultimate Anti-Vacuity Guarantee for Games & Puzzles:**
    - A procedural level generator that only proves `defined` ("no soft-locks on
      winning paths") can wall off the goal so zero winning paths exist!
    - **`ProductiveOn (fun q => q = s₀) level` directly states that the level is
      SOLVABLE ($\mathsf{EF}\;\mathsf{Win}$)!**
    - **Soft-Lock Freedom ($\mathsf{AG}(\mathsf{EF}\;\mathsf{Win})$)** is
      expressed in `theory/` without adding a single line to `trusted/lean/` by
      asserting `ProductiveOn (ReachableFrom s₀) level`: *every state reachable
      from $s_0$ still has a productive path to victory!*
- **`VerificationResult` & `TrustPolicy`:**
  - Models **Speedrunner Glitch Logic Tiers (`Archipelago` `No Glitches` vs.
    `Minor Glitches` / `Overworld Bunny Revival`)**: standard seeds are proved
    `ProductiveOn` with `waived = []`, while advanced glitch-logic seeds
    explicitly list `.bombJumpAllowed` or `.framePerfectClip` in `waived`!

Basis: normative + documentation + source + derived.

---

### 3.11 Domain 10: Smart-Home, Matter, and IoT Trigger-Action Automation Verification

#### 1. Goals and Target Users
Smart-home and Industrial IoT verification tools analyze collections of
event-driven **Trigger-Action Programs (`TAP`s)**—such as `Home Assistant`
automations, `Samsung SmartThings` SmartApps, `IFTTT` applets, and `Matter 1.3`
device bindings—to prevent **cross-app interference (`CAI`)**, **infinite
rule-chaining actuator loops**, **indirect physical-channel feedback hazards**
(via temperature, humidity, illuminance, smoke, or water flow), and **safety/security
policy violations** (such as unlocking exterior doors while `ArmedAway` without
an active fire alarm). Target users include smart-home platform engineers,
IoT security researchers, and building automation integrators.

#### 2. Concrete Tool Lineage and Technical Architecture
- **`SOTERIA` (Celik, McDaniel, & Tan, Penn State, USENIX ATC 2018) & `IoTGuard`
  (Celik et al., NDSS 2019):**
  - **`SOTERIA`:** Translates Groovy-based `SmartThings` app source code into an
    Intermediate Representation (`IR`), extracts finite-state machine (`FSM`)
    models with state-space reduction, and invokes `NuSMV` symbolic model
    checking against `CTL`/`LTL` safety, security, and functional properties
     across multi-app compositions.
  - **`IoTGuard`:** A dynamic runtime reference monitor that instruments IoT
    apps with code hooks collecting runtime events into a dynamic execution
    model and blocks actuator commands that would transition the home into a
    policy-violating state.
- **`IoTSAN` (`IoT Sanctifier`, Nguyen, Song, Qian, et al., ACM CoNEXT 2018) &
  `iRuler` (Wang et al., USENIX Security 2019):**
  - **`IoTSAN`:** Translates multi-app configurations and physical configuration
    dependencies into **Promela** and runs the `SPIN` explicit-state model
    checker to detect interaction-level flaws (chaining loops, race conditions,
    conflicting simultaneous commands) with root-cause app attribution.
  - **`iRuler`:** Uses SMT solving (`Z3`) and natural-language processing (`NLP`)
    of IFTTT rule descriptions to discover inter-rule vulnerabilities, including
    timing-window conflicts and hidden state dependencies across cloud service
    channels.
- **`MenShen` (Bu et al., DSN 2018) & `IoTMon` (Ding & Hu, ACM CCS 2018):**
  **Cyber-Physical Channel Verification!** Early verifiers missed interactions
  where App 1 turns on a space heater (`electricHeater.on`) and App 2 opens a
  window when temperature exceeds $80^\circ\text{F}$ (`tempSensor > 80 ->
  window.open`), because the two apps share no digital variable. `IoTMon` and
  `MenShen` construct bipartite **Actuator $\to$ Physical Channel $\to$ Sensor**
  dependency graphs (over 7 physical channels: temperature, humidity,
  illuminance, smoke, sound, motion, water level); `MenShen` models the coupled
  system as a **Linear Hybrid Automaton (`LHA`, checked via `PHAVer`)** tracking
  continuous temperature/humidity drift rates $\dot{T} \in [\alpha, \beta]$ to
  detect and repair physical-channel loops.
- **`SafeTAP` / `AutoTap` (`UChicagoSUPERgroup/autotap`, Lefkowitz, Zhang,
  Ur, & Littman, CHI 2019 / ICSE 2020):** Synthesizes and automatically patches
  user-written trigger-action rules against `LTL` safety properties ($\mathbf{G}
  \neg(\text{Raining} \land \text{WindowOpen})$) by constructing product Büchi
  automata and generating minimal additional guard predicates (`... AND NOT
  it_is_raining`) that preserve user intent while eliminating all violating
  paths.
- **`HAWatcher` (Fu, Zeng, et al., USENIX Security 2021):** Semantics-aware
  shadow-execution anomaly detector that mines normal physical-digital
  correlation invariants (e.g., `switch.on => powerMeter > 10W` and `motion =>
  illuminance_change`) from both automation rules and historical telemetry logs
  to detect spoofed sensor events, broken actuators, and stealthy cross-app
  attacks.
- **`Matter 1.3+` Specification (`project-chip/connectedhomeip`, Connectivity
  Standards Alliance):** Standardizes the local-first application-layer data
  model (`Nodes`, `Endpoints`, `Clusters`, `Attributes`, `Commands`, `Events`,
  and Access Control Lists `ACL`s with `View`/`Operate`/`Manage`/`Administer`
  privilege levels) across Thread, Wi-Fi, and Ethernet smart-home devices.

#### 3. Design Philosophy and Tradeoffs
- **Static Model Checking (`SOTERIA`, `IoTSAN`, `MenShen`, `AutoTap`) vs.
  Runtime Interception (`IoTGuard`, `HAWatcher`):** Static model checkers catch
  all reachable conflicts and synthesize minimal rule patches (`AutoTap`) at
  design time before any physical hazard occurs, but require known rule sets and
  bounded physical-channel models (`MenShen`); `IoTGuard` and `HAWatcher` handle
  dynamic closed-source cloud apps and hardware faults at runtime, at the cost
  of having to decide whether to **fail-open or fail-closed** when an actuator
  command is blocked mid-emergency.
- **Digital-Only State Models (`SOTERIA`) vs. Hybrid Physical-Channel Models
  (`MenShen`, `IoTMon`):** Modeling only digital device attributes misses $>40\%$
  of real-world cross-app interferences mediated by room temperature, light, or
  motion.

#### 4. Ecosystem Comparisons
- **`SOTERIA` (`NuSMV` BDDs) vs. `IoTSAN` (`SPIN` Promela) vs. `iRuler` (`Z3`
  SMT):** `SOTERIA` excels at symbolic CTL property checking on small state
  spaces; `IoTSAN` models asynchronous event queues and message-passing concurrency
  accurately in Promela; `iRuler` scales to thousands of stateless/timed IFTTT
  trigger-action applets via SMT.
- **Verification Only (`SOTERIA`/`IoTSAN`) vs. Automated Rule Repair
  (`AutoTap`/`MenShen`):** End users rarely understand raw `NuSMV`/`SPIN`
  counterexample traces; `AutoTap` translates counterexamples directly into
  concrete `IF ... WHILE ... THEN ...` guard patches.

#### 5. Formal Theory and TCB Analysis
- **Trigger-Action Confluence & Quiescence:** Let $R = \{r_1, \dots, r_m\}$ be a
  set of trigger-action rules where $r_i = (\text{event}_i, \text{cond}_i(s),
  \text{act}_i)$. Upon an external sensor event $e_0$ in quiescent state $s_0$,
  the rule engine steps $(s, E) \to (s', E')$ until the pending event queue $E$
  is empty. The rule set is **terminating (quiescent)** iff no infinite cascade
  exists, and **confluent** iff for every initial event $e_0$, all valid
  interleavings of simultaneously enabled rules reach the **exact same**
  quiescent actuator state $s^*$.
- **Büchi / Safety Shield Synthesis (`AutoTap`):** Given plant/environment
  transition system $T_{\text{env}}$ and safety property $\mathbf{G}\,\Phi_{\text{safe}}$,
  restricting each rule $r_i$'s condition to $\text{cond}'_i(s) :=
  \text{cond}_i(s) \land \Phi_{\text{safe}}(\text{act}_i(s))$ guarantees forward
  invariance of $\Phi_{\text{safe}}$.

#### 6. Exact Mapping to Anneal's 4 `trusted/` Primitives
- **`Language SemObs` & `Partial`:**
  - `HomeSafetySpec.Prog`: High-level safety lattice (`LifeSafety > Security >
    Comfort > Energy`) and desired user intents (`AutoTap` LTL/safety contract).
  - `TAPLang.Prog`: Composed `Home Assistant` / `Matter` / `SmartThings` rule
    set coupled with the `IoTMon`/`MenShen` physical-channel dependency graph.
  - `Query`: Initial device states + external environmental event (smoke
    detected, time reaches 11:00 PM, user leaves home, temperature crosses
    threshold).
  - `Out` & `SemObs` (`obs`): `EventualOut ActuatorCascadeTrace
    QuiescentHomeState`; `obs` extracts the final stabilized physical actuator
    vector (locks, valves, alarms, HVAC) after internal rule cascades settle.
  - `Partial.ub` (`defined = False`):
    1. **Safety/Security Violation (`SOTERIA` / `IoTGuard` / `AutoTap`):**
       Reaching any state with `smokeAlarm == On ∧ frontDoor == Locked`,
       `waterLeak == On ∧ mainValve == Open`, `heater == On ∧ ac == On`, or
       `mode == ArmedAway ∧ door == Unlocked ∧ ¬fireEmergency`.
    2. **Actuator Chattering / Non-Quiescence (`IoTSAN` / `iRuler`):** A single
       external event triggers an infinite or $> K$-step rule-chaining loop.
    3. **Non-Confluent Race (`IoTSAN`):** Two rules triggered by the same event
       write conflicting commands (`Lock` vs. `Unlock`) to the same `Matter`
       endpoint without deterministic priority arbitration.
- **`BehaviorCodec`, `Compiles`, & `Abstracts`:**
  - `Compiles HomeSafetySpec TAPLang codec userIntentSpec patchedRules`:
    **Formalizes `AutoTap` / `SafeTAP` rule repair!** Proves that compiling
    raw user rules by injecting priority-shield guards produces a `TAPLang`
    program that refines the safety specification (`defined = True`) and
    preserves all safe user automations (`obs_decodeOut`).
  - `Abstracts LinearHybridChannelLang TAPLang codec menshenLHA ruleSet`:
    Formalizes `MenShen` and `IoTMon` cyber-physical channel abstraction
    (`Abstracts`), bounding continuous temperature/illuminance/humidity coupling
    across independent apps.
  - `decodeOut = none`: Rejects unacknowledged `Matter` actuator states or
    oscillating non-quiescent states (`False`).
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
  - **Multi-Hop Rule-Cascade Stabilization via `EventualBehaviorOf` +
    `ProductiveOn`:** A single external event (1 step in `HomeSafetySpec`) may
    fire a 4-rule internal cascade (`Motion -> LivingRoomScene -> BlindsClose ->
    LightOn`) in `TAPLang` before reaching quiescence. `EventualBehaviorOf`
    collapses this $1 \to 4$ internal cascade naturally, and `ProductiveOn`
    proves that every external event **terminates in a quiescent state** rather
    than chattering forever!
  - **`StepResult.externalCall boundaryInv branches`:** Models physical sensor
    and actuator execution (`HAWatcher`): `boundaryInv` checks physical
    pre-actuation interlocks (such as garage-door optical beam clearance), and
    `branches` models nondeterministic physical world responses and `HAWatcher`
    sensor correlation bounds.
- **`VerificationResult` & `TrustPolicy`:**
  - Separates non-waivable life-safety obligations (`.fireUnlockOverride`,
    `.coVentilation`, `.sumpPumpAlwaysPowered`) from user-waivable comfort/energy
    tradeoffs (`.nighttimeThermostatOverride`).

Basis: normative + documentation + source + derived.

---

### 3.12 Master Cross-Domain Synthesis Matrix

| Domain | Representative Real-World Tools | `Prog` (`Source` $\leftrightarrow$ `Target`) | `Partial.ub` (`defined = False`) & `decodeOut = none` | `Compiles` (Downward) & `Abstracts` (Upward) | Anti-Vacuity Role of `ProductiveOn` + `InhabitedPre` | `StepResult.externalCall` & `VerificationResult` Waivers |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **1. Agentic AI Sandboxes & Firewalls** | `CaMeL`, `FIDES`, `SEAgent`, `AirGapAgent`, `Invariant`, `Cedar`, `OPA`, `NeMo`, `LlamaFirewall`, `LMQL`, `Guidance`, `Outlines` | `Cedar`/`FIDES` IFC Policy $\to$ `CaMeL`/`MCP` Proxy & `Outlines` DFA Mask | Unauthorized tool call, prompt-injected secret exfiltration; malformed JSON / forged MAC (`decodeOut = none`) | `Compiles`: Policy $\to$ Proxy; `Abstracts`: Lattice taint summary over `RAG` memory | Blocks "paranoid brick firewall" that rejects 100% of benign user tasks | `externalCall`: tool capability check (`boundaryInv`) + demonic LLM/web token output (`branches`); waives statistical classifier recall |
| **2. Neural-Network Certification** | `α,β-CROWN`, `Marabou`, `ERAN` (`DeepZ`/`DeepPoly`/`PRIMA`), `nnenum`, `NNV`, `OVAL`, `PyRAT`, `MN-BaB`, `VNN-LIB`, `Vehicle`, `CAISAR`, `Verisig` | `Vehicle` Spec $\to$ `VNN-LIB` / `FP32`/`INT8` Net $\leftarrow$ `α,β-CROWN` Dual / `Star` Set | Adversarial misclassification in $B_\infty(x_0, \epsilon)$, fairness violation, `NaN` (`decodeOut = none`) | `Abstracts`: `DeepPoly` / `α,β-CROWN` / `Star` set bounds concrete net; `Compiles`: `Vehicle` $\to$ `VNN-LIB` | Blocks contradictory `BaB` `ReLU` splits (`¬ InhabitedPre`) & empty output polytopes | `externalCall`: closed-loop `Verisig`/`NNV` plant ODE step; `VerificationResult` tracks per-anchor robustness & float solver waivers |
| **3. Automated Planning (`PDDL` / `HTN`)** | `VAL`, `INVAL`, Isabelle Validator (`Abdulaziz & Lammich`), `Fast Downward` (`helve`), `PANDA`/`pandaPIValidator`, `SHOP3`, `PRP`, `Unified Planning`, `LLM-Modulo` | `HDDL` Compound Task Network $\to$ Grounded `PDDL 2.1` Plan $\leftarrow$ `helve` Certificate | Unsatisfied action precondition, durative mutex clash; inconsistent mutex facts (`decodeOut = none`) | `Compiles`: `HTN` task decomposition (`pandaPIValidator`); `Abstracts`: `helve` inductive unsolvability invariant | Blocks dead-end plans, infinite wait loops, & inconsistent initial world states ($1 \to k$ via `EventualBehaviorOf`) | `externalCall`: `PRP` `FOND` demonic `oneof` environment outcomes; `LLM-Modulo` checks untrusted LLM plans with zero waivers |
| **4. CAD/CSG & CNC/3D-Print G-Code** | `Reincarnate`/`λCAD`, `Szalinski`, `Caviar`, `Fidget`/`Libfive`, `Manifold`, `OpenSCAD`, `VERICUT`, `CAMotics`, `LinuxCNC`, `PrusaSlicer`, `IceSL`, `FullControl` | `λCAD`/`Fidget` CSG Solid $\to$ `LinuxCNC`/`PrusaSlicer` G-Code $\leftarrow$ `Fidget` IA Octree | CNC holder/fixture crash, part gouge, 3D-print mid-air overhang; non-2-manifold mesh (`decodeOut = none`) | `Compiles`: CSG $\to$ mesh/G-code & `Szalinski`/`Caviar` e-graph rewrites; `Abstracts`: 3D Interval Octree | Blocks "air-cutting" or empty `M-30` G-code that avoids crashes by machining nothing ($1 \to 50{,}000$ steps) | `externalCall`: `LinuxCNC` `G-38.2` touch-probe cycle; waives decorative fillet tolerances while proving zero fixture clash |
| **5. Textiles (`Knitout`), Sheet Metal, & Origami** | `knitout`, `Autoknit`, `KnitSpeak`, `Radbend`/`TruTops`, `FOLD`, `Origami Simulator`, `Freeform Origami` | `Autoknit` Stitch Mesh / `FOLD` Crease Graph $\to$ `.k` `knitout` / Press-Brake Bends | Dropped live stitch, over-racked yarn snap, flange-punch crash, `faceOrders` self-intersection | `Compiles`: Stitch mesh $\to$ `knitout` needle transfers; `Abstracts`: Yarn stretch / rigid-origami cone | Blocks deadlocked transfer schedules & stranded un-cast-off needle loops ($1 \to 12$ `xfer` macro steps) | `externalCall`: yarn tension sensor & laser bend-angle feedback; waives empirical sheet-metal $K$-factor springback |
| **6. Civil/Structural, `BIM`/`IFC`, & `TopOpt`** | `Solibri`, `IfcOpenShell`/`ifctester` (`IDS`), `KBimCode`/`BERA`, `FDS + Evac`, `Pathfinder`, `OpenSees`, Interval `FEM`, `TopOpt` | Space Program $\to$ `IFC` BIM Model / `TopOpt` Mesh $\leftarrow$ Interval `FEM` (`IFEM`) | Dead-end fire egress ($\text{RSET} > \text{ASET}$), MEP 3D clash, beam buckling; $\det K = 0$ (`decodeOut = none`) | `Compiles`: Space program $\to$ `IFC`; `Abstracts`: Krawczyk Interval `FEM` stress/displacement enclosure | Blocks "windowless bunker" with zero doors or zero occupants satisfying egress rules vacuously | `externalCall`: $N-1$ fire/smoke corridor blockage contingencies; models `AHJ` building-code variances in `waived` |
| **7. GPU Shaders, Color Codecs, & UI Layout** | `spirv-val`, `Naga`/`Tint`, `GPUVerify`, `Faial`, `GraphicsFuzz`, `Slang`, `Halide`, `Gator`, `OCIO`/`ACES`, `Cassowary`/`Kiwi`, `Cassius`/`VizAssert`, `Taffy`, `Typst`, `FreeType` | `Halide`/`Gator` / `CSS` DOM $\to$ `SPIR-V`/`WGSL` / 2D Boxes; `OCIO` Color `BehaviorCodec` | GPU data race (`Faial`), barrier divergence, `TDR` hang, UI text overlap (`VizAssert`), glyph stem dropout | `Compiles`: `Halide`/`Gator`/`Taffy` lowering; `Abstracts`: `Faial` memory access protocols | Blocks layout engine hiding text (`display: none`) or failing on valid responsive viewport widths $[320, 3840]$ | `OCIO`/`ACES` instantiates `BehaviorCodec` directly; waives hardware GPU driver bugs or `Knuth–Plass` emergency stretch |
| **8. Music Theory & Audio DSP Stability** | `Faust`, `ChucK`/`Kronos`, `rtsan`, `DSVerifier`, `Astrée` Ellipsoid Domain, `Strasheela`, `Kulitta`, `ITU-R BS.1770` | `Faust` Block Algebra / `Kulitta` Grammar $\to$ SIMD Audio Kernel / 4-Part Score | IIR pole explosion ($|\lambda_i| \ge 1$), `FXP` limit cycle (`DSVerifier`), `rtsan` blocking call, parallel 5ths | `Compiles`: `Faust` codegen & `Kulitta` harmonization; `Abstracts`: `Astrée` quadratic Lyapunov ellipsoid | Blocks "4'33\" silence" (`y[n] = 0.0`) or counterpoint dead-ends before final cadence | `VerificationResult` records explicit `.artisticLicense` counterpoint waivers (`Bar 12`) while proving remaining bars |
| **9. Games, Puzzles, TCGs, & Economies** | `PuzzleScript`, `Ceptre`, `Ludii`, `Machinations`, `Archipelago`/`ALttPR`, `XMage`/`Forge`, `Festival` Sokoban | Lock-and-Key Graph / Card Rules $\to$ `PuzzleScript`/`Archipelago` Seed / `XMage` Engine | Progression soft-lock ($\neg\mathsf{EF}\;\mathsf{Win}$), `MTG` mandatory loop, economy arbitrage exploit | `Compiles`: Dormans mission-to-space PCG; `Abstracts`: `Festival` corral deadlocks & Farkas Petri-net prices | `ProductiveOn s₀` proves level beatability; `ProductiveOn (Reach s₀)` proves universal no-soft-lock ($\mathsf{AG}\mathsf{EF}\;\mathsf{Win}$) | `externalCall`: opponent/RNG transitions; `VerificationResult` encodes `Archipelago` speedrunner glitch-logic tiers |
| **10. Smart-Home, `Matter`, & IoT Rules** | `SOTERIA`, `IoTGuard`, `IoTSAN`, `MenShen`, `iRuler`, `SafeTAP`/`AutoTap`, `HAWatcher`, `IoTMon`, `Matter 1.3` | `AutoTap` LTL Safety Spec $\to$ `Matter` / `Home Assistant` TAP Rules $\leftarrow$ `MenShen` LHA | Fire-door locked during alarm, heater + A/C clash, infinite relay-chattering loop | `Compiles`: `AutoTap` safety-shield patch synthesis; `Abstracts`: `MenShen`/`IoTMon` physical-channel LHA | `EventualBehaviorOf` + `ProductiveOn` proves multi-rule cascades converge to a unique quiescent state | `externalCall`: cyber-physical sensor/actuator step (`HAWatcher`); blocks waiving life-safety rules while allowing comfort waivers |

---

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **Progent (`sunblaze-ucb/progent`, 2025), AgentArmor (2025), IsolateGPT (NDSS
  2025), XGrammar (`mlc-ai/xgrammar`), SynCode, and SpiceDB/OpenFGA:** SMT-
  verified monotonic privilege confinement for agent tool calls
  (`StepResult.externalCall`), runtime CFG/PDG information-flow guards, and
  pushdown-automaton token-mask compilers (`decodeOut != none`).
- **NeuralSAT (`dynaroars/neuralsat`, VNN-COMP 2024-2025), Marabou Proof-
  Producing Farkas Checker in Imandra, CORA, Venus2, Debona, PeregriNN, DNNV,
  LipSDP, and Isabelle/HOL FNN (SEFM 2023):** CDCL+LiRPA neural verifiers, exact
  rational Farkas tree certificate checkers, SDP 1-Lipschitz certifiers, and
  mechanized ITP neural network formalizations.
- **Lean 4 Unsolvability Certificate Validator (`AmosNico/validator`,
  2025-2026), `helve` (`salome-eriksson/helve`), Isabelle Temporal Plan
  Validator, and TAMER:** Mechanized Lean 4 kernel validator for classical
  planning unsolvability certificates (`¬ ProductiveOn`) and temporal `PDDL+`
  SMT validators.
- **Formalizing Linear Motion G-Code (OOPSLA 2025), LLNL Coq RS-274 G-Code
  Analyzer (2023-2024), CSL for 5-Axis CNC Spatial Heaps, CGAL 3D Nef Polyhedra,
  and Fornjot:** G-code cuboid/point-cloud invariant lifting, Coq-extracted
  RS-274 static analysis, spatial-separation-logic collision freedom, and exact
  rational Boolean CSG kernels.
- **Fenced Tangles & `UFO` Knitting Compilers (SIGGRAPH 2023 / Asia 2024),
  Polynomial-Time Knitting Equivalence (ICFP 2025), and Origamizer (SoCG
  2017):** Knot-theoretic denotational semantics (`Fenced Tangles`) and
  polynomial-time topological equivalence decision procedures for V-bed machine
  knitting.
- **CORENET e-PlanCheck (`FORNAX`), Compas TNA (`compas_tna`),
  `INTLAB`/`IntervalLinearAlgebra.jl`, Coq-Verified Halide TRS (OOPSLA 2020),
  Cornipickle, Coq Digital Filters & WCPG Theorem (FM 2019), Velus (PLDI 2017),
  Micro-Machinations, and PatrIoT/ContexIoT:** Masonry thrust-network
  equilibrium certificates, Coq-verified Halide rewrite rules, Coq LTI filter
  Worst-Case Peak-Gain proofs, and MFOTL runtime IoT monitors.

### Part II: Historical Verification, Compiler, and Operational Failure Postmortems

### Historical Failure Analysis 1. Cross-domain failure taxonomy and mapping to Anneal's `trusted/` primitives

Every historical failure examined in this report instantiates one or more of six
structural defects that Anneal's four `trusted/` primitive families are
designed to prevent:

| Defect class | Representative historical incidents | Anneal `trusted/` primitive that blocks the defect |
| :--- | :--- | :--- |
| **Ideal-math vs. machine-arithmetic gap** | Jia & Rinard (2021) breaking `ERAN`/`MIPVerify` via IEEE-754 rounding; `VNN-COMP` GPU non-associativity in `α,β-CROWN`; `CGAL` exact-to-float STL snap self-intersections; audio DSP subnormal CPU spikes | `Language SemObs` concrete machine semantics (`BitVec` / IEEE-754 `Float32`) + `Abstracts` conservative rounding envelopes |
| **Validator micro-step & boundary semantics bug** | PDDL `VAL` accepting invalid plans due to `add`/`delete` ordering & $\epsilon$-boundary drift; CNC `G-00` dogleg rapid collisions missed by linear CAM simulators | Kernel-checked operational semantics in `trusted/` (`StepResult`, `EventualBehaviorOf`) with `Partial.ub` (`defined = False`) on any intermediate hazard prefix |
| **Ill-formed intermediate representation / mesh** | Sleipner A `NASTRAN` skewed tricell element mesh ($47\%$ shear error); `OpenSCAD` non-manifold edges; `Knitout` stranded live loops at program end | `BehaviorCodec.decodeOut = none` rejecting ill-formed target states before outcome comparison |
| **Unmodeled environment or physical coupling** | Hartford Civic Center unmodeled eccentric top-chord buckling; `SOTERIA`/`iRuler` heater $\to$ temp $\to$ window $\to$ alarm physical loops; `Autoknit` yarn-tension breakage across racks | `Abstracts` over coupled environment state + `StepResult.externalCall boundaryInv branches` for nondeterministic plant/environment interactions |
| **Vacuous satisfaction / over-refusal / hang** | `NeMo Guardrails` / `LlamaGuard` blocking benign prompts (`XSTest`/`OR-Bench`); empty `BaB` split cells in neural verification; iOS `Auto Layout` exponential freeze; shader `TDR` infinite loops | `InhabitedPre` (non-empty valid inputs) + `ProductiveOn` (existence of terminating, non-UB execution) + `obs_decodeOut` (observable spine preservation) |
| **Unverified solver or oracle in the TCB** | `VNN-COMP` false `UNSAT` from Gurobi/CPLEX `10^-6` tolerances (`VeriNet`, `Marabou`, `CGDTest`); indirect prompt injection subverting LLM safety judges (`AgentDojo`) | Positive per-obligation `VerificationResult` (`ob.id ∈ waived ∨ ob.prop`) + certificate checking in `theory/` instead of trusting external solver verdicts |

Basis: **derived** synthesis across the primary literature, CVEs, and forensic
reports cited in Sections 2–6.

---

### Historical Failure Analysis 2. Neural-network verifier soundness failures (`VNN-COMP` and floating-point attacks)

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

### Historical Failure Analysis 3. Agentic guardrail bypasses and over-refusal vacuity (`NeMo Guardrails`, `LlamaGuard`, `CaMeL`, `XSTest`, and `OR-Bench`)

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

### Historical Failure Analysis 4. Automated planning validator bugs (`VAL` vs. Isabelle/HOL `INVAL`)

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

### Historical Failure Analysis 5. CAD/CSG non-manifold failures, CNC G-code crashes, textile compiler bugs, and structural FEA collapses

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

#### 5.2 CNC rapid-traverse (`G-00`) dogleg collision crashes

In 3-axis and 5-axis CNC milling (`ISO 6983` / RS-274D G-code), `G-01 Xx Yy Zz Ff`
commands a **linearly interpolated cutting move** where all axes are
synchronized to follow the exact straight line segment from $\mathbf{p}_0$ to
$\mathbf{p}_1$. By contrast, `G-00 Xx Yy Zz` commands a **non-cutting rapid
positioning traverse**.

A notorious cause of catastrophic physical CNC spindle crashes is the **`G-00`
dogleg (non-linear rapid) semantic mismatch**:

- **The physical controller behavior:** On standard industrial CNC controllers
  (Fanuc, Haas, Siemens, Mazak when non-linear rapid parameter `NLR` is active),
  `G-00` does **not** interpolate a straight line in $\mathbb{R}^3$. Instead, the
  controller commands each axis motor ($X, Y, Z$) independently at its maximum
  rapid velocity $v_{\max,i}$. If the tool moves from $(0, 0, 50)$ to $(100, 20,
  50)$ with $v_{\max,X} = v_{\max,Y}$, the $Y$-axis reaches $Y = 20$ at $X = 20$
  (traveling at a $45^\circ$ diagonal) and then travels parallel to the $X$-axis
  from $(20, 20, 50)$ to $(100, 20, 50)$—forming a bent **"dogleg" trajectory**.
  Even worse, on a combined $XY+Z$ rapid retract or plunge, if the $Z$-axis has
  a slower rapid rate or longer travel than $X/Y$, the tool sweeps horizontally
  before clearing the workpiece height!
- **The CAM simulator failure:** Unverified CAM toolpath visualizers and naive
  collision checkers model `G-00` as a straight line segment $\overline{\mathbf{p}_0
  \mathbf{p}_1}$ identical to `G-01`. When a fixture clamp or tall boss lies
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
   under-approximated point sample:** Both the CNC `G-00` dogleg crash and the
   Sleipner A $47\%$ shear underestimation happened because a simulator or FEA
   model substituted an optimistic point/line approximation for a conservative
   outer envelope. In Anneal, `Abstracts AbstractLang ConcreteLang codec absProg
   concProg` requires `ConcreteLang.sem concProg ≤ codec.toMorphism
   (AbstractLang.sem absProg)`. For a CNC verifier, `absProg` must bound the
   entire swept bounding box of all non-deterministic per-axis `G-00` velocity
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
   `ProductiveOn` blocks an agent from emitting `M-30` (an immediate halt that
   cuts zero metal and therefore never crashes) or generating a building with
   zero doors to vacuously satisfy door-width rules.

---

### Historical Failure Analysis 6. Shader compilers, font hinting bytecode, UI constraint layout, audio DSP, and smart-home IoT rule failures

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

### Part I — Real-World Tool Survey Boundaries

The following boundaries separate established findings in this report from
unexamined or unsupported cases:

1. **Floating-Point vs. Exact Rational Dual Verification (`known not to apply`
   without certificate translation):** Standard GPU executions of `α,β-CROWN`,
   `GPUPoly`, `VERICUT`, `Origami Simulator`, and `OpenSees` compute in IEEE-754
   floating-point arithmetic (`FP32`/`FP64`) rather than exact rationals
   $\mathbb{Q}$ or rigorous interval arithmetic. Their native outputs do not
   by themselves constitute Lean-kernel proofs of `Abstracts` unless their dual
   witnesses (such as `α,β-CROWN` $(\alpha, \beta)$ multipliers, `Astrée`
   Lyapunov matrices $P$, or Krawczyk interval enclosures) are checked via
   verified rational or outward-rounded interval arithmetic in `theory/`.
2. **Continuous PDE Discretization Fidelity (`not examined`):** In Domain 6
   (`FDS + Evac` Navier–Stokes smoke transport and continuous 3D elasticity
   prior to `FEM` meshing) and Domain 5 (nonlinear yarn visco-elasticity beyond
   discrete needle-pitch stretch bounds), the fidelity of the finite-volume or
   finite-element PDE discretization relative to continuum physics was not
   mechanically verified; Anneal's `VerificationResult` models these continuum
   fidelity assumptions as explicit positive waiver IDs.
3. **Statistical Guardrail Classifiers (`unsupported` as sound `Abstracts`
   certificates):** Neural classifiers in Domain 1 (`PromptGuard 2`,
   `AlignmentCheck`, embedding-similarity rails) do not provide sound
   over-approximations (`Abstracts`) against adaptive adversarial inputs; only
   architectural capability/IFC sandboxes (`CaMeL`, `FIDES`, `SEAgent`, `Cedar`)
   and automaton-masked decoders (`Outlines`, `LMQL`, `Guidance`) establish
   deterministic prefix safety (`defined`).
4. **Source-Level Execution of Proprietary Commercial Tools (`not examined`):**
   Closed-source commercial tools surveyed for architectural comparison
   (`VERICUT`, `NCSimul`, `Radbend`, `TruTops Bend`, `Solibri Office`,
   `Pathfinder`, `Astrée`) were analyzed via their published technical
   specifications, patents, and peer-reviewed academic papers rather than
   direct source-code inspection or local binary execution.

---

### Part II — Historical Verification Failure Postmortem Boundaries

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
  permits degenerate implementations that reject all inputs, emit empty `M-30`
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

### Part I — Real-World Tool Survey Evidence

### Domain 1 (Agentic AI Sandboxes, Action Firewalls, & Constrained Decoding)
- **`CaMeL`:** Edoardo Debenedetti, Ilia Shumailov, Tianqi Fan, Jamie Hayes,
  Nicholas Carlini, Daniel Fabian, Christoph Kern, Chongyang Shi, Andreas
  Terzis, & Florian Tramèr, *"Defeating Prompt Injections by Design"*,
  `arXiv:2503.18813` (March 2025); repository
  `https://github.com/google-research/camel-prompt-injection` (normative +
  documentation + source).
- **`FIDES`:** Manuel Costa, Boris Köpf, Aashish Kolluri, Andrew Paverd, Mark
  Russinovich, Ahmed Salem, Shruti Tople, Lukas Wutschitz, & Santiago Zanella-Béguelin
  (Microsoft Research), *"Securing AI Agents with Information-Flow Control"*,
  `arXiv:2505.23643` (May 2025) (documentation).
- **`SEAgent` & `AirGapAgent`:** *"Taming Various Privilege Escalation in
  LLM-Based Agent Systems: A Mandatory Access Control Framework"*,
  `arXiv:2505.09143` (2025); Eugene Bagdasarian et al., *"AirGapAgent:
  Protecting Privacy-Conscious Conversational Agents"*, ACM CCS 2024
  (documentation).
- **`Cedar`:** Joseph W. Cutler, Craig Disselkoen, Aaron Eline, Shaobo He, Kyle
  Headley, Michael Hicks, Kesha Hietala, Eleftherios Ioannidis, John Kastner,
  Anwar Mamat, Darin McAdams, Matt McCutchen, Neha Rungta, Emina Torlak, &
  Andrew Wells, *"Cedar: A New Language for Expressive, Fast, Safe, and
  Analyzable Authorization"*, OOPSLA 2024; Lean 4 formalization at
  `https://github.com/cedar-policy/cedar-spec` (normative + source).
- **`OPA`, `Invariant Guardrails`, `NeMo Guardrails`, `LlamaFirewall`, `LMQL`,
  `Guidance`, `Outlines`:** `https://github.com/open-policy-agent/opa`,
  `https://github.com/invariantlabs-ai/invariant`,
  `https://github.com/NVIDIA/NeMo-Guardrails`,
  `https://github.com/meta-llama/PurpleLlama` (`LlamaFirewall` & `CodeShield`),
  `https://github.com/eth-sri/lmql` (Beurer-Kellner et al., PLDI 2023),
  `https://github.com/guidance-ai/guidance`, and
  `https://github.com/dottxt-ai/outlines` (Willard & Louf, 2023)
  (documentation + source).

### Domain 2 (Neural-Network Certification)
- **`α,β-CROWN`:** Huan Zhang, Shiqi Wang, Kaidi Xu, Linyi Li, Bo Li, Suman
  Jana, Cho-Jui Hsieh, & Zico Kolter, `https://github.com/Verified-Intelligence/alpha-beta-CROWN`
  (Wang et al., *NeurIPS* 2021; Zhang et al., *NeurIPS* 2018) (documentation +
  source).
- **`Marabou` / `Reluplex`:** Guy Katz et al., *"The Marabou Framework for
  Verification and Analysis of Deep Neural Networks"*, CAV 2019 / *"Marabou
  2.0"*, CAV 2024; `https://github.com/NeuralNetworkVerification/Marabou`
  (documentation + source).
- **`ERAN` (`DeepZ`, `DeepPoly`, `GPUPoly`, `PRIMA`) & `MN-BaB`:** Gagandeep
  Singh, Timon Gehr, Matthew Mirman, Markus Püschel, & Martin Vechev (ETH
  Zurich), *NeurIPS* 2018 (`DeepZ`), *POPL* 2019 (`DeepPoly`), *POPL* 2022
  (`PRIMA`), `https://github.com/eth-sri/eran` and
  `https://github.com/eth-sri/mn-bab` (Ferrari et al., *ICLR* 2022)
  (documentation + source).
- **`nnenum`, `NNV`, `OVAL`, `VeriNet`, `PyRAT`, `SAVer`, `FairSquare`,
  `VeriFair`, `Verisig`, `ReachNN*`:** Stanley Bak, CAV 2021
  (`https://github.com/stanleybak/nnenum`); Hoang-Dung Tran et al., CAV 2020
  (`https://github.com/verivital/nnv`); `https://github.com/oval-group/oval-bab`;
  Albarghouthi et al., OOPSLA 2017 (`FairSquare`); Bastani et al., OOPSLA 2019
  (`VeriFair`); Radoslav Ivanov et al., HSCC 2019
  (`https://github.com/verisig/verisig`) (documentation + source).
- **`VNN-LIB`, `Vehicle`, & `CAISAR`:** `https://github.com/VNNLIB/VNNLIB-Standard`;
  Matthew L. Daggitt, Robert Atkey, Wen Kokke, Ekaterina Komendantskaya, & Luca
  Arnaboldi, *"Vehicle: Bridging the Embedding Gap in the Verification of
  Neuro-Symbolic Programs"*, `https://github.com/vehicle-lang/vehicle`; Julien
  Girard-Satabin et al., *"The CAISAR Platform: Extending the Reach of Machine
  Learning Specification and Verification"*, iFM 2023,
  `https://git.frama-c.com/pub/caisar` (normative + documentation + source).

### Domain 3 (Automated Planning & PDDL Validators)
- **`VAL`, `INVAL`, & Isabelle Verified Validator:** Richard Howey, Derek Long,
  & Maria Fox, *"VAL: Automatic Plan Validation, Continuous Effects and Mixed
  Initiative Planning Using PDDL"*, ICTAI 2004 (`https://github.com/KCL-Planning/VAL`);
  Patrik Haslum, `https://github.com/patrikhaslum/INVAL`; Mohammad Abdulaziz &
  Peter Lammich, *"A Formally Verified Validator for Classical Planning Problems
  and Plans"*, ITP 2018 / Archive of Formal Proofs
  `AI_Planning_Languages_Semantics` (normative + documentation + source).
- **`Fast Downward` Unsolvability Certificates (`helve`), `PANDA` /
  `pandaPIValidator`, `SHOP3`, `PRP`, `Unified Planning`, `ENHSP`/`POPF`, &
  `LLM-Modulo`:** Salomé Eriksson, Gabriele Röger, & Malte Helmert, *"Unsolvability
  Certificates for Classical Planning"*, ICAPS 2017 (`https://github.com/aibasel/downward`);
  Daniel Höller et al., `https://github.com/panda-planner-dev/pandaPIValidator`;
  `https://github.com/shop-planner/shop3`; Christian Muise et al., ICAPS 2012
  (`PRP`); `https://github.com/aiplan4eu/unified-planning`; Subbarao Kambhampati
  et al., *"LLMs Can't Plan, But Can Help Planning in LLM-Modulo Frameworks"*,
  ICML 2024 (`arXiv:2402.01817`) (documentation + source).

### Domain 4 (CAD/CSG Solid Modeling & G-Code Slicers)
- **`Reincarnate` (`λCAD`), `Szalinski`, & `Caviar`:** Chandrakana Nandi, James
  R. Wilcox, Pavel Panchekha, Taylor Blau, Dan Grossman, & Zachary Tatlock,
  *"Functional Programming for Compiling and Decompiling Computer-Aided Design"*,
  ICFP 2018 (`https://github.com/uwplse/reincarnate`, including Rocq/Coq proofs
  of `λCAD` mesh compilation); Chandrakana Nandi et al., *"Synthesizing
  Structured CAD Models with Equality Saturation and Inverse Transformations"*,
  PLDI 2020 (`https://github.com/uwplse/szalinski`); Yaëlle Kourta, Adel
  Bouredji, et al., *"Caviar: An E-graph Based TRS for Halide"*, OOPSLA 2022
  (documentation + source).
- **`Fidget`, `Libfive`, `Manifold`, `OpenSCAD`, `CAMotics`, `LinuxCNC`,
  `PrusaSlicer`, `IceSL`, & `FullControl`:** Matt Keeter,
  `https://github.com/mkeeter/fidget` and `https://github.com/libfive/libfive`;
  Emmett Lalish, `https://github.com/elalish/manifold`;
  `https://github.com/CauldronDevelopmentLLC/CAMotics`;
  `https://github.com/LinuxCNC/linuxcnc`;
  `https://github.com/prusa3d/PrusaSlicer`;
  `https://github.com/FullControlXYZ/fullcontrol` (Gleadall, *Additive
  Manufacturing* 2021) (documentation + source).

### Domain 5 (Programmable Textiles, Sheet Metal, & Rigid Origami)
- **`knitout`, `Autoknit`, `KnitSpeak`, `FOLD`, `Origami Simulator`, &
  `Freeform Origami`:** James McCann et al. (CMU Textiles Lab), *"A Compiler for
  3D Machine Knitting"*, ACM TOG / SIGGRAPH 2016, and Vidya Narayanan et al.,
  *"Automatic Machine Knitting of 3D Meshes"*, SIGGRAPH 2018
  (`https://github.com/textiles-lab/knitout` and
  `https://github.com/textiles-lab/autoknit`); Megan Hofmann et al., UIST 2019 /
  CHI 2023 (`KnitPick`/`KnitSpeak`); Erik D. Demaine, Jason S. Ku, & Robert J.
  Lang, `https://github.com/edemaine/fold`; Amanda Ghassaei, Erik D. Demaine, &
  Neil Gershenfeld, `https://github.com/amandaghassaei/OrigamiSimulator`;
  Tomohiro Tachi, *"Generalization of Rigid-Foldable Quadrangle-Mesh Origami"*,
  *Journal of the IASS* 2009 (`Freeform Origami`) (normative + documentation +
  source).

### Domain 6 (Civil/Structural, `BIM`/`IFC`, & `TopOpt`)
- **`IfcOpenShell`/`ifctester`, `KBimCode`/`BERA`, `FDS + Evac`, `OpenSees`,
  Interval `FEM`, & `TopOpt`:** `https://github.com/IfcOpenShell/IfcOpenShell`
  (`ifctester` / buildingSMART `IDS 1.0`); Jin-Kook Lee, Charles M. Eastman, et
  al., *"Translating building legislation into a computer-executable format for
  evaluating building permit requirements"*, *Automation in Construction* 2016
  (`BERA`/`KBimCode`); NIST `https://github.com/firemodels/fds`;
  `https://github.com/OpenSees/OpenSees`; Rafi L. Muhanna & Robert L. Mullen,
  *"Uncertainty in Mechanics Problems—Interval-Based Approach"*, *ASCE Journal
  of Engineering Mechanics* 2001 (`Interval FEM`); Ole Sigmund, *"A 99 line
  topology optimization code written in Matlab"*, *Structural and
  Multidisciplinary Optimization* 2001 (normative + documentation + source).

### Domain 7 (GPU Shaders, Color-Space Codecs, Typography, & UI Layout)
- **`spirv-val`, `Naga`/`Tint`, `GPUVerify`, `Faial`, `GraphicsFuzz`, `Slang`,
  `Halide`, `Gator`, & `OpenColorIO`:** `https://github.com/KhronosGroup/SPIRV-Tools`;
  `https://github.com/gfx-rs/wgpu` (`naga`); Adam Betts et al., OOPSLA 2012
  (`GPUVerify`); Tiago Cogumbreiro et al., *"Memory Access Protocols: Certified
  Data-Race Freedom for GPU Kernels"*, CAV 2021 (`https://github.com/umb-svl/faial`,
  with Rocq/Coq proofs); Alastair F. Donaldson et al., OOPSLA 2017
  (`GraphicsFuzz`); Julie L. Newcomb et al., *"Verifying and Improving Halide's
  Term Rewriting System with Program Synthesis"*, OOPSLA 2020
  (`https://github.com/halide/Halide`); Dietrich et al., *"Geometry Types for
  Graphics Programming"*, OOPSLA 2020 (`https://github.com/cucapra/gator`);
  `https://github.com/AcademySoftwareFoundation/OpenColorIO` (normative +
  documentation + source).
- **`Cassowary`/`Kiwi`, `Cassius`/`VizAssert`, `Taffy`, `Knuth–Plass`/`Typst`, &
  `FreeType`/`FontBakery`:** Greg J. Badros, Alan Borning, & Peter J. Stuckey,
  *ACM TOCHI* 2001 (`https://github.com/nucleic/kiwi`); Pavel Panchekha, Adam
  T. Geller, Michael D. Ernst, Zachary Tatlock, & Shoaib Kamil, *"Verifying That
  Web Pages Have Accessible Layout"*, PLDI 2018 (`https://github.com/uwplse/cassius`);
  `https://github.com/DioxusLabs/taffy`; Donald E. Knuth & Michael F. Plass,
  *"Breaking Paragraphs into Lines"*, *SPE* 1981;
  `https://github.com/typst/typst`; `https://github.com/fonttools/fontbakery`
  (documentation + source).

### Domain 8 (Music Theory & Audio DSP)
- **`Faust`, `rtsan`, `DSVerifier`, `Astrée` Filter Domains, `Strasheela`,
  `Kulitta`, & `ITU-R BS.1770`:** Yann Orlarey, Dominique Fober, & Stéphane
  Letz, `https://github.com/grame-cncm/faust`; LLVM `RealtimeSanitizer`
  (`compiler-rt/lib/rtsan`, LLVM 20); Hussama Ismail, Iury Bessa, Lucas C.
  Cordeiro, Eddie de Lima Filho, & João Edgar Chaves Filho, *"DSVerifier: A
  Bounded Model Checking Tool for Digital Systems"*, *ACM TECS* 2017
  (`https://github.com/ssvlab/dsverifier`); Jérôme Feret, *"Static Analysis of
  Digital Filters"*, ESOP 2004 (quadratic ellipsoid domain in `Astrée`);
  Torsten Anders, `https://github.com/tanders/strasheela`; Donya Quick & Paul
  Hudak, *"Grammar-Based Automated Music Composition in Haskell"*, FARM 2013
  (`Kulitta`); Recommendation `ITU-R BS.1770-5` (normative + documentation +
  source).

### Domain 9 (Games, Puzzles, TCG Engines, & Virtual Economies)
- **`PuzzleScript`, `Ceptre`, `Ludii`, `Machinations`, `Archipelago`, `XMage`, &
  `Festival`:** `https://github.com/increpare/PuzzleScript`; Chris Martens,
  *"Ceptre: A Language for Modeling Generative Interactive Systems"*, AIIDE 2015
  (`https://github.com/chrisamaphone/ceptre`); Cameron Browne et al., *IEEE
  Transactions on Games* 2020 (`Ludii`); Joris Dormans, *"Engineering
  Emergence: Applied Theory for Game Design"*, PhD Thesis, Univ. of Amsterdam
  2012 (`Machinations`); `https://github.com/ArchipelagoMW/Archipelago`;
  `https://github.com/magefree/mage` (`XMage`); Yaron Shoham & Jonathan
  Schaeffer, *"The Festival Sokoban Solver"*, IJCAI 2021 (documentation +
  source).

### Domain 10 (Smart-Home, `Matter`, & IoT Automation)
- **`SOTERIA`, `IoTGuard`, `IoTSAN`, `MenShen`, `iRuler`, `AutoTap`,
  `HAWatcher`, `IoTMon`, & `Matter`:** Z. Berkay Celik, Patrick McDaniel, &
  Gang Tan, *"SOTERIA: Automated IoT Safety and Security Analysis"*, USENIX ATC
  2018, and *"IoTGuard: Dynamic Enforcement of Security and Safety Policy in
  Commodity IoT"*, NDSS 2019; Dang Tu Nguyen et al., *"IoTSAN: Fortifying the
  Safety of IoT Systems"*, ACM CoNEXT 2018; Lei Bu et al., *"Systematically
  Ensuring The Confidence of Real-Time Home Automation IoT Systems"* (`MenShen`),
  *ACM TCPS* 2018; Qi Wang et al., *"Charting the Attack Surface of
  Trigger-Action IoT Platforms"* (`iRuler`), USENIX Security 2019; Lefan Zhang
  et al., *"Trace2Tap / AutoTap: Synthesizing and Repairing Trigger-Action
  Programs Using LTL Properties"*, ICSE 2020
  (`https://github.com/UChicagoSUPERgroup/autotap`); Chenglong Fu et al.,
  *"HAWatcher: Semantics-Aware Anomaly Detection for Appified Smart Homes"*,
  USENIX Security 2021; Wenbo Ding & Hongxin Hu, *"On the Safety of IoT Device
  Physical Interaction Control"* (`IoTMon`), ACM CCS 2018;
  `https://github.com/project-chip/connectedhomeip` (`Matter`) (normative +
  documentation + source).

---

### Part II — Historical Verification Failure Postmortem Evidence

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

### Part I — Real-World Tool Survey Revalidation

To revalidate the findings in this report when Anneal's `trusted/lean/` semantic
primitives or an upstream domain tool evolves:

1. **Structural Signature Check against Anneal's `trusted/lean/` Kernel:**
   Verify that the four primitive interfaces used in Sections 3.1–3.12 remain
   present and compositional:
   - `Language SemObs` (`Prog`, `Query`, `Out`, `obs : Out → SemObs`, and `sem :
     Prog → Query → Partial (Out → Prop)`);
   - `BehaviorCodec L₁ L₂` (`encodeQuery`, `decodeQuery`, `encodeOut`,
     `decodeOut : L₂.Out → Option L₁.Out`, `obs_decodeOut`, `Compiles`, and
     `Abstracts`);
   - `EventualBehaviorOf`, `StepResult.externalCall boundaryInv branches`,
     `InhabitedPre`, and `ProductiveOn`;
   - `VerificationResult policy waived obligations` (`ob.id ∈ waived ∨
     ob.prop`).
2. **Targeted Domain Certificate Probes:**
   - **Domains 1 & 7 (`Cedar` & `Faial`):** Inspect `cedar-policy/cedar-spec`
     (Lean 4 evaluator theorems) and `umb-svl/faial` (Coq memory-access
     protocol soundness theorems) to confirm their mechanized interfaces continue
     to match `Compiles` and `Abstracts`.
   - **Domains 2, 3, & 8 (`α,β-CROWN`, `helve`, & `Astrée` Ellipsoids):**
     Check that dual certificates ($(\alpha, \beta)$ linear bounds, inductive
     Horn/BDD state invariants $I$, and discrete Lyapunov matrices $A^\top P A -
     P \prec 0$) remain checkable via upward `Abstracts` without modifying
     `trusted/lean/`.
   - **Domains 4, 5, 6, 9, & 10 (Anti-Vacuity Probes):** Confirm that for any
     domain instantiation, removing `ProductiveOn` or `obs_decodeOut` re-admits
     the cataloged degenerate solutions (empty `M-30` G-code, zero-door BIM
     floorplans, `display: none` layouts, unsolvable puzzles, or non-quiescent
     IoT cascades).
3. **Corpus Metadata Validation:**
   Run `python3 tools/reference.py check` from the `reference` worktree root to
   verify `REPORT.json` schema compliance and `CATALOG.json` consistency.

### Part II — Historical Verification Failure Postmortem Revalidation

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
