# Real-World Verification Tools and Historical Failure Postmortems Across Computational Law, DeFi, Mechanism Design, Voting, Clinical Pathways, Aviation/Maritime Rules, and Regulatory Compliance

## Summary

### Part I — Real-World Verification, Synthesis, and Compilation Tool Landscape

Formal verification and executable specification systems across statutory law,
commercial derivatives, decentralized finance (DeFi), financial market
infrastructure, economic mechanism design, game theory, electronic voting,
clinical medicine, cyber-physical transport rules, and regulatory compliance
repeatedly confront four structural failure modes:

1. **Antecedent and precondition vacuity:** Over-constrained statutory
  eligibility rules, mutually contradictory clinical trial inclusion criteria,
  or off-equilibrium zero-probability game histories make standard partial
  correctness assertions (`pre q → post q out`) hold vacuously while leaving
  real citizens, patients, or market states unhandled.
2. **Unchecked representation and unit codecs:** Lowering decimal tax statutes,
  rational automated market maker (AMM) curves, clinical drug-dosing formulas,
  or binary exchange wire formats into machine integers introduces rounding
  arbitrage, unit-confusion overdoses, and step-count mismatches ($1$ logical
  specification step lowering to $k$ target loop iterations).
3. **Open-world callback and solver escapes:** External ERC-20/flash-loan token
  hooks, unverified mixed-integer linear programming (MILP) auction solvers, and
  administrative or clinical hold callbacks violate internal invariants if
  pre-call boundary invariants and demonic post-call framing are not enforced.
4. **Cross-obligation explosion from local waivers:** Regulatory waivers
  (Medicaid Section 1115 waivers, board consent overrides, MILP solver timeout
  fallbacks, or hardware safety-case assumptions) placed on the left-hand side
  of an implication (`→`) allow a single inconsistent or violated local
  assumption to discharge unrelated safety obligations via `False.elim`.

This report surveys 65 concrete real-world tools and formal frameworks across 10
socio-technical, financial, economic, clinical, and regulatory domains and
demonstrates that Anneal's four core `trusted/` primitives—(1) `Language` with
observable quotienting (`SemObs`) and `Partial` (`defined : Prop`,
`val : defined → B`, `Partial.ub`), (2) `BehaviorCodec` / `PartialBehaviorCodec`
with `Compiles` and `Abstracts`, (3) `ProductiveOn` and `InhabitedPre` paired
with `EventualBehaviorOf` and `StepResult.externalCall`, and (4) positive
per-obligation `VerificationResult` / `ScopedVerificationResult` gated by
`TrustPolicy`—provide a unified, kernel-checked foundation capable of expressing
the verification obligations of every surveyed system without adding
domain-specific axioms to `trusted/lean/`.

### Part II — Historical Verification, Compiler, and Operational Failure Postmortems

Formal verification, statutory compilation, economic mechanism design, and
safety-critical certification fail in production far more often from
**specification boundary gaps, vacuous assumptions, compiler/lowering mismatch,
and optimistic external-call framing** than from soundness bugs inside a core
proof kernel. Across four high-consequence domains—decentralized finance (DeFi)
and smart-contract verification, statutory tax and social-benefit engines,
electronic voting and financial/auction market clearing, and clinical medical
devices and airborne collision-avoidance rulebooks—historical postmortems
converge on four structural failure classes that map directly onto Anneal's four
trusted primitives (`Language` / `Partial`, `BehaviorCodec` / `Compiles` /
`Abstracts`, `StepResult.externalCall` / `EventualBehaviorOf` / `ProductiveOn` /
`InhabitedPre`, and positive per-obligation `VerificationResult` /
`TrustPolicy`):

1. **Whole-unit invariant bypass, compiler lock-slot miscompilation, and
   optimistic callback framing in DeFi:**
   - In the **Euler Finance exploit (\$197M, March 13, 2023)**, governance
     upgrade EIP-14 added `EToken.donateToReserves` without the mandatory
     `checkLiquidity` health-factor check enforced by other balance-mutating
     functions, allowing an attacker to intentionally self-inflict unbacked bad
     debt and profit via discounted self-liquidation.
   - In the **Curve Finance / Vyper compiler re-entrancy exploit (\$70M, July
     30, 2023)**, source contracts annotated multiple entrypoints with
     `@nonreentrant('lock')`, but a storage-slot allocation bug in Vyper
     `0.2.15`–`0.3.0` (`data_positions.py`) assigned distinct storage slots to
     each function, turning source-level mutual exclusion into target-bytecode
     cross-function re-entrancy.
   - Across **Wormhole (\$324M, Feb 2022)**, **Beanstalk (\$182M, Apr 2022)**,
     **Nomad (\$190M, Aug 2022)**, **Mango Markets (\$110M, Oct 2022)**,
     **Lendf.Me / ERC-777 (\$25M, Apr 2020)**, **Balancer / Curve read-only
     re-entrancy**, and **ERC-4626 empty-vault share inflation**, exploits
     succeeded at cross-contract boundaries where models assumed external token
     transfers were side-effect-free (`HAVOC_ECF`), omitted representation
     validity on spoofed capability handles (`Sysvar: Instructions`), or failed
     to enforce rounding-direction conservation.
   - In industrial smart-contract provers (**Certora Prover**, **KEVM**, and the
     **Aptos/Sui Move Prover and Bytecode Verifier**), rules routinely passed
     vacuously when `require` preconditions over-constrained reachable states
     (necessitating `--rule_sanity`), when default `HAVOC_ECF` summaries hid
     re-entrant callbacks into the caller or sibling view functions, or when
     unverified lowering and reference-borrow checks diverged from VM semantics.
2. **Default-exception priority inversions, temporal aggregation mismatches, and
   non-atomic ledger synchronization in statutory and accounting systems:**
   - Reverse-engineering the **French DGFiP `M`-language income tax code**
     (`Mlang`, CC 2021) and formalizing **French family benefits and US tax
     statutes in `Catala`** (ICFP 2021) exposed statutory contradictions,
     missing default branches, and floating-point/truncation workarounds in
     official state tax and benefit engines.
   - Australia's **Robodebt automated debt-recovery scheme (2015–2019, Royal
     Commission Final Report July 7, 2023)** and **Social Security Act 1991 s
     1073B income apportionment** unlawfully substituted coarse annual
     tax-office income averages (`ATO / 26`) for statutory fortnightly
     entitlement predicates—an unsound downward refinement of a non-linear
     statutory operator.
   - The **UK Post Office Fujitsu Horizon scandal (1999–2015, *Bates & Others v
     Post Office Ltd* [2019] EWHC 3408 (QB))** demonstrated how UI freeze
     retries (**Dalmellington bug**), duplicate database inserts (**Callendar
     Square bug**), and local-cache/central-ledger desynchronization (**Receipts
     and Payments Mismatch bug**) violated double-entry conservation while legal
     presumptions treated the unverified ledger as infallible.
   - **US SNAP and Medicaid (MAGI vs. non-MAGI) eligibility engines** suffered
     from contradictory cross-statutory exception predicates (bureaucratic
     Catch-22s leaving statutory cohorts uninhabited) and discontinuous marginal
     effective tax rate (METR $> 100\%$) benefit cliffs.
3. **Cryptographic proof-check omissions, fractional vote-transfer
   non-termination, dead-code deployment drift, and Sybil equilibrium collapse
   in voting and markets:**
   - In the **SwissPost / Scytl e-voting system (2019, Haines, Lewis, Pereira,
     and Teague, IEEE S&P 2020)**, the Universal Verifiability specification and
     verifier omitted the constructibility/zero-knowledge proof that Bayer-Groth
     shuffle commitment parameters were generated without a known trapdoor,
     allowing a malicious mixnet or electoral authority to forge passing audit
     proofs for altered tallies.
   - Formal verification of **Australian Senate Single Transferable Vote (STV)**
     tabulation by Pattinson, Tiwari, and Goré uncovered discrepancies between
     natural-language electoral statutes and production counting software
     (`AEC EasyCount`) around fractional transfer value truncation, quota
     exhaustion, and multi-way tie-breaking.
   - **Knight Capital's \$440M loss (August 1, 2012, SEC Release No. 34-70694)**
     stemmed from an incomplete binary deployment to 1 of 8 `SMARS` servers that
     re-activated dead `Power Peg` code when a retired order-flag bit was reused
     without an cumulative fill-quantity state invariant.
   - In **multi-item Vickrey-Clarke-Groves (VCG) and second-price spectrum
     auctions (New Zealand 1990 TV/radio spectrum auction; Ausubel & Milgrom
     2006)**, truthful bidding collapsed under complementary goods, thin
     competition (a NZ\$100,000 valuation winning for NZ\$6), and Sybil/shill
     bidding because single-agent deviation models ignored coalitional/Sybil
     splitting.
4. **Interactive number-entry state-machine anomalies, concurrent interlock
   races, and hybrid advisory reversals in medical devices and aviation:**
   - PVS verification of the **Becton Dickinson / CareFusion Alaris GP infusion
     pump** by Masci, Thimbleby, Curzon, and Oladimeji uncovered keystroke
     handling, chevron saturation/wrapping, and decimal rounding anomalies where
     minor clinician key-slips produced silent 10x–100x dosing changes.
   - The **Therac-25 radiation therapy overdoses (1985–1987, Leveson & Turner
     1993)** resulted from an 8-bit shared-counter wraparound (`Class3`
     incrementing to `0` every 256 ticks) and a 8-second terminal cursor-edit
     race (`Data Entry Complete` hiding subsequent turntable mode edits from the
     beam-spreader interlock).
   - The **2002 Überlingen mid-air collision (BFU Report AX001-1-2/02)** and
     formal verification of **TCAS II / ACAS X** in `KeYmaera` by Jeannin,
     Platzer, et al. (TACAS 2015 / EMSOFT 2015 / STTT 2017) exposed unsafe
     advisory regions where delayed reversal logic (`TCAS II v7.0` vs.
     `Change 7.1`) and discrete lookup-table interpolation under pilot response
     delay violated continuous kinematic safe-separation envelopes.

## Applicability

### Part I — Real-World Verification and Compilation Tools Applicability

The findings in this report apply to Anneal's trusted refinement core and small
step transition infrastructure across three pinned repository states, evaluated
against 10 families of external specification, simulation, and verification
toolchains:

| Subject Group | Pinned Coordinates | Role in This Report |
| :--- | :--- | :--- |
| `Anneal (trusted-refinement-core)` | `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` (`trusted/lean/Trusted/Refinement.lean`, `trusted/lean/Trusted/StepResult.lean`) | Defines `Preorder`, `Partial`, `Partial.ub`, `Language`, `Language.SpecOn`, `Language.WellFormedOn`, `Compiles`, `Abstracts`, `Compiler.Verified`, `TrustedAssumption`, `TrustPolicy`, and `VerificationResultOn`. |
| `Anneal (x86-backend-pipeline)` | `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457` (`trusted/lean/Trusted/X86Semantics.lean`, `trusted/audit/TrustedBoundary.lean`) | Defines target machine lowering and the `.olean` kernel boundary auditor. |
| `Anneal (reference hardening corpus)` | `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` (`support/BehaviorCodecExpressiveness.lean`, `support/StructuralExternalCallAndCanaries.lean`, `support/ProofGatedCompilationAndTrustPolicy.lean`) | Mechanizes `BehaviorCodec`, `PartialBehaviorCodec`, `EventualBehaviorOf`, `ProductiveOn`, `InhabitedPre`, `StepResult.externalCall`, and `ScopedVerificationResult`. |
| Domains 1–10 Tool Ecosystems | Primary repositories, specifications, and archival DOIs listed in `REPORT.json` and `## Evidence` | Concrete external compilers, DSLs, model checkers, theorem-prover libraries, and domain engines mapped onto Anneal's four primitives. |

This report establishes architectural correspondence and semantic encodings
between the surveyed external tools and Anneal's Lean 4 definitions. It does not
claim that Anneal currently bundles parsers or front-end extractors for those
external DSLs; rather, it specifies how each tool's verification contract and
TCB boundary map onto Anneal's existing `trusted/` kernel types when verifying
Rust implementations or certificates derived from those systems.

### Part II — Historical Verification and Operational Failures Applicability

The findings in this report apply to the ten subject groups recorded in
`REPORT.json`:

1. **Anneal's core verification framework** at
   `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`
   (`trusted/lean/Trusted/Refinement.lean`,
   `trusted/lean/Trusted/StepResult.lean`, and
   `trusted/lean/Trusted/MirSemantics.lean`) and the **Anneal reference corpus
   verification-hardening packages** at
   `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`
   (`anneal-behavior-codec-and-progress-refinement-2026`,
   `anneal-polar-ctfe-admission-and-semantic-polarity-2026`,
   `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`,
   `anneal-rustc-obligation-inventory-and-single-source-codegen-2026`, and
   `anneal-structural-external-calls-and-tcb-mutation-testing-2026`).
2. **Historical production failures, vulnerability disclosures, judicial
   findings, and formal-methods postmortems** across smart contracts and DeFi
   (2020–2023), statutory tax/welfare and accounting systems (1999–2023),
   electronic voting, auctions, and equity order routing (1990–2020), and
   medical devices and airborne collision avoidance (1985–2017).

The relationship among subjects is **comparative and architectural**: historical
failures in external domains are analyzed from primary postmortems, judicial and
regulatory records, and peer-reviewed formal verification literature, and each
failure mechanism is mapped to the exact structural invariant in Anneal's four
trusted primitives that prevents the analogous defect class when Anneal is
instantiated for Rust verification or domain-specific compilation/certification.

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

### Finding 1: Statutory Law, Legislative Default Calculi, and Tax-Benefit Microsimulation Engines

`Basis: normative + documentation + source + derived`

#### 1.1 Domain Goals, Target Users, and Concrete Tool Inventory

Statutory law and administrative rulebooks (such as the US Internal Revenue
Code, the French *Code général des impôts* and *Code de la sécurité sociale*,
and social-benefit eligibility statutes) organize legal rules using **defeasible
default logic**: a general statutory clause defines a baseline tax liability or
benefit entitlement, and scattered subsections, cross-references, and later
legislative amendments override that baseline under specific factual predicates.
Eight concrete systems represent the state of practice:

- **`Catala` (`CatalaLang/catala`):** A literate legislative programming
  language developed at Inria for socio-fiscal statutes. Target users are
  interdisciplinary pairs of legislative drafters/lawyers and software engineers
  at government agencies (such as the French *Direction générale des Finances
  publiques* [DGFiP] and *Caisse nationale des allocations familiales* [CNAF]).
- **`OpenFisca` (`openfisca/openfisca-core`):** A Python/NumPy vectorized
  tax-benefit microsimulation platform created by France's Etalab and used to
  model national socio-fiscal systems (`openfisca-france`, `openfisca-uk`,
  `openfisca-tunisia`) for economists, parliamentary budget offices, and civic
  welfare simulators (`Mes Aides`).
- **`Blawx` (`Lexpedite/blawx`):** A web-based visual Rules-as-Code environment
  created by Jason Morris that compiles natural-language statutory encodings to
  Answer Set Programming (`s(CASP)`), targeting public-sector legal analysts and
  policy drafters.
- **`L4` (`smucclaw/dsl`):** A deontic and defeasible domain-specific language
  developed at Singapore Management University's Centre for Computational Law
  (CCLAW) by Meng Weng Wong and collaborators, targeting statutory drafters,
  regulatory compliance officers, and insurance/legal engineers.
- **`PolicyEngine` (`PolicyEngine/policyengine-us`, `policyengine-uk`):** A
  open-source microsimulation and policy-scoring engine (evolved from the
  OpenFisca architecture) used by think tanks, legislative staffs, and
  benefit-access platforms (`MyFriendBen`) to compute household marginal
  effective tax rates (METRs) and macroeconomic budgetary impacts.
- **`PSL Tax-Calculator` (`PSLmodels/Tax-Calculator`):** The Policy Simulation
  Library's Python microsimulation model of US federal individual income and
  payroll taxes, used by the US Joint Committee on Taxation (JCT), AEI,
  Brookings, and academic public-finance economists.
- **`Oracle Intelligent Advisor` (formerly `Oracle Policy Automation` / `Haley`
  / `RuleBurst`):** An enterprise commercial natural-language rules engine
  widely deployed by national tax authorities and social-welfare ministries (US
  state Medicaid/SNAP portals, UK, Australia, New Zealand) to execute
  eligibility determinations and interactive citizen interviews.
- **French `DGFiP M` Language (`MLang/mlang`):** The domain-specific array and
  rule description language maintained since 1990 by the French Ministry of
  Economy and Finance (DGFiP) to compute the official income tax (*impôt sur le
  revenu*) for 40 million French households.

#### 1.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Computational law evolved through three distinct generations:

1. **Batch Mainframe and Legacy Array DSLs (`DGFiP M`, 1990–present):** `M` was
  designed to transcribe paper tax-return worksheets (`Form 2042` box codes)
  into acyclic or bounded-loop C code. It prioritizes raw batch throughput and
  direct correspondence to tax-form line numbers (`tgv` array variables), but
  lacks lexical scoping, user-defined functions, and native exception priority,
  forcing maintainers to encode statutory overrides via brittle Boolean flag
  cascades.
2. **Vectorized Economic Microsimulation (`OpenFisca`, `PSL Tax-Calculator`,
  `PolicyEngine`, 2011–present):** Designed by economists rather than PL
  theorists, these systems represent statutes as dependency DAGs of NumPy array
  operations over 100,000+ synthetic or CPS/PUF survey households. They excel at
  macroeconomic distributional analysis and reform scoring, but sacrifice
  single-household formal guarantees: NumPy IEEE-754 floating-point arithmetic
  diverges from statutory cent-rounding rules, and implicit array broadcasting
  can mask unhandled statutory branches.
3. **Formal Rules-as-Code Compilers (`Catala`, `L4`, `Blawx`,
  `Oracle Intelligent Advisor`, 2019–present):** Following Sarah Lawsky's
  formalization of the US Internal Revenue Code via Reiter's default logic (*"A
  Logic for Statutes"*, Florida Tax Review 2017) and Denis Merigoux, Nicolas
  Chataing, and Jonathan Protzenko's *Catala: A Programming Language for the
  Law* (ICFP 2021, DOI `10.1145/3473582`), `Catala` enforces **isomorphic
  literate programming**: every paragraph of statute is followed immediately by
  the `scope` definition and prioritized exception clause that implements it.
  `Blawx` prioritizes goal-directed abductive explanation and counterfactual
  querying via `s(CASP)` top-down execution with negation-as-failure, whereas
  `L4` combines regulated transition systems (timed automata with `MUST`/`MAY`/
  `SHANT` deontic modalities and `HENCE`/`LEST` reparation clauses) with
  transpilation to Petri nets, SMT, and natural-language explanations.

#### 1.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool | Semantic Core | Arithmetic Model | Verification / Solver Backend | TCB & Soundness Gaps |
| :--- | :--- | :--- | :--- | :--- |
| `Catala` | Prioritized default calculus ($D_{\text{calc}} \to \lambda_{\text{calc}}$) mechanized in `F*` | Exact GMP rationals & cent-rounded decimals | `Z3` SMT proof obligations + OCaml/C/Python/Java extraction | Unverified OCaml parser/driver and `Z3` SMT solver; `F*` proof covers core $D_{\text{calc}} \to \lambda_{\text{calc}}$ translation. |
| `DGFiP M` | Untyped flat global variable array (`double`) + macro loops | IEEE-754 `double` with custom `arr()` floor/round macros | None natively (analyzed via `MLang` + `Catala` differential fuzzing) | Entire `M`-to-C compiler, uninitialized box defaults (`0.0`), and floating-point precision loss. |
| `OpenFisca` / `PolicyEngine` | Vectorized Python/NumPy entity-variable-period DAG | `float32`/`float64` NumPy arrays | Unit tests & CBO/JCT aggregate benchmark validation | Python runtime, NumPy float rounding, and absence of static exhaustiveness or conflict checking. |
| `PSL Tax-Calculator` | Procedural Python functions per IRS schedule/worksheet | `float64` arrays + parameter JSON schedules | Regression diffs against IRS PUF / Taxsim | Python runtime; imperative mutation order across tax calculation stages. |
| `Blawx` | Goal-directed constraint Answer Set Programming (`s(CASP)`) | Prolog/CLP(Q) rationals or floats | Abductive proof-tree search in `s(CASP)` / SWI-Prolog | Non-stratified negation loops; SWI-Prolog/`s(CASP)` runtime; Blockly-to-Prolog translator. |
| `L4` | Deontic default logic + timed Hohfeldian state machines | Arbitrary-precision integers/decimals | `Z3` SMT, `UPPAAL` timed automata, `ASP` | Multi-target transpiler written in Haskell/TypeScript; unverified semantic preservation across backends. |
| `Oracle Intelligent Advisor` | Three-valued Kleene logic (`true`, `false`, `uncertain`/`unknown`) | Fixed-point decimal currency | Static conflict/redundancy rule reports | Proprietary closed-source Java/.NET rule engine and Word/Excel rule-table parser. |

#### 1.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial` (`Trusted/Refinement.lean:242-308`):**
   - `Prog`: A legislative program in `Catala`'s default calculus
     `DefaultGroup Priority Outcome`, a `DGFiP M` rule graph, or a Rust tax
     engine binary extracted by `anneal-rustc-capture`.
   - `Query`: A household socio-fiscal filing record `HouseholdFacts` (income
     schedules, dependents, residency intervals, disability status).
   - `Out`: The full administrative determination record (line-item worksheet
     variables, applied statutory citations, and net assessment).
   - `SemObs`: The legally dispositive outcome
     `(NetTaxCents × EligibilityFlag × MandatoryReportingFlags)`, quotienting
     away intermediate worksheet boxes (such as `DGFiP M`'s 3,000 internal `tgv`
     variables).
   - `Partial.ub` (`defined := False`): Directly captures `Catala`'s two runtime
     error states—`ConflictError` (two exceptions to the same base rule fire
     simultaneously on `q` with incomparable priority,
     $\mathsf{Obligatory}(A) \land \mathsf{Forbidden}(A)$) and arithmetic
     overflow/division-by-zero in statutory phase-out fractions. When
     `defined = True`, `val` holds the legally valid determinations (a singleton
     for deterministic tax codes, or a multi-element set when the statute grants
     a taxpayer election).
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`
  (`Trusted/Refinement.lean:369-385`):**
   - `Compiles StatuteLang RustAgencyLang codec catalaStatute rustTaxEngine`:
     Proves that a production Rust tax calculator (`t`) refines the enacted
     `Catala` statutory specification (`s`). Where the statute permits
     administrative discretion, `t` refines the allowed outcome set
     (`t ≤ codec.toMorphism s`).
   - `Abstracts FiscalEnvelopeLang StatuteLang codec metrsBound catalaStatute`:
     Proves that a `PolicyEngine` or CBO piecewise-linear marginal effective tax
     rate (METR) envelope (`v`) soundly over-approximates the micro-level
     statutory code (`s`).
   - `PartialBehaviorCodec` (`decodeOut : L₂.Out → Option L₁.Out`): Maps binary
     IRS Form 1040 / `DGFiP` box outputs back to statutory determinations;
     `decodeOut = none` rejects negative non-refundable credits or invalid
     filing status combinations, while `obs_decodeOut` guarantees cent-exact
     preservation (catching `OpenFisca` / `DGFiP M` IEEE-754 float drift).
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`ProductiveOn pre prog` & `InhabitedPre pre`:** In `Catala`, if no
     default rule is enabled on a query `q`, evaluation raises `EmptyError`
     (modeled as `.stuck` in `ReachesPrefix`). Furthermore, in `Blawx`, `L4`,
     and `Oracle Intelligent Advisor`, an agency worksheet that conjoins two
     mutually inconsistent cross-referenced definitions (a bureaucratic
     Catch-22) makes standard partial correctness (`pre q → Safe`) hold
     vacuously. Requiring `InhabitedPre pre` for every statutory benefit tier
     forces a constructive citizen witness `q₀`, and `ProductiveOn pre prog`
     guarantees that every qualifying household reaches a defined, non-empty
     determination (`EmptyError` and `ConflictError` are both impossible).
   - **`EventualBehaviorOf`:** Bridges a 1-step declarative `Catala` scope
     definition to a $k$-step iterative IRS worksheet or `DGFiP M` fixed-point
     tax-credit loop without `Classical.choice`.
   - **`StepResult.externalCall`:** Models `Oracle Intelligent Advisor`'s
     `uncertain` external interview callbacks and cross-agency database lookups
     (e.g., querying Social Security disability status mid-evaluation),
     enforcing statutory authority preconditions (`boundaryInv`) before external
     inquiry.
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`
  (`Trusted/Refinement.lean:418-471`):**
   - Models statutory grandfather clauses, transitional tax-year safe harbors,
     and state-specific Medicaid Section 1115 federalism waivers positively
     (`ob.id ∈ waived ∨ ob.prop` gated by `TrustPolicy.isAllowed`), preventing a
     waived legacy sub-schedule from exploding verification of the rest of the
     tax code via `False.elim`.

---

### Finding 2: Commercial Legal Contracts, Financial Derivatives Standards, and Cap-Table Conveyancing

`Basis: normative + documentation + source + derived`

#### 2.1 Domain Goals, Target Users, and Concrete Tool Inventory

Commercial legal contracts, over-the-counter (OTC) financial derivatives, and
venture-capital equity conveyancing schedules are stateful, multi-party
protocols governing cash-flow exchanges, option exercises, collateral margin
calls, and liquidation waterfalls. Nine concrete tools and standards anchor this
domain:

- **`ISDA CDM` & `Rune` / `Rosetta` (`finos/common-domain-model`,
  `finos/rune-dsl`):** The International Swaps and Derivatives Association's
  Common Domain Model, hosted by FINOS and written in Regnosys's `Rosetta` /
  `Rune` DSL. Target users are Tier-1 investment banks, clearinghouses (LCH,
  CME), and derivatives regulators standardizing trade lifecycle events
  (execution, clearing, margining, close-out netting).
- **`ACTUS` (`actusfrf/actus-core`):** The Algorithmic Contract Types Unified
  Standards, a mathematical taxonomy and Java/C++/Python reference engine that
  represents almost all financial instruments (PAM principal-at-maturity loans,
  ANN annuities, SWAPS, OPTNS) as deterministic state-transition machines over
  32 standard contract types for central banks and risk managers.
- **`Marlowe` (`input-output-hk/marlowe-cardano`, `marlowe`):** A decidable,
  bounded financial contract DSL developed by Simon Thompson, Pablo Lamela
  Seijas, and IOG for Cardano, targeting financial engineers and non-programmer
  domain experts via visual Blockly/Haskell/TypeScript authoring and automated
  `Z3` static analysis.
- **`LexiFi MLFi` (`LexiFi`):** The commercial OCaml-derived functional language
  for structuring, pricing, and lifecycle management of complex OTC derivatives
  and structured products, built on Simon Peyton Jones, Jean-Marc Eber, and
  Julian Seward's seminal ICFP 2000 combinator calculus (*"Composing Contracts:
  An Adventure in Financial Engineering"*, DOI `10.1145/351240.351267`).
- **`Daml` (`digital-asset/daml`):** Digital Asset's Haskell-inspired smart
  contract language based on a strict **signatory/observer/controller**
  authorization and privacy calculus, used by securities exchanges (ASX, HKEX,
  DTCC, Canton Network) to model bilateral and multilateral settlement
  workflows.
- **`Accord Project` — `Concerto` & `Ergo` (`accordproject/ergo`,
  `accordproject/concerto`):** A Linux Foundation open-source framework for
  Smart Legal Contracts created by Jérôme Siméon and Clause.io, pairing
  natural-language legal templates (`CiceroMark`), typed data models
  (`Concerto`), and a strongly typed functional contract execution language
  (`Ergo`) compiled to Coq (`Q*cert`) and JavaScript.
- **`Open Cap Table Coalition (OCF)`
  (`Open-Cap-Table-Coalition/Open-Cap-Format-OCF`):** An open industry JSON
  schema and calculation reference initiated by Carta, Morgan Stanley, LTSE, and
  Goodwin Procter to standardize corporate capitalization tables,
  preferred-stock liquidation waterfalls, and convertible-note/SAFE conversions.
- **`Stipula` (`stipula-language/stipula`):** A stateful legal contract DSL
  developed by Cosimo Laneve and Adele Veschetti (University of Bologna) with
  first-class **linear assets** (`assets`) and **normative agreement fields**
  that prevent double-spending or asset duplication by syntax.
- **`Symboleo` (`Smart-Contract-Modelling-uOttawa/Symboleo-JS-2`):** A formal
  specification language developed by Daniel Amyot, John Mylopoulos, and
  collaborators based on UFO-L (Unified Foundational Ontology for Legal
  Relations), modeling contracts as concurrent statecharts of **Obligations**
  and **Powers** verified via `NuXmv` model checking.

#### 2.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Modern financial and legal contract languages descend from two foundational
lineages:

1. **Compositional Denotational Combinators (`Peyton Jones-Eber` $\to$
  `LexiFi MLFi` $\to$ `Marlowe` $\to$ `Findel`):** Peyton Jones and Eber (ICFP
  2000) discovered that arbitrary financial derivatives decompose into seven
  algebraic combinators (`zero`, `one(currency)`, `give(c)`, `and(c1, c2)`,
  `or(c1, c2)`, `cond(obs, c1, c2)`, `when(obs, c)`). `LexiFi MLFi` extended
  this calculus with concrete settlement calendars, path-dependent fixings, and
  Monte Carlo/PDE pricing compilation. `Marlowe` intentionally **restricts**
  this combinator algebra by banning recursion and bounding every `When` timeout
  by a finite slot number: in exchange for giving up Turing completeness, every
  `Marlowe` contract has a finite number of execution paths and admits
  push-button `Z3` SMT verification of conservation of funds and
  no-locked-assets.
2. **Event-State-Obligation Calculi (`ISDA CDM`, `ACTUS`, `Daml`, `Symboleo`,
  `Stipula`):** Rather than algebraic payoff trees, `ISDA CDM` and `Daml` model
  contracts as permissioned state transitions (`PrimitiveEvent` / `Choice`).
  `Daml` enforces **double-entry authorization** (no contract can be created or
  archived without the cryptographic consent of all listed `signatory` parties),
  while `Stipula` uses a linear resource type system where moving an asset from
  escrow `a` to party `p` (`a -o p`) consumes `a`. By contrast, corporate
  cap-table tools (`OCF`) define preferred-stock liquidation waterfalls and
  anti-dilution ratchets declaratively, which in practice induces **simultaneous
  algebraic fixed-point equations** when convertible notes convert based on a
  fully diluted share count that itself depends on the conversion price.

#### 2.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool / Standard | Expressiveness & Termination | Asset / Conservation Model | Formal Verification Stack | Primary TCB & Limitations |
| :--- | :--- | :--- | :--- | :--- |
| `Marlowe` | Strictly bounded AST (no loops/recursion; finite `Timeout` horizons) | Explicit internal `accounts : Map (Party, Token) Integer`; automatic refund on `Close` | Built-in `Z3` SMT symbolic execution + Isabelle/HOL mechanized semantics (`Marlowe_Semantics`) | Cardano Plutus V2 validator compiler and on-chain transaction size limits. |
| `LexiFi MLFi` | Total combinator AST over stochastic observables | Cash-flow stream algebra (no stateful escrow locking) | Type checking + algebraic equivalence rewriting | Closed-source OCaml compiler and numerical PDE/Monte Carlo pricers. |
| `Daml` | Turing-complete functional steps (`Update` monad) | UTXO contract archival (`create`/`exercise`) + signatory authority | Static type checking (early `Daml-LF` formalization in Isabelle/HOL) | `Daml-LF` engine, Ledger API, and absence of built-in termination proofs for recursive choices. |
| `Accord Project` / `Ergo` | Pure functional request/state transition (no unbounded loops in `Q*cert` core) | Record-based obligation emission (no native linear asset type) | Mechanized compilation from `Ergo` to `Q*cert` (NRA/NNRC) in Coq | Natural-language `CiceroMark` template parser and JS runtime host. |
| `ISDA CDM` / `Rune` | Pure functional expressions with bounded list comprehensions | Post-condition qualification rules (`condition` assertions on quantity conservation) | Runtime post-condition assertion checking; no built-in theorem prover | `Rune`-to-Java/Python/TypeScript code generators and unverified external market-data feeds. |
| `ACTUS` | Deterministic finite event schedule $\to$ state/payoff transitions | Explicit notional principal and accrued interest state variables | Reference test suite across 32 contract types | IEEE-754 floating-point arithmetic in Java/Python reference engines. |
| `Stipula` | Finite-state normative machine with timed events | Linear asset variables (`-o` move semantics) | Liquidity and asset-conservation static analyzers | Research prototype interpreter; unverified compilation to EVM/blockchain targets. |
| `Symboleo` | Reactive statecharts of Hohfeldian Obligations and Powers | Event-calculus predicates | Translation to `NuXmv` LTL/CTL model checking | Finite-domain abstraction gap between `Symboleo` specifications and `NuXmv` models. |
| `OCF` (Cap Tables) | JSON schema + iterative waterfall/conversion solvers | Share-count and dollar-payout vectors | Schema validation only | Floating-point/cent-rounding drift and non-convergence or non-monotonicity in circular SAFE/note conversions. |

#### 2.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial`:**
   - `Prog`: A `Marlowe` / `LexiFi` contract AST, a `Daml` template choice
     graph, an `ISDA CDM` close-out netting workflow, or a Rust `OCF` cap-table
     liquidation waterfall engine.
   - `Query`: A lifecycle trace of external market fixings, counterparty choice
     actions, default/cure notices, or an M&A exit valuation $V \ge 0$.
   - `Out`: The terminal distribution of cash flows, equity shares, and legal
     statuses across all parties.
   - `SemObs`: Net party payout vector `(PartyId → CurrencyAmount × ShareCount)`
     and terminal legal status (`Performed`, `DefaultAccelerated`, `Rescinded`).
   - `Partial.ub` (`defined := False`): Captures **conservation-of-funds
     breaches** ($\sum_i \text{payout}_i \neq V$), **negative share or cash
     allocations** (`Marlowe` `TransactionWarning.TransactionNonPositivePay`),
     **unauthorized signatory actions** (`Daml` authorization failures), or
     **double-conveyance of linear escrow assets** (`Stipula`).
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
   - `Compiles CharterSpecLang ClosingEngineLang codec ocfCharter rustWaterfall`:
     Proves that an executable Rust/spreadsheet M&A closing disbursement script
     (`t`) faithfully refines the corporate charter's preferred-stock waterfall
     (`s`).
   - `Abstracts ExposureEnvelopeLang IsdaCdmLang codec pfeBound isdaCsaContract`:
     Proves that a simplified Basel Potential Future Exposure (PFE) or `ACTUS`
     cash-flow bound (`v`) soundly abstracts every execution path of a multi-leg
     `ISDA CDM` Credit Support Annex (`s`).
   - `PartialBehaviorCodec`: Rejects closing outputs that leak fractional
     pennies or unallocated shares into dust accounts (`decodeOut = none`) and
     enforces exact conservation via `obs_decodeOut`.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`ProductiveOn` (Waterfall Fixed-Point Existence & `Stipula`/`Marlowe`
     Liquidity):** In `OCF` cap-table waterfalls with circular SAFE/convertible
     note dilution, if the contract specifies payouts declaratively as a fixed
     point, `ProductiveOn (fun V => V ≥ 0) waterfallProg` proves that **at least
     one valid, non-negative, cent-conserving payout solution exists for every
     exit valuation $V \ge 0$**. In `Marlowe` and `Stipula`, `ProductiveOn`
     directly formalizes **contract liquidity** (from every reachable funded
     state, there exists a finite sequence of steps ending in `Close` where all
     escrow accounts reach zero balance).
   - **`StepResult.externalCall`:** Models external valuation appraisers, `ISDA`
     calculation agents, or county title-recording callbacks, enforcing that
     `boundaryInv` (all required `Daml` signatory consents and Good Funds are
     locked in escrow *before* title release) holds at the external handoff.
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`:**
   - Models **board waivers, Series Preferred shareholder consent overrides
     (e.g., waiving an anti-dilution ratchet or notice window), and
     force-majeure carve-outs** positively (`ob.id ∈ waived ∨ ob.prop` gated by
     `BoardAndPreferredConsentPolicy`), ensuring a waived Series B notice clause
     cannot invalidate the conservation proof for Series A and common payouts.

---

### Finding 3: Smart Contracts, DeFi Economic Security, and Automated Market Maker Solvency

`Basis: normative + documentation + source + derived`

#### 3.1 Domain Goals, Target Users, and Concrete Tool Inventory

Smart contracts on the Ethereum Virtual Machine (EVM), Solana (SVM), Move
(Aptos/Sui), and Tezos/Concordium manage tens of billions of dollars in
Automated Market Makers (Uniswap v3/v4, Curve), lending protocols (Aave, Morpho,
MakerDAO), and tokenized vaults (ERC-4626) under fully adversarial open-world
execution. Nine core verification toolchains define this domain:

- **`Certora Prover` & `CVL` (`Certora/CertoraProver`):** An industrial
  SMT-based formal verification platform for EVM, Solana/Rust, Soroban/Wasm, and
  Sui/Move bytecode. Users (protocol engineers and security auditors at Aave,
  Lido, MakerDAO, Uniswap) write specifications in the **Certora Verification
  Language (CVL)** using relational rules, state invariants, storage `hook`s,
  and function `ghost` variables.
- **`Halmos` (`a16z/halmos`) & `Hevm` (`ethereum/hevm`):** Open-source bounded
  symbolic execution engines for EVM bytecode developed respectively by a16z
  Crypto (Daejun Park et al.) and DappHub / the Ethereum Foundation Formal
  Methods team, allowing Solidity developers to write parametric symbolic tests
  (`check_*(...)`) directly in Foundry test suites.
- **`KEVM` & `Kontrol` (`runtimeverification/evm-semantics`,
  `runtimeverification/kontrol`):** Runtime Verification's executable semantics
  of the EVM in the **K Framework** (`KEVM`) and its Foundry-integrated symbolic
  reachability prover (`Kontrol`), supporting unbounded loop invariants and
  Matching Logic proof generation.
- **`Move Prover` (`move-language/move`, `aptos-labs/aptos-core`):** An
  auto-active formal verifier for the Move language created by David L. Dill,
  Wolfgang Grieskamp, Shaz Qadeer, et al. (CAV 2020, DOI
  `10.1007/978-3-030-53288-8_7`), translating Move bytecode and `spec` blocks to
  `Boogie` and `Z3`/`CVC5`.
- **`Mi-Cho-Coq` (`nomadic-labs/mi-cho-coq`) & `ConCert` (`AU-COBRA/ConCert`):**
  Interactive theorem-prover frameworks in Coq/Rocq: `Mi-Cho-Coq` (Nomadic Labs)
  provides a typed GADT shallow/deep embedding and weakest-precondition calculus
  for Tezos Michelson scripts, while `ConCert` (Danil Annenkov, Jakob Botsch
  Nielsen, and Bas Spitters, CPP 2020, DOI `10.1145/3372885.3373829`) embeds
  multi-contract message-passing execution traces in Coq with `MetaCoq`
  extraction to Concordium (Rust), Tezos (CameLIGO), and Elm.
- **`Aeneas` (`AeneasVerif/aeneas`) & `Veridise Vanguard` / `OrCa`
  (`Veridise/Vanguard`):** Rust and smart-contract verification tools: `Aeneas`
  (Son Ho and Jonathan Protzenko, ICFP 2022) translates borrow-checked safe Rust
  (`Charon` LLBC) into pure functional Lean 4 / Coq / HOL4 / F* via symbolic
  backward functions, while `Veridise Vanguard` performs static taint and
  missing-validation analysis across Solana/Anchor, CosmWasm, and Move, paired
  with `[V] Specification Language` temporal/invariant checking (`OrCa`).
- **`Slither` (`crytic/slither`), `Echidna` (`crytic/echidna`), & `Medusa`
  (`crytic/medusa`):** Trail of Bits' static analyzer (`Slither`, lifting
  Solidity to SSA `SlithIR`) and stateful coverage-guided property fuzzers
  (`Echidna` in Haskell, `Medusa` in Go) that synthesize multi-transaction
  adversarial call sequences to falsify protocol invariants.
- **`Clockwork Finance` (`kushalbabel/Clockwork-Finance`):** A mechanized
  economic-security and Miner/Maximal Extractable Value (MEV) verification
  framework developed by Kushal Babel, Philip Daian, Mahimna Kelkar, and Ari
  Juels (IEEE S&P 2023, DOI `10.1109/SP46215.2023.10179346`) in the K Framework
  to compute upper bounds on attacker arbitrage profit across composed DeFi
  protocols.

#### 3.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Following the June 2016 DAO re-entrancy exploit
(\$60M) and the 2017 Parity MultiSig wallet freeze (\$150M), smart-contract
verification split across four design philosophies:

1. **Bytecode-Level Auto-Active SMT (`Certora Prover`, `KEVM`/`Kontrol`,
  `Halmos`, `Hevm`):** Because the Solidity compiler (`solc`) historically
  contained code-generation bugs and inline Yul assembly bypasses high-level AST
  checks, `Certora`, `KEVM`, and `Halmos` verify **compiled EVM bytecode**.
  `Certora` decompiles EVM bytecode into a tactical CFG (`TacProgram`),
  approximates nonlinear `U256` multiplication (`mulDiv`) via linear integer
  arithmetic (LIA) + NIA axiomatizations, and summarizes external calls via
  `HAVOC_ECF` (havocing all non-current-contract storage unless re-entrancy is
  enabled) or `DISPATCHER`. This achieves industrial scale on 10,000-line DeFi
  protocols, at the cost of loop unrolling bounds (`--loop_iter`) and potential
  false negatives when `HAVOC_ECF` assumes external calls do not re-enter.
2. **Resource-Linear Language Design (`Move Prover`):** Move eliminates two
  entire classes of EVM bugs at the type-and-bytecode level: assets (`struct`s
  without `copy` or `drop` abilities) are **linear resources** that cannot be
  duplicated or accidentally erased, and dynamic dispatch / re-entrant external
  callbacks are **banned by the Move VM** (all module calls form a strict DAG).
  Furthermore, the `Move Prover` uses a **reference-elimination transformation**
  (paralleling `Aeneas`'s backward functions) to translate mutable borrows
  (`&mut T`) into pure functional value updates in `Boogie`, enabling rapid SMT
  verification without heap separation logic.
3. **Foundational Coq Trace Embeddings (`Mi-Cho-Coq`, `ConCert`):** While
  `Mi-Cho-Coq` verifies single-contract functional correctness, `ConCert`
  explicitly models the **blockchain execution layer (`ChainBuilder`)** with
  configurable depth-first or breadth-first action queues—allowing `ConCert` to
  mechanize the exact 2016 DAO re-entrancy exploit in Coq by proving that a
  contract valid under breadth-first message execution fails under EVM-style
  depth-first call-stack execution!
4. **Economic Game-Theoretic Composition (`Clockwork Finance`):** Standard
  functional correctness (`transfer` moves $x$ tokens) does not prevent an
  attacker from combining a flash loan, an AMM price-oracle manipulation, and a
  lending liquidation to extract millions of dollars in a single atomic
  transaction. `Clockwork Finance` models composed contracts as an adversarial
  state transition system and proves **$\alpha$-Extractable Value ($\alpha$-EV)
  bounds**: no sequence of $k$ attacker actions can increase the attacker's net
  wealth across token vector $\vec{p}$ by more than $\alpha$.

#### 3.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool | Target Artifact | Re-Entrancy & External Call Model | Nonlinear Math & Loops | TCB & Soundness Boundaries |
| :--- | :--- | :--- | :--- | :--- |
| `Certora Prover` (`CVL`) | EVM / Solana / Soroban / Move bytecode | Configurable `HAVOC_ALL`, `HAVOC_ECF`, `DISPATCHER`, or `AUTO` summaries | Bounded loop unrolling (`--loop_iter`); LIA/BV/NIA solver portfolio | Proprietary Kotlin decompiler (`Tac`), loop unrolling bound, and `HAVOC_ECF` non-reentrant defaults. |
| `Halmos` / `Hevm` | EVM bytecode (Foundry tests) | Concrete or symbolic storage havoc on unknown `CALL` targets | Bounded symbolic execution (`--loop`); bit-precise `BV256` SMT | Bounded loop depth, 64-byte symbolic memory array assumptions, and external `Z3`/`Bitwuzla` solvers. |
| `KEVM` / `Kontrol` | EVM bytecode via K Framework | Full EVM call-stack semantics; coinductive Reachability Logic | Symbolic loop invariants (`kevm.infiniteGas` or explicit gas bounds) | K Framework Kore engine and `Z3` SMT backend (unless Matching Logic proof objects are checked). |
| `Move Prover` | Move bytecode + `spec` blocks | Dynamic dispatch & re-entrancy banned statically by Move VM | Reference elimination $\to$ `Boogie` $\to$ `Z3` with `global invariant`s | Move-to-Boogie translator, Boogie VC generator, and `Z3` solver. |
| `ConCert` / `Mi-Cho-Coq` | Coq AST / Michelson / Rust (via `MetaCoq`) | Explicit multi-contract `ChainBuilder` trace induction (DFS vs. BFS) | Unbounded Coq mathematical induction over arbitrary `Z` / `N` | Small Coq/Rocq kernel (plus `MetaCoq` erasure/printing when extracting to Rust/LIGO). |
| `Aeneas` | Safe Rust (`Charon` LLBC) $\to$ Lean 4 / Coq | Closed-world safe Rust borrow graph (no `unsafe` raw pointers or re-entrant FFI) | Pure functional backward functions + extrinsic termination proofs | `Charon` MIR extractor and `Aeneas` OCaml translator (trust boundary audited in sibling corpus reports). |
| `Clockwork Finance` | Composed K-Framework DeFi models | Symbolic multi-actor transaction blocks with flash-loan actions | Symbolic polynomial inequality solving (`Z3` / `Mathematica`) | Manual abstraction from Solidity to K-CF models and bounded block length $k$. |
| `Slither` / `Echidna` / `Medusa` | Solidity AST (`SlithIR`) / EVM runtime | Concrete multi-contract fuzzing with synthesized attacker contracts | Empirical falsification only (no soundness proof) | Unbounded false negatives (fuzzing cannot prove absence of exploits). |

#### 3.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial`:**
   - `Prog`: High-level AMM/lending mathematical specification, Rust/Solana or
     Move contract MIR, or EVM/SBPF bytecode.
   - `Query`: Initial ledger state (pool reserves $(x, y)$, share supply $S$,
     tick bitmaps, user balances) paired with an adversarial transaction or
     sequence of calls.
   - `Out`: Post-transaction ledger state, emitted event logs, or explicit
     transaction revert (`Out.reverted`).
   - `SemObs`: Net external balance deltas `(Address → Token → Int)`, pool
     reserve solvency flag, and emitted logs.
   - `Partial.ub` (`defined := False`): Represents **Conservation-of-Value
     violations**, **AMM / Vault solvency breaches** ($x' \cdot y' < x \cdot y$
     or ERC-4626 share-inflation rounding extraction where
     $\Delta \text{AttackerWealth} > 0$, matching `Clockwork Finance`'s $0$-EV
     bound), or **arithmetic panic on a valid withdrawal**. Crucially, an
     explicit `require(...)` revert on invalid user input is a **defined**
     outcome (`Out.reverted`), whereas an invariant breach or unexpected
     bricking on a valid withdrawal is `Partial.ub`.
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
   - `Compiles RealAmmSpecLang FixedPointContractLang codec rationalCurve q64_96Contract`:
     Proves that a 256-bit fixed-point implementation (using Q64.96 sqrt-price
     math and `mulDivDown`/`mulDivUp`) refines the ideal real/rational AMM curve
     with **pool-favored rounding** (`t ≤ codec.toMorphism s`).
   - `Abstracts ClockworkEvLang ContractLang codec zeroEvEnvelope defiProtocol`:
     Proves that a `Clockwork Finance` economic non-arbitrage envelope (`v`)
     soundly abstracts the concrete smart contract (`s`).
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`StepResult.externalCall` (Exact Solution to Classic & Read-Only DeFi
     Re-Entrancy):** In
     `anneal-structural-external-calls-and-tcb-mutation-testing-2026`, Anneal's
     `StepResult.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)`
     directly resolves the soundness gap between `Certora`'s `HAVOC_ECF` and
     `ConCert`'s multi-contract trace induction. When a DeFi pool invokes an
     untrusted external token or flash-loan callback (`IERC20.transfer`,
     `onFlashLoan`), `boundaryInv` checks the **Pool Solvency & Accounting
     Coherency Invariant** *at the call site* (either a re-entrancy mutex is
     held *and* read-only price-oracle getters enforce that mutex, or physical
     token balances already satisfy $x \cdot y \ge k$ before the external call).
     If `boundaryInv = false` (e.g., Curve-style read-only re-entrancy where LP
     supply was updated before token balances without locking the price getter),
     `StepResult.externalCall` steps immediately to `.failed` (`Partial.ub`).
     When `boundaryInv = true`, demonic choice quantifies over all arbitrary
     attacker callback transitions while preserving the caller's isolated frame,
     verified by straight-line fuel induction
     (`open_world_callback_composition_sound`).
   - **`ProductiveOn` & `InhabitedPre` (Anti-Freeze / Anti-Brick Liveness):** A
     contract that unconditionally reverts (`revert()` on every call) trivially
     satisfies every `Certora` or `Move Prover` partial-correctness invariant
     while permanently freezing user funds! Requiring
     `ProductiveOnNonRevert ValidWithdrawalRequest withdrawFn` and
     `ProductiveOnNonRevert UnderwaterPosition liquidateFn` proves that
     legitimate user withdrawals and solvency-restoring liquidations **can
     always succeed without reverting**.
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`:**
   - Models **trusted external token and oracle assumptions** positively
     (`.erc20StandardCompliant "USDC" ∈ waived ∨ ob.prop` under
     `DeFiAuditTrustPolicy`), ensuring that an assumption about a specific
     whitelisted token never introduces an antecedent contradiction that could
     mask an arithmetic bug in the core pool math.

---

### Finding 4: Financial Clearinghouses, Limit-Order-Book Matching Engines, and Double-Entry Ledgers

`Basis: normative + documentation + source + derived`

#### 4.1 Domain Goals, Target Users, and Concrete Tool Inventory

Traditional financial market infrastructure—equity and derivatives **Limit Order
Book (LOB) matching engines** (IEX, Goldman Sachs SIGMA X2, Six Swiss Exchange,
CME Globex), central-bank **Real-Time Gross Settlement (RTGS)** systems,
high-throughput **double-entry accounting databases**, ultra-low-latency **wire
protocol codecs**, and **Basel III/IV capital-adequacy risk engines**—must
process hundreds of thousands to millions of messages per second while obeying
strict market-structure regulations (SEC Reg NMS Rule 611 Order Protection,
MiFID II RTS 6) and Abelian group conservation laws. Six primary tool families
govern this domain:

- **`Imandra` (`imandra-ai/imandra-docs`, Aesthetic Integration):** An
  industrial automated reasoning and theorem-proving platform over a pure
  mechanized subset of OCaml, created by Grant Passmore and Denis Ignatovich.
  Target users are securities exchanges (IEX, SIX, Goldman Sachs), investment
  banks, and financial regulators (SEC, FCA) verifying Limit Order Book matching
  engines, dark-pool midpoint pegs, closing auctions, and FIX protocol
  Connectivity specs (`Imandra Markets` / `IPL`).
- **`TigerBeetle` (`tigerbeetle/tigerbeetle`):** A high-assurance distributed
  financial accounting database written in Zig by Joran Dirk Greef and the
  TigerBeetle team, targeting payment processors, central banks, and fintech
  ledgers. It processes millions of two-phase double-entry `Account` and
  `Transfer` mutations per second using static memory allocation (`TigerStyle`),
  Viewstamped Replication consensus, and deterministic fault-injection
  simulation (`VOPR`).
- **`Beancount` (`beancount/beancount`) & `Ledger` (`ledger/ledger`) / `hledger`
  (`simonmichael/hledger`):** Plain-Text Accounting (PTA) double-entry
  bookkeeping compilers created respectively by Martin Blais (Python/Rust
  `beancount`), John Wiegley (C++ `ledger`), and Simon Michael (Haskell
  `hledger`). They compile human-readable journal directives into strictly
  balanced multi-commodity ledger states with lot-level cost-basis tracking.
- **`TARGET2` / `CLS` RTGS Liquidity & Gridlock Verifiers:** Formal verification
  models (in `Spin` Promela, `UPPAAL`, `CPN Tools` Colored Petri Nets, and
  `Alloy`/`TLA+`) used by central-bank payment economists (ECB TARGET2/T2, Bank
  of England CHAPS, CLS FX settlement) to verify bilateral/multilateral
  **Liquidity-Saving Mechanisms (LSMs)** and cycle-offsetting algorithms against
  settlement gridlock.
- **`Simple Binary Encoding (SBE)` (`real-logic/simple-binary-encoding`) &
  `QuickFIX` (`quickfix/quickfix`):** The FIX Trading Community's standard
  wire-protocol engines: `SBE` (created by Martin Thompson and Real Logic, used
  by CME MDP 3.0, NASDAQ, Euronext) generates zero-copy, flyweight C++/Java/Rust
  codecs over fixed-offset byte buffers, while `QuickFIX` implements the
  stateful FIX session and application layer.
- **`Open-Source Risk Engine (ORE)` (`OpenSourceRisk/Engine`) & `QuantLib`
  (`lballabio/QuantLib`):** The standard open-source C++ quantitative finance
  libraries (sponsored by Acadia/LSEG and led by Luigi Ballabio and Roland
  Lichters) used by banks and clearinghouses to compute XVA (CVA/DVA/FVA/MVA),
  SIMM initial margin, and Basel III/IV FRTB Expected Shortfall stress
  envelopes.

#### 4.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Financial infrastructure tools balance nanosecond hardware sympathy against
mathematical auditability:

1. **ACL2-Inspired Recursive First-Order Proof Automation (`Imandra`):**
  Following the Boyer-Moore (`Nqthm` / `ACL2`) tradition, `Imandra` embeds both
  the executable matching engine and its regulatory theorems in pure OCaml. It
  combines **waterfall inductive theorem proving**, **non-linear real/integer
  SMT**, and **Region Decomposition** (partitioning a matching engine's infinite
  input space into finite symbolic state-transition equivalence regions). This
  discovered real price-time priority and Reg NMS order-protection bugs in Wall
  Street dark pools (Passmore et al., *Formal Verification of Financial
  Algorithms*, CADE-26, 2017), though the OCaml-to-production-C++/FPGA lowering
  typically relies on differential conformance testing rather than a
  kernel-checked machine-code compiler.
2. **Fixed-Schema Zero-Allocation State Machines (`TigerBeetle` & `SBE`):**
  Unlike general-purpose SQL databases where double-entry accounting is
  re-implemented ad-hoc in application transactions, `TigerBeetle` restricts its
  entire domain model to two fixed-size 128-byte structures (`Account` and
  `Transfer`) with built-in `debits_pending`, `debits_posted`,
  `credits_pending`, and `credits_posted` u128 counters, linked transfer chains,
  and `flags.debits_must_not_exceed_credits`. Similarly, `SBE` sacrifices
  arbitrary recursive nesting for deterministic $O(1)$ pointer-offset decoding.
  Both systems follow NASA's Power-of-Ten / `TigerStyle` discipline (zero
  dynamic heap allocation after startup, explicit loop bounds, paired caller/
  callee assertions), trading specification generality for deterministic latency
  and exhaustive simulation (`VOPR`).
3. **Abelian Multi-Commodity Conservation (`Beancount` / `Ledger`):** Martin
  Blais formalized double-entry bookkeeping as a **multi-commodity conservation
  law** where every transaction is a zero-sum vector in a free Abelian group
  over `(Commodity × CostBasisLot × AcquisitionDate)`, paired with explicit
  `balance` assertion directives at chronological checkpoints.

#### 4.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool | Core Invariant Enforced | Execution / Verification Method | Arithmetic Representation | Primary TCB & Soundness Gaps |
| :--- | :--- | :--- | :--- | :--- |
| `Imandra` | Price-time priority, no crossed book ($\text{bestBid} < \text{bestAsk}$), Reg NMS Rule 611 | Inductive waterfall proofs + SMT + symbolic Region Decomposition | Exact arbitrary-precision `Z` / `Q` rationals | `Imandra` proof kernel + unverified extraction/conformance bridge to C++/FPGA production engines. |
| `TigerBeetle` | Conservation of money ($\Delta\text{debits} = \Delta\text{credits}$), two-phase pending/post atomicity, balance bounds | Deterministic simulation (`VOPR`) + runtime paired assertions | `u128` fixed-point integer units | Zig compiler, Linux `io_uring` kernel interface, and absence of mechanized deductive proofs over `VOPR` state space. |
| `Beancount` / `Ledger` | Zero-sum transaction balance ($\sum w_i \cdot c_i = 0$) and non-negative lot inventory | Static batch parsing + chronological balance/pad solver | Decimal fixed-point (`Decimal` / MPFR rationals) | Python/C++/Haskell parser and floating-tolerance interpolation rules (`inferred_tolerance_default`). |
| `TARGET2` / `CLS` RTGS Checkers | Absence of partial deadlock in multilateral cycle-offsetting LSMs | Finite-state model checking (`Spin` / `UPPAAL`) + Tarski fixed-point lattice | Integer currency units | State-space explosion requiring small bank/payment-queue abstractions ($N \le 10$ banks). |
| `SBE` / `QuickFIX` | Wire-format framing, schema version backward compatibility, field bounds | Code generation from XML schema (`sbe-tool`) | Little/big-endian fixed-width binary primitives + mantissa/exponent decimals | Unverified Java `sbe-tool` generator; variable-length group pointer arithmetic in C++/Rust targets. |
| `ORE` / `QuantLib` | Arbitrage-free yield-curve interpolation, Basel FRTB Expected Shortfall bounds | Monte Carlo simulation + finite-difference PDE solvers + unit suites | IEEE-754 `double` (with optional AAD adjoint differentiation) | IEEE-754 floating-point catastrophic cancellation and discretization errors. |

#### 4.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial`:**
   - `Prog`: A low-latency Rust/C++ arena Limit Order Book, a `TigerBeetle`
     transfer-batch state machine, or a `Beancount` ledger compiler.
   - `Query`: A stream of `SBE`/`FIX` order messages (`NewOrder`, `Cancel`,
     `Modify`, `ClosingCross`) or `TigerBeetle` `CreateTransfers` batches.
   - `Out`: Execution reports (`Fill`, `Reject`), updated order book state, and
     posted ledger journal entries.
   - `SemObs`: The external matched-trade tape `(Price, Qty, MakerId, TakerId)`
     and net `Account` trial balances.
   - `Partial.ub` (`defined := False`): Represents **Price-Time Priority
     violations**, **crossed books** ($\text{bestBid} \ge \text{bestAsk}$ after
     continuous matching), **Reg NMS trade-throughs**, or **double-entry
     conservation breaches** ($\sum \text{Debits} \neq \sum \text{Credits}$ or
     violating `debits_must_not_exceed_credits`).
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
   - `Compiles ImandraLobSpecLang ArenaLobRustLang codec functionalBook arenaBook`:
     Proves that a zero-allocation, cache-aligned Rust intrusive arena order
     book (`t`) refines the pure functional `Imandra`-style list specification
     (`s`).
   - `Abstracts BaselFrtbEnvelopeLang OrePortfolioLang codec esBound oreEngine`:
     Proves upward abstraction (`Abstracts`) from a detailed `ORE`/`QuantLib`
     portfolio simulation (`s`) to a regulatory Basel III/IV Expected Shortfall
     capital envelope (`v`).
   - `PartialBehaviorCodec` (Direct Formalization of `SBE` Wire Codecs):
     `encodeQuery` and `decodeOut` model `SBE` zero-copy binary serialization
     and deserialization; `decodeOut = none` rejects truncated buffers, invalid
     `actingBlockLength`/`schemaId` headers, or out-of-range enum tags, while
     `decode_encode_out` and `encode_of_decode_some` eliminate parser-serializer
     roundtrip bugs.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`EventualBehaviorOf` (Variable $1 \to k$ Sweep Matching Loops):** In an
     exchange specification (`Imandra`), an incoming aggressive `IOC` or
     `Market` order that sweeps $k$ resting price levels and $m$ resting orders
     is a **single logical event** ($1$ step in `L_src`), whereas the concrete
     Rust/x86-64 engine (`L_tgt`) executes $k + m$ loop iterations. As proved in
     `anneal-behavior-codec-and-progress-refinement-2026`, `EventualBehaviorOf`
     validates this variable $1 \to (k+m)$ step refinement constructively while
     proving that the matching loop never diverges!
   - **`ProductiveOn` (RTGS Gridlock Freedom & Closing-Auction Clearing):** In
     `TARGET2`/`CLS` Liquidity-Saving Mechanisms and exchange closing auctions,
     `ProductiveOn ValidQueueState lsmOffsetProg` proves that the multilateral
     cycle-offsetting algorithm always terminates with a maximal valid
     settlement subset (Knuth-Tarski fixed point) without freezing the payment
     queue.
   - **`StepResult.externalCall`:** Models **Reg NMS Intermarket Sweep Order
     (ISO) external venue routing** and **two-phase `TigerBeetle`
     pending-transfer timeouts**, where `boundaryInv` verifies that sufficient
     pending balance is reserved (`debits_pending`) *before* external settlement
     dispatch.
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`:**
   - Models **Limit-Up/Limit-Down (LULD) volatility halt overrides**,
     **Self-Trade Prevention (STP) wash-trade exemptions**, and **supervisory
     Basel internal-model waivers** positively (`ob.id ∈ waived ∨ ob.prop`).

---

### Finding 5: Economic Mechanism Design, Combinatorial Auctions, and Two-Sided Matching Markets

`Basis: normative + documentation + source + derived`

#### 5.1 Domain Goals, Target Users, and Concrete Tool Inventory

Mechanism design constructs allocation and pricing algorithms over private agent
reports (valuations, rank-order preference lists, donor-recipient compatibility
matrices) that satisfy axiomatic economic hyperproperties: **Dominant-Strategy
Incentive Compatibility (DSIC / Strategy-Proofness)**, **Individual Rationality
(IR)**, **Stability (no blocking pairs)**, and **Pareto Efficiency**. Six
landmark systems represent this domain:

- **`SATFC` — FCC Broadcast Incentive Auction Feasibility Checker
  (`ubc-tea/SATFC`):** Developed by Kevin Leyton-Brown, Neil Newman, Chris
  Cameron, and collaborators at UBC and Auctionomics for the US Federal
  Communications Commission's \ 19.8B Broadcast Incentive Auction (PNAS 2017,
  DOI `10.1073/pnas.1616385114`). During each descending clock round, `SATFC`
  solved NP-complete TV station spectrum-repacking graph-coloring instances
  under sub-second timeouts using portfolio SAT/UNSAT solvers (`clasp`,
  `Glucose`, `Gurobi`).
- **`ForMaRE` Isabelle/HOL & Coq VCG Combinatorial Auction Checkers (`VCG` in
  Isabelle AFP):** Developed by Marco B. Caminati, Manfred Kerber, Christoph
  Lange, and Colin Rowat (*ForMaRE* project, University of Birmingham; AFP
  `VCG`), with parallel Coq formalizations of Vickrey and VCG mechanisms by
  Pierre Jouvelot, Mittelmann, et al. Target users are market designers
  requiring machine-checked proofs that extracted Scala/OCaml auction code
  computes exact Clarke pivot payments and preserves DSIC, non-negative prices,
  and pairwise-disjoint allocations.
- **`KidneySolver` (`JohnDickerson/KidneySolver`):** A branch-and-price integer
  linear programming (ILP) engine (using `Gurobi`/`CPLEX`) developed by John P.
  Dickerson, Tuomas Sandholm, David Manlove, and collaborators for the UNOS
  (US), NHSBT (UK), and National Kidney Registry (NKR) kidney paired-donation
  exchanges, finding maximum-weight disjoint cycles (length $\le K$, typically
  $K=3$) and non-directed donor (NDD) chains.
- **Isabelle/HOL `Stable_Matching` (`Peter Gammie` & `Tobias Nipkow`, Isabelle
  AFP):** Mechanized formalizations of the Gale-Shapley Deferred Acceptance
  algorithm, Many-to-One hospital-resident matching with quotas and
  **contracts** (Hatfield & Milgrom 2005; Roth 1984), Knuth-Tarski lattice
  fixed-point existence under substitutability and the **Law of Aggregate Demand
  (LAD)**, and strategy-proofness for proposing agents.
- **`Roth-Peranson` NRMP & School-Choice Matchers (`NRMP`, `matchingMarkets`,
  `PyMatching`):** The production residency-matching algorithm designed by Alvin
  E. Roth and Elliott Peranson (AER 1999) for the National Resident Matching
  Program (NRMP) and public-school choice systems (NYC, Boston), extending
  hospital-proposing Deferred Acceptance with heuristic conflict resolution for
  **married couples** submitting joint preference lists.
- **`MATPOWER` (`MATPOWER/matpower`) & `PowerModels.jl`
  (`lanl-ansi/PowerModels.jl`):** The standard open-source electric power grid
  optimization frameworks (created respectively by Ray Zimmerman at Cornell and
  Carleton Coffrin at Los Alamos National Laboratory) used by Independent System
  Operators (PJM, ERCOT, NYISO, CAISO) to solve Day-Ahead Unit Commitment and
  DC/AC Optimal Power Flow (OPF) for Locational Marginal Pricing (LMP).

#### 5.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Computational mechanism design bridges non-constructive mathematical economics
(Arrow-Debreu, Myerson, Vickrey-Clarke-Groves, Gale-Shapley) and NP-hard
combinatorial optimization:

1. **The Approximation- destroys-Truthfulness Barrier (`ForMaRE VCG` vs.
  `SATFC`):** A celebrated theorem by Nisan and Ronen (STOC 1999) proves that in
  combinatorial auctions (`VCG`), replacing an exact NP-hard winner
  determination solver with an sub-optimal approximation heuristic **destroys
  Vickrey-Clarke-Groves strategy-proofness (DSIC)**, because an agent can
  profitably misreport to nudge the heuristic into a different local optimum!
  `ForMaRE` resolves this for moderate auctions by verifying exact VCG winner
  determination and Clarke pivot pricing in Isabelle/HOL (`VCG` AFP) and
  extracting verified Scala code. For the massive FCC spectrum repacking problem
  where exact VCG was intractable and non-monotone, Milgrom and Segal (2014)
  designed a **Deferred-Acceptance Clock Auction** that is **obviously
  strategy-proof (OSP)** for **any** deterministic greedy feasibility
  oracle—allowing `SATFC` to use a time-bounded portfolio SAT solver with a
  cached feasibility database while preserving truthful bidding!
2. **Constructive Lattice Fixed Points vs. Couple Non-Existence
  (`Stable_Matching` vs. `Roth-Peranson`):** When matching single residents to
  hospitals, Gammie's Isabelle/HOL `Stable_Matching` formalization proves that
  under bilateral substitutability and the Law of Aggregate Demand, the set of
  stable many-to-one matchings forms a **non-empty complete lattice** (via
  Tarski's fixed-point theorem) and Deferred Acceptance finds the
  resident-optimal extreme point. However, when **married couples** submit joint
  preferences (`Roth-Peranson`), the substitutability condition fails: a stable
  matching may **not exist**, and deciding existence is NP-complete (Ronayne
  1990). Production `Roth-Peranson` engines therefore run sequential heuristics
  that can either cycle or return an unstable/unmatched outcome unless coupled
  with an explicit stability certificate checker.
3. **Primal-Dual Certificate Checking over Untrusted Solvers (`KidneySolver` &
  `PowerModels.jl`):** Both `KidneySolver` (branch-and-price over exponentially
  many cycles) and `PowerModels.jl` (MILP Unit Commitment + non-convex AC-OPF
  SDP/SOCP relaxations in `JuMP`/`Ipopt`/`Gurobi`) rely on millions of lines of
  unverified C/C++ commercial solver code. Rather than verifying `Gurobi`, a
  high-assurance architecture checks the solver's returned primal allocation
  (cycle length caps, HLA crossmatch safety, kirchhoff flow balance) and dual
  optimality/LMP shadow prices inside a small verified checker.

#### 5.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool / Framework | Economic / Physical Mechanism | Core Verified / Target Property | Solver / Proof Engine | TCB & Soundness Boundaries |
| :--- | :--- | :--- | :--- | :--- |
| `SATFC` (FCC Auction) | Milgrom-Segal Deferred-Acceptance Descending Clock Auction | Interference-free TV channel assignment within <1s clock step | Portfolio SAT/MIP (`clasp`, `Glucose`, `Gurobi`) + containment cache | Unverified C++/Java portfolio wrapper; relies on Milgrom-Segal theorem that timeout (`UNKNOWN`) preserves OSP if handled deterministically. |
| `ForMaRE` (`VCG` AFP) | Combinatorial Vickrey-Clarke-Groves (VCG) auction | Pairwise-disjoint allocation, non-negative Clarke payments, DSIC | Isabelle/HOL (`VCG` AFP) $\to$ extracted Scala | Isabelle kernel + Scala code generator (`Code_Target_Nat`); exponential $O(2^{|G|})$ brute-force winner search. |
| `Stable_Matching` (AFP) | Gale-Shapley Deferred Acceptance with contracts (Hatfield-Milgrom) | Stability (no blocking coalition), lattice structure, proposer strategy-proofness | Isabelle/HOL (`Stable_Matching` AFP) | Isabelle kernel; requires external proof that concrete hospital contracts satisfy `irc` (irrelevance of rejected contracts) and `lad`. |
| `Roth-Peranson` (NRMP) | Hospital-resident DA + iterative couple adjustment | Absence of blocking pairs and couple instability | Imperative heuristic loop | Can fail to converge or terminate without a stable matching on pathological couple instances. |
| `KidneySolver` | Cycle-and-chain branch-and-price ILP (`PICEF` / `HPIEF`) | ABO/HLA crossmatch compatibility, cycle cap $\le K$, max transplants | Java + `CPLEX` / `Gurobi` branch-and-price | Commercial MIP solver floating-point tolerances (`EpInt = 1e-5`) and unverified pricing subproblem. |
| `MATPOWER` / `PowerModels.jl` | DC-OPF, AC-OPF, SOCP/SDP relaxations, LMP pricing | Kirchhoff's laws, thermal line limits, generator ramp bounds | MATLAB / Julia `JuMP` + `Ipopt`, `Mosek`, `Gurobi` | Non-convexity of AC power flow (local optima) and floating-point solver tolerances. |

#### 5.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial`:**
   - `Prog`: A VCG auction solver, a Gale-Shapley / `Roth-Peranson` matcher, a
     `KidneySolver` cycle allocator, or a DC-OPF grid-clearing engine.
   - `Query`: A preference profile $v = (v_1, \dots, v_n)$ (or a **unilateral
     deviation pair** $((v_i, v_{-i}), (v'_i, v_{-i}))$ for relational DSIC
     verification!) plus physical constraints (interference graph, hospital
     quotas, HLA compatibility matrix, transmission susceptances).
   - `Out`: Allocation matrix $x$ and payment/LMP vector $p$.
   - `SemObs`: The externally observable `(Allocation × Payments)` (or in the
     relational 2-run product `Language`, the utility pair
     `(u_i(truthful), u_i(misreport))`).
   - `Partial.ub` (`defined := False`): Represents **infeasible allocations**
     (double-allocated spectrum channel in `SATFC`, ABO/HLA-incompatible kidney
     transplant in `KidneySolver`, thermal line overload in `PowerModels.jl`),
     **blocking pairs/coalitions** in `Stable_Matching`/`Roth-Peranson`,
     **Individual Rationality breaches** ($p_i > v_i(x)$), or **profitable
     strategic misreports** ($u_i(v'_i, v_{-i}) > u_i(v_i, v_{-i})$, violating
     DSIC).
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
   - `Compiles ForMareVcgLang FastBranchAndBoundLang codec textbookVcg rustVcgSolver`:
     Proves that a fast branch-and-bound or LP-duality Rust auction solver (`t`)
     refines the textbook `ForMaRE` Isabelle/HOL VCG specification
     (`s`)—guaranteeing exact winner determination so Nisan-Ronen DSIC failure
     cannot occur!
   - `Abstracts SocpRelaxationLang AcOpfLang codec convexEnvelope acGridModel`:
     Proves that `PowerModels.jl`'s Second-Order Cone Programming (SOCP) or SDP
     convex relaxation (`v`) soundly bounds the non-convex AC Optimal Power Flow
     feasible set (`s`).
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`ProductiveOn` (Constructive Existence of Stable Matchings & Market
     Clearing):** In `Roth-Peranson` matching with couples, a solver that
     returns `NoSolution` (empty outcome set) when couples create a cycle
     trivially satisfies partial stability (`∀ out ∈ ∅, IsStable out`)!
     Requiring `ProductiveOn AdmittedPreferenceProfile matchingProg` forces a
     constructive existence proof (paralleling Gammie's Knuth-Tarski theorem in
     `Stable_Matching`) or requires the runtime to produce a certified outcome
     on every admitted profile.
   - **`StepResult.externalCall` (Certifying Untrusted `Gurobi`/`SATFC`
     Solvers):** Models the exact callout from a verified Rust mechanism host to
     an untrusted external MILP/SAT solver (`Gurobi`, `CPLEX`, `clasp` in
     `SATFC`, `KidneySolver`, or `PowerModels.jl`), where the post-call
     transition checks a primal-dual optimality or stability certificate before
     accepting the external solver's witness.
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`:**
   - Models **NP-hard solver timeout waivers vs. non-waivable
     biological/physical safety**. In `SATFC` or `KidneySolver`, if the MILP/SAT
     solver hits its clock-round timeout,
     `.globalCardinalityOptimality ∈ waived` can be permitted by
     `MechanismTrustPolicy` (falling back to a greedy feasible repacking or
     shorter valid transplant cycles), while `TrustPolicy.isAllowed` strictly
     forbids waiving `.hlaCrossmatchCompatible`, `.noSpectrumInterference`, or
     `.individualRationality`.

---

### Finding 6: Game Theory, Multi-Agent Equilibrium Verification, and Algorithmic Collusion Bounds

`Basis: normative + documentation + source + derived`

#### 6.1 Domain Goals, Target Users, and Concrete Tool Inventory

Game-theoretic analysis and multi-agent verification tools compute or verify
strategic equilibria (**Nash Equilibrium [NE]**, **Subgame-Perfect Equilibrium
[SPE]**, **Sequential Equilibrium**, **Correlated Equilibrium [CE]**) and audit
autonomous learning agents (pricing bots, auction bidders, security patrols) for
**tacit algorithmic collusion** or **strategic temporal-logic specifications**.
Five major tools and frameworks anchor this domain:

- **`Gambit` (`gambitproject/gambit`):** The foundational open-source C++/Python
  library for finite normal-form and extensive-form games, created by Richard D.
  McKelvey, Andrew McLennan, and Theodore Turocy (1994–present). It provides 10+
  equilibrium solvers (Lemke-Howson linear complementarity, simplicial
  subdivision, homotopy continuation, global Newton, logit Quantal Response
  Equilibrium [QRE], and extensive-form Sequence Form LP) for economists and AI
  researchers.
- **`OpenSpiel` (`google-deepmind/open_spiel`):** Google DeepMind's C++/Python
  framework for reinforcement learning and search in imperfect-information games
  (Marc Lanctot et al., 2019), implementing Counterfactual Regret Minimization
  (`CFR`, `CFR+`, `Deep CFR`), `Exploitability` / `NashConv` exact best-response
  distance calculators, and $\alpha$-Rank evolutionary evaluation across 70+
  games.
- **`PRISM-games` (`prismmodelchecker/prism-games`):** An extension of the
  `PRISM` probabilistic model checker developed by Marta Kwiatkowska, Gethin
  Norman, David Parker, and Gabriel Santos at Oxford (TACAS 2013 / TACAS 2020,
  DOI `10.1007/978-3-030-45237-7_21`), verifying Turn-Based and Concurrent
  Stochastic Multi-Player Games (`SMG` / `CSG`) against probabilistic
  Alternating-Time Temporal Logic with rewards (`rPATL`) and synthesizing
  social-welfare-maximizing Nash and subgame-perfect equilibria.
- **`MCMAS` (`lomuscio/mcmas`):** A BDD-based symbolic model checker for
  Multi-Agent Systems developed by Alessio Lomuscio, Hongyang Qu, and Franco
  Raimondi (Imperial College London / UCL, CAV 2009 / STTT 2017, DOI
  `10.1007/s10009-015-0378-x`). Users specify agents in the **Interpreted
  Systems Programming Language (`ISPL`)** and verify specifications combining
  epistemic knowledge (`K_i`, `E_G`, `C_G` common knowledge), deontic
  correctness (`O_i`), and strategic logic (`ATLK` / **Strategy Logic [`SL`]**).
- **`Calvano` Algorithmic Collusion Q-Learning Models (`Emilio Calvano`,
  `Calzolari`, `Denicolò`, `Pastorello`, AER 2020, DOI
  `10.1257/aer.20190623`):** The canonical econometric and multi-agent
  simulation framework used by antitrust authorities (DOJ, FTC, EU DG
  Competition, UK CMA) to study how independent tabular and deep Q-learning
  pricing bots in repeated Bertrand oligopolies autonomously learn
  supracompetitive pricing sustained by finite-phase retaliatory punishment
  strategies.

#### 6.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Multi-agent strategic verification evolved along three complementary axes:

1. **Exact Algebraic/LP Equilibrium Solvers (`Gambit`) vs. Regret-Minimizing
  Iterative Search (`OpenSpiel`):** Finding a Nash Equilibrium in a general-sum
  2-player game is **PPAD-complete** (Daskalakis, Goldberg, Papadimitriou 2006).
  `Gambit` targets small-to-medium games using exact pivoting (Lemke-Howson on
  bimatrix games, or Koller-Megiddo-von Stengel **Sequence Form** LP on
  extensive games without absent-mindedness) and homotopy path-following to
  enumerate *all* isolated equilibria. For huge imperfect-information games
  ($10^{14}+$ states), `OpenSpiel` uses iterative **Counterfactual Regret
  Minimization (`CFR+`)**, where the time-averaged strategy profile converges to
  an $\epsilon$-Nash Equilibrium in zero-sum games and an $\epsilon$-Coarse
  Correlated Equilibrium in general-sum games, audited by exact tree-walk
  `NashConv`
  ($\sum_i \max_{\sigma'_i} u_i(\sigma'_i, \sigma_{-i}) - u_i(\sigma)$).
2. **Temporal-Epistemic-Strategic Model Checking (`PRISM-games` & `MCMAS`):**
  Alur, Henzinger, and Kupferman (JACM 2002) introduced **Alternating-Time
  Temporal Logic (`ATL`)**, where the coalition modality
  $\langle\langle A \rangle\rangle \phi$ asserts that coalition $A$ has a
  strategy to enforce $\phi$ against *all* demonic counter-strategies of
  $Ag \setminus A$. `MCMAS` combines `ATL` with epistemic knowledge operators
  (`K_i`), immediately encountering the **imperfect-information uniform strategy
  problem**: an agent can only execute a strategy if it assigns identical
  actions to epistemically indistinguishable local states (which is undecidable
  for multiple agents with perfect recall). `PRISM-games` extends `ATL` to
  stochastic transitions and bimatrix subgame-perfect synthesis (`rPATL`) via
  backwards value iteration and SMT (`Z3`/`Yices`) at each state.
3. **Antitrust Auditing of Learned Punishment Automata (`Calvano`):** Calvano et
  al. (AER 2020) showed that even 1-step-memory Q-learning agents
  ($S_t = (p_{1,t-1}, p_{2,t-1})$) converge not merely to high prices, but to a
  **subgame-perfect grim-trigger / finite-punishment automaton**: if rival $j$
  undercuts the collusive price $p^C$, bot $i$ slashes its price to
  $p^{\text{punish}}$ for $k$ periods before gradually returning to $p^C$,
  making unilateral deviation unprofitable! Auditing a commercial pricing
  algorithm for antitrust compliance therefore requires proving a **strategic
  abstraction property**: that the algorithm's policy cannot implement a
  retaliatory punishment phase conditioned on rival price cuts.

#### 6.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool / Framework | Game Model | Equilibrium / Logic Checked | Computational Engine | TCB & Soundness Gaps |
| :--- | :--- | :--- | :--- | :--- |
| `Gambit` | Finite normal-form & extensive-form games (EFG) | Exact Nash, SPE, Sequential Equilibrium, QRE | Exact rational `lrsmp` / Lemke-Howson + floating-point homotopy | Floating-point precision loss in homotopy/Newton solvers; exponential blowup on large game trees. |
| `OpenSpiel` | Extensive-form games, FOSG (Factored-Observation Stochastic Games) | $\epsilon$-NE (`NashConv`), $\epsilon$-CCE, $\alpha$-Rank | C++ tree traversal, `CFR+`, Deep RL (`PyTorch`/`JAX`) | IEEE-754 `double` accumulation in `NashConv`; zero-probability off-path information sets require explicit belief handling. |
| `PRISM-games` | Turn-based (`SMG`) and Concurrent Stochastic Games (`CSG`) | `rPATL` coalition strategies, social-welfare SPE & NE | MTBDD/hybrid symbolic engines + `Z3`/`Yices` + `Gurobi` | IEEE-754 value-iteration stopping tolerance ($\epsilon = 10^{-6}$ can stop early on slow-mixing Markov chains) and external SMT/LP solvers. |
| `MCMAS` | Interpreted Systems (`ISPL`) with local epistemic accessibility | `CTLK`, `ATLK` (uniform strategies), Strategy Logic (`SL`), Deontic `O_i` | `CUDD` BDD symbolic fixpoint model checking | Incomplete approximate fixpoint for uniform strategies under imperfect information; unverified C++ BDD engine. |
| `Calvano` Q-Learning | Repeated Bertrand logit-demand oligopoly with 1-period price memory | Supracompetitive profit gain $\Delta \in [0, 1]$ and impulse-response punishment | Tabular Q-learning simulation + forced-deviation impulse response | Empirical simulation over fixed random seeds; no formal verification of continuous/neural pricing policies. |

#### 6.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial`:**
   - `Prog`: A candidate strategy profile $\sigma = (\sigma_1, \dots, \sigma_n)$
     computed by `Gambit`/`OpenSpiel`, a `PRISM-games` synthesized controller,
     or a production Rust dynamic-pricing bot.
   - `Query`: An information set $h \in \mathcal{H}_i$, market demand state, and
     a unilateral deviation strategy $\sigma'_i$.
   - `Out`: The induced distribution over terminal histories $z \in Z$, price
     trajectories, and expected payoff vector
     $u(\sigma \mid h) \in \mathbb{R}^n$.
   - `SemObs`: Expected agent utilities, `NashConv` regret
     $\max_{\sigma'_i} (u_i(\sigma'_i, \sigma_{-i}) - u_i(\sigma))$, and
     price-cost markup ratios.
   - `Partial.ub` (`defined := False`): Represents a **profitable unilateral
     deviation**
     ($u_i(\sigma'_i, \sigma_{-i} \mid h) > u_i(\sigma \mid h) + \epsilon$,
     refuting $\epsilon$-SPE/Nash), a **violation of epistemic uniformity**
     (`MCMAS` `ATLK`: assigning distinct actions to two histories $s, s' \in h$
     in the same information set), or **retaliatory anti-collusion breach**
     (`Calvano`).
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
   - `Compiles BlueprintStrategyLang ProductionBotLang codec openSpielCfr rustTradingBot`:
     Proves that a low-latency Rust trading or bidding bot (`t`) faithfully
     refines the certified `OpenSpiel`/`Gambit` blueprint equilibrium strategy
     (`s`).
   - `Abstracts CompetitivePricingLang DynamicPricingBotLang codec bertrandEnvelope qLearningBot`:
     Directly formalizes **algorithmic antitrust compliance**: proves that a
     commercial dynamic-pricing algorithm (`s`, tracking inventory and demand)
     is soundly abstracted (`Abstracts`) by a competitive Markovian pricing
     envelope (`v`) whose price transitions are conditionally independent of
     rival punishment triggers—ruling out `Calvano`-style tacit collusion!
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`InhabitedPre` & `ProductiveOn` (Eliminating Off-Equilibrium-Path
     Zero-Probability Vacuity):** In extensive-form games (`Gambit`,
     `OpenSpiel`), if an information set $h \in \mathcal{H}_i$ lies **off the
     equilibrium path** (reach probability $P^\sigma(h) = 0$), the naive Bayes
     conditional payoff formula
     $P^\sigma(h) \cdot u_i(\sigma'_i \mid h) \le P^\sigma(h) \cdot u_i(\sigma \mid h)$
     reduces to $0 \le 0$ and holds **vacuously** for arbitrary irrational
     threats at $h$! This is the exact game-theoretic analogue of Anneal's
     negative-polarity vacuity bug. Requiring
     `InhabitedPre (ConsistentBeliefAt h)` and `ProductiveOn` over Kreps-Wilson
     trembling-hand belief assessments $\mu(\cdot \mid h)$ forces a normalized,
     strictly inhabited probability distribution at *every* information set $h$
     before checking sequential rationality.
   - **`StepResult.externalCall`:** Directly models `PRISM-games` and `MCMAS`
     $\langle\langle A \rangle\rangle \phi$ **coalition-vs-adversary
     transitions**: at each step, `boundaryInv` verifies that coalition $A$'s
     chosen action satisfies its local safety/epistemic shield, and the demonic
     choice quantifies over all possible counter-moves of the opponent coalition
     $Ag \setminus A$ and stochastic nature transitions.
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`:**
   - Models **$\epsilon$-equilibrium bounded-rationality tolerances** and
     **opponent-model domain assumptions** positively
     (`ob.id ∈ waived ∨ ob.prop` gated by `EquilibriumTrustPolicy`).

---

### Finding 7: Cryptographic Voting Systems, Social Choice Theory, and Governance Protocols

`Basis: normative + documentation + source + derived`

#### 7.1 Domain Goals, Target Users, and Concrete Tool Inventory

Trustworthy collective decision-making requires three distinct layers of
assurance: (1) **End-to-End Cryptographic Verifiability (`E2E-V`)** (proving
that every cast ballot is recorded as intended and tallied as recorded without
revealing voter identity), (2) **Verified Tabulation & Social Choice Axioms**
(proving that complex multi-round preferential counting algorithms such as
Single Transferable Vote [STV] terminate and obey statutory transfer rules), and
(3) **Constitutional & On-Chain Governance Safety** (proving that self-amending
quorum and timelock protocols cannot be captured or permanently deadlocked). Six
tool families define this domain:

- **`Verificatum` (`verificatum/verificatum-vmn`, `verificatum-vcr`):** The
  universally verifiable cryptographic ElGamal mixnet suite created by Douglas
  Wikström (KTH Royal Institute of Technology), deployed in national and
  municipal binding elections (Norway parliamentary elections, Estonia `ivxv`,
  Swiss Post/Scytl assessments) to anonymize and decrypt encrypted preferential
  ballots with zero-knowledge Proofs of Shuffle (Terelius-Wikström 2010).
- **`ElectionGuard` (`microsoft/electionguard`, `electionguard-rust`):** An
  open-source E2E-V cryptographic SDK developed by Microsoft Research (Josh
  Benaloh) and Galois, using exponential ElGamal homomorphic tallying,
  Chaum-Pedersen disjunctive zero-knowledge proofs of ballot well-formedness
  ($0 \lor 1$ selection bounds), and guardian threshold key ceremonies for
  optical-scan voting machines (Hart InterCivic, VotingWorks).
- **`Belenios` (`belenios/belenios`) & `Helios` (`benadida/helios-server`):**
  Web-based verifiable electronic voting platforms created respectively by Ben
  Adida (`Helios`, Usenix Security 2008) and Véronique Cortier, Pierrick Gaudry,
  and Stéphane Glondu at Inria/CNRS (`Belenios`, adding MAC/signature credential
  protection against ballot-stuffing by a corrupt server; routinely used by ACM,
  IACR, CNRS, and universities).
- **Coq & Isabelle Verified `Single Transferable Vote (STV)` Tabulators
  (`Dirk Pattinson`, `Rajeev Goré`, `Jeremy Dawson`, `Milad Ghale`,
  `Thomas Meumann`, VoteID 2015 / ITP 2017–2021, DOI
  `10.1007/978-3-662-48899-7_12`):** Machine-checked Coq (`VeriVote`) and
  Isabelle/HOL formalizations and verified Haskell/OCaml code extractors for
  statutory STV election variants (Australian Senate, ACT Hare-Clark, Victoria,
  Meek's iterative quota fixed-point STV).
- **Isabelle/HOL `Social_Choice_Types` (`Manuel Eberl` & `Felix Brandt`,
  Isabelle AFP, paired with `Nipkow`'s Arrow/Gibbard-Satterthwaite AFP entries
  and `PrefLib`):** Mechanized social-choice theory libraries formalizing
  anonymous/neutral preference profiles, Condorcet efficiency, Pareto
  optimality, strategy-proofness, and randomized Social Decision Schemes (SDSs)
  via First-Order Stochastic Dominance (`SD`) and Bilinear Dominance (`BD`).
- **`OpenZeppelin Governor` & `Compound TimelockController`
  (`OpenZeppelin/openzeppelin-contracts`):** The industry-standard on-chain
  governance and constitutional execution frameworks for Ethereum DAOs (Uniswap,
  Compound, Arbitrum, Optimism, ENS), implementing checkpointed `ERC20Votes`
  quorum snapshots, proposal state machines (`Pending` $\to$ `Active` $\to$
  `Succeeded` $\to$ `Queued` $\to$ `Executed`), and delayed timelock execution
  queues.

#### 7.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Voting and governance tools confront a fundamental tension between **expressive
social choice** and **cryptographic/computational tractability**:

1. **Additive Homomorphic Tallying (`ElectionGuard`, `Belenios`) vs. Verifiable
  Mixnet Shuffles (`Verificatum`):** For plurality or approval voting,
  `ElectionGuard` and `Belenios` never decrypt individual ballots: they multiply
  exponential ElGamal ciphertexts
  $\prod_{i=1}^n (g^{r_i}, y^{r_i} g^{m_i}) = (g^{\sum r_i}, y^{\sum r_i} g^{\sum m_i})$
  so only the aggregate sum $\sum m_i$ is decrypted via threshold Lagrange
  interpolation. However, for **Ranked-Choice Voting (IRV / STV)** with $C = 20$
  candidates, there are $20! \approx 2.4 \times 10^{18}$ possible rankings,
  making homomorphic counter vectors impossible. `Verificatum` solves this by
  passing encrypted ballots through a cascade of mix-servers, each applying a
  secret permutation $\pi$ and re-encryption factor while emitting a
  non-interactive Terelius-Wikström zero-knowledge proof of shuffle, outputting
  plaintext anonymized rankings that are then fed into a verified STV tabulator!
2. **Proof-Carrying Tabulation Certificate Checking
  (`Pattinson et al. Coq STV`):** Statutory STV legislation (such as the
  Australian Commonwealth Electoral Act 1918 § 273 or Meek's STV) involves
  complex fractional transfer values
  $t_c = (\text{tally}_c - \text{quota}) / \text{tally}_c$, exact floor/ceiling
  rounding, exclusion orderings, and iterative quota recalculation when ballots
  become exhausted. Pattinson, Goré, and Ghale pioneered **hybrid tabulation
  verification**: both verifying the STV algorithm inductively in Coq and
  synthesizing a fast **certificate checker** that validates an external
  tabulator's step-by-step election transcript (`Elect`, `Transfer`,
  `Eliminate`, `Count`).
3. **Self-Amending Constitutional Deadlocks (`OpenZeppelin Governor` /
  *Nomic*):** As philosopher Peter Suber analyzed in *The Paradox of
  Self-Amendment* (1990), any governance system whose proposals can modify the
  governance parameters themselves (`updateQuorumNumerator`,
  `setProposalThreshold`, `grantRole`/`revokeRole` on `TimelockController`) is
  vulnerable to **constitutional suicide**: a valid proposal can raise the
  quorum numerator above total circulating supply or revoke `PROPOSER_ROLE` and
  `TIMELOCK_ADMIN_ROLE` simultaneously, permanently bricking future upgrades.

#### 7.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool / Framework | Voting / Governance Rule | Primary Assurance Property | Verification / Crypto Core | TCB & Soundness Boundaries |
| :--- | :--- | :--- | :--- | :--- |
| `Verificatum` | Universally verifiable ElGamal mixnet for arbitrary ballot encodings | Shuffle soundness (multiset of decrypted ballots equals encrypted inputs) + privacy | Terelius-Wikström ZK Proof of Shuffle + independent `verificatum-vcr` verifier | Fiat-Shamir random-oracle heuristic, DDH assumption, and Java/GMP implementation (mitigated by independent verifier implementations). |
| `ElectionGuard` | Plurality, $k$-of-$m$, and bounded write-in homomorphic tallying | Ballot selection bounds ($0 \le m_{i,j} \le 1$, $\sum_j m_{i,j} \le k$) + accurate decryption | Disjunctive Chaum-Pedersen ZKPs + `HACL*`/Rust/C# verifiers | Ballot-marking device (BMD) trusted display UI; threshold guardian collusion ($t$-of-$n$). |
| `Belenios` / `Helios` | Homomorphic online voting with credential authentication | Cast-as-intended, recorded-as-cast, tallied-as-recorded + ballot secrecy | `ProVerif` / `EasyCrypt` protocol proofs (Cortier et al.) + OCaml verifier | Voter client browser JavaScript environment and registrar/decryption trustee separation. |
| `Pattinson et al. Coq STV` | Hare-Clark, Australian Senate, and Meek STV | Termination of transfer loops, quota bounds ($\lvert Winners\rvert \le Seats$), certificate soundness | Coq/Rocq constructive inductive proofs + Haskell/OCaml extraction | Coq kernel + OCaml/Haskell extraction runtime; statutory tie-breaking requires external randomness seed. |
| `Social_Choice_Types` (AFP) | Deterministic and randomized Social Choice Functions / SDSs | Anonymity, neutrality, Pareto efficiency, SD-strategy-proofness, Arrow/Gibbard-Satterthwaite | Isabelle/HOL (`Social_Choice_Types` AFP) | Isabelle kernel; formalizes mathematical properties rather than executable binary I/O codecs. |
| `OpenZeppelin Governor` | Token-weighted checkpointed proposals + `TimelockController` | Flash-loan vote resistance (`getPastVotes`), timelock delay, role access control | `Certora Prover` CVL specs + Foundry test suites | Arbitrary target `calldata` payloads executed by `TimelockController.executeBatch` can mutate governance storage if not guarded. |

#### 7.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial`:**
   - `Prog`: A Rust/extracted STV election tabulator, an `ElectionGuard` /
     `Verificatum` cryptographic transcript verifier, or an
     `OpenZeppelin Governor` constitutional state machine.
   - `Query`: A ballot profile `List Ballot` (or encrypted election guardian
     transcript) or a governance proposal sequence.
   - `Out`: The elected winner set `Finset Candidate` + round-by-round tally
     transcript, or the post-execution constitutional state.
   - `SemObs`: Official elected winners / enacted constitutional parameters and
     public audit totals.
   - `Partial.ub` (`defined := False`): Represents **unauthorized proposal
     execution without past-block quorum + timelock delay**, **dropped or
     double-counted ballots**, **Meek STV quota invariant breaches**, or
     **acceptance of an invalid Chaum-Pedersen / mixnet shuffle proof**.
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
   - `Compiles StatutoryStvLang RustTabulatorLang codec electoralActSpec rustStvBinary`:
     Proves that a production Rust election-night tabulation binary (`t`)
     faithfully refines the Coq/Isabelle statutory STV specification (`s`),
     closing the unverified OCaml/Haskell extraction gap.
   - `PartialBehaviorCodec`: Models `ElectionGuard` / `Verificatum` ASN.1/JSON
     cryptographic transcript parsing; `decodeOut = none` rejects malformed
     group elements not in the prime-order subgroup $\mathbb{G}_q$.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`ProductiveOn` (Anti-Constitutional-Deadlock & Meek STV Termination):**
     In `OpenZeppelin Governor` / `TimelockController`, requiring
     `ProductiveOn ReachableGovernanceState emergencyRecoveryProposal` proves a
     machine-checked **No-Constitutional-Suicide Theorem**: from every reachable
     governance state, there exists at least one valid token-holder/role
     coalition and proposal sequence capable of enacting a recovery upgrade! In
     Meek STV (`Pattinson et al.`), where surplus transfer factors and quotas
     are updated in a mutually recursive fixed-point loop as candidates are
     eliminated, `ProductiveOn ValidBallotProfile meekStvProg` proves that the
     tabulation loop terminates and produces a valid winner set on *every*
     ballot profile.
   - **`StepResult.externalCall` (Guarding Governance Proposal Payloads):** When
     `TimelockController.execute` invokes an arbitrary external proposal payload
     (`target.call{value}(data)`), `StepResult.externalCall` enforces
     `boundaryInv`—verifying that the **Constitutional Meta-Invariant**
     (`quorumNumerator <= quorumDenominator`, `PROPOSER_ROLE` inhabited,
     timelock `minDelay >= MIN_CONSTITUTIONAL_DELAY`) still holds across the
     external payload execution!
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`:**
   - Models **statutory tie-breaking lotteries** (when two STV candidates are
     tied to the exact fractional vote and the Electoral Officer draws lots) and
     **emergency security-council pause overrides** (`ob.id ∈ waived ∨ ob.prop`
     gated by `ElectionAuditPolicy`).

---

### Finding 8: Clinical Pathways, Closed-Loop ICU Titration, and Medical Device Calculators

`Basis: normative + documentation + source + derived`

#### 8.1 Domain Goals, Target Users, and Concrete Tool Inventory

Clinical decision support (CDS), intensive-care unit (ICU) closed-loop
physiological titration, programmable infusion pumps, and adaptive oncology
clinical trials translate high-stakes medical protocols into executable software
where unit confusion, unhandled physiological lab combinations, or
dose-escalation boundary bugs cause patient injury or death. Five major tool
families govern this domain:

- **`HL7 CQL` (Clinical Quality Language) & `FHIR Clinical Reasoning`
  (`cqframework/clinical_quality_language`, HL7 Normative Standard):** The
  international healthcare DSL created by Bryn Rhodes and HL7 to express
  electronic Clinical Quality Measures (`eCQMs`, used by CMS/NCQA) and
  executable Clinical Decision Support (`CDS Hooks`, NCCN/CDC guidelines) over
  `HL7 FHIR` patient data models (`ELM` Expression Logical Model AST) in Epic,
  Oracle Health (Cerner), and HAPI FHIR.
- **`PROforma` (`Tallis` / `OpenClinical.net`), `Asbru`, & the `KIV` Interactive
  Verifier:** Formal clinical guideline modeling languages (`PROforma` created
  by John Fox at Cancer Research UK based on the $R^2 L$ logic of argument and
  `Enquiry`/`Decision`/`Plan`/`Action` tasks; `Asbru` created by Yuval Shahar,
  Silvia Miksch, and Peter Johnson at Stanford/TU Wien for time-oriented
  skeletal plans with `filter`, `setup`, `suspend`, `reactivate`, and `abort`
  conditions). Annette ten Teije, Frank van Harmelen, Wolfgang Reif, and Marcos
  translated `Asbru` protocols into the **Karlsruhe Interactive Verifier
  (`KIV`)** to verify neonatal jaundice and mechanical ventilation guidelines.
- **`FDA Generic Patient-Controlled Analgesia (GPCA)` Infusion Pump Verifiers
  (`Kind2` [`kind2-mc/kind2`], `PVS` [`masci/pvsio-web`], `NuSMV`):** A
  multi-institution open verification benchmark initiated by the US Food and
  Drug Administration (FDA CDRH — Insup Lee, Rahul Mangharam, Mats Heimdahl,
  John Hatcliff, Cesare Tinelli, Paolo Masci) modeling a PCA opioid infusion
  pump in Simulink/Stateflow, Lustre (`Kind2` SMT $k$-induction), and `PVS` to
  eliminate lethal over-infusion bugs across basal rates, patient boluses, and
  clinician-bolus interlocks.
- **`SPRINT` (Specialized Relative Insulin and Nutrition Tables) & `STAR`
  (Stochastic Targeted) ICU Glycemic Control (`J. Geoffrey Chase`,
  `Christopher Pretty`, `Shaw` et al., Christchurch ICU / University of
  Canterbury):** Bedside nurse-driven (`SPRINT` lookup wheels) and
  tablet-computed (`STAR` 3D stochastic physiological insulin-sensitivity
  compartment models) closed-loop titration protocols that modulate intravenous
  insulin ($0\text{–}6\text{ U/h}$) and enteral nutrition to maintain ICU blood
  glucose in $4.0\text{–}8.0\text{ mmol/L}$ while bounding severe hypoglycemia
  risk ($< 2.2\text{ mmol/L}$) below $5\%$.
- **`BOIN` (Bayesian Optimal Interval) & `CRM` (Continual Reassessment Method)
  Phase I Oncology Dose-Finding Engines (`boin` R package, MD Anderson
  `trialdesign.org`, `dfcrm`):** Statistical clinical-trial engines created
  respectively by Ying Yuan and Suyu Liu (MD Anderson, *JRSS-B* 2015, DOI
  `10.1111/rssb.12089`) and John O'Quigley, Margaret Pepe, and Lloyd Fisher
  (*Biometrics* 1990) to govern cytotoxic dose escalation, de-escalation, and
  isotonic-regression/Bayesian toxicity stopping boundaries in Phase I cancer
  trials.

#### 8.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Medical software verification evolved in direct response to clinical adverse
events and FDA recalls (over 56,000 infusion-pump adverse event reports and 710
deaths recorded by the FDA between 2005 and 2009):

1. **Three-Valued Temporal Query Logic (`HL7 CQL`) vs. Skeletal Intention State
  Machines (`Asbru`/`PROforma` + `KIV`):** `HL7 CQL` unifies clinical cohort
  queries and bedside decision support into a functional expression language
  with built-in **UCUM (Unified Code for Units of Measure) quantities**, Allen's
  13 temporal interval operators (`overlaps`, `starts`, `within 24 hours of`),
  and **three-valued logic (`true`, `false`, `null`)** for missing EHR lab
  values. However, `CQL`'s `null` propagation creates a subtle hazard: if an
  alert condition `Patient.SerumPotassium > 5.5 'meq/L'` evaluates to `null`
  because the lab result is pending, `if Cond then HoldACEInhibitor` takes the
  `else` branch unless explicitly guarded! By contrast, `Asbru` and `KIV` model
  guidelines as hierarchical temporal state machines with explicit `filter`
  (mandatory preconditions) and `abort` transitions verified via Symbolic
  Execution in Dynamic Logic (`KIV`).
2. **Model-Based Reference Architecture (`FDA GPCA` + `Kind2` / `PVS`):** The
  FDA's GPCA project demonstrated that commercial infusion pump firmware fails
  not in isolated PID control loops, but at **mode-switch boundaries**: e.g.,
  when an alarm silences during a priming bolus or when a clinician edits the
  Drug Library `VTBI` (Volume To Be Infused) limit while a basal infusion is
  active. Expressing the GPCA architecture in `Lustre` and verifying it with
  `Kind2`'s multi-engine IC3/PDR + $k$-induction solver proved 50+ safety
  properties (`Rate_Out <= Max_Safe_Dose_Rate`, `Air_In_Line => Flow_Rate = 0`).
3. **Closed-Loop PK/PD Stochastic Envelopes (`SPRINT`/`STAR`) & Transparent
  Interval Boundaries (`BOIN` vs. `CRM`):** While `CRM` requires re-fitting a
  Bayesian parametric dose-toxicity curve after every patient cohort (acting as
  an opaque black box to bedside oncologists and occasionally escalating across
  skipped doses if unguarded), `BOIN` proves that optimal Bayes decision
  boundaries reduce to **two closed-form constant thresholds**
  $(\lambda_e, \lambda_d)$ on the observed Dose-Limiting Toxicity (DLT) rate
  $\hat{p}_j = y_j / n_j$, plus an explicit **overdose elimination rule**
  $\Pr(p_j > \phi \mid y_j, n_j) > 0.95$—allowing clinicians and IRBs to audit
  the entire dose-escalation table by inspection before the first patient is
  enrolled!

#### 8.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool / Protocol | Clinical Domain | Core Safety Property | Verification / Execution Stack | TCB & Soundness Boundaries |
| :--- | :--- | :--- | :--- | :--- |
| `HL7 CQL` / `ELM` | EHR clinical decision support & eCQMs | Cohort accuracy, temporal medication windowing, UCUM unit consistency | Java/TypeScript/`cql-engine` over `FHIR` resources | No static exhaustiveness or `null`-safety verifier; silent `null` fall-through on missing EHR labs. |
| `PROforma` / `Asbru` + `KIV` | Oncology, neonatal ICU, & ventilation pathways | Absence of conflicting drug orders, termination, intention reachability | `KIV` interactive theorem prover (Interval Temporal Logic / Dynamic Logic) | Manual translation from clinical prose to `Asbru`; `KIV` models abstract continuous physiology into discrete events. |
| `FDA GPCA` (`Kind2` / `PVS`) | PCA opioid infusion pump controller & alarms | Zero over-infusion (`Flow <= DrugLib_HardMax`), alarm halt within 1 tick | `Kind2` Lustre SMT ($k$-induction + IC3) & `PVS` interactive theorem prover | Code generation gap from Lustre/Simulink to target embedded C unless paired with verified C compilation. |
| `SPRINT` / `STAR` | ICU tight glycemic control (insulin + nutrition) | 5th-percentile predicted blood glucose $\ge 4.0\text{ mmol/L}$ (hypoglycemia shield) | Stochastic physiological compartment ODE integration + tabular lookup | Patient physiological model mismatch (extreme septic shock / steroid resistance outside stochastic atlas). |
| `BOIN` / `CRM` | Phase I oncology dose-escalation trials | Never escalate when $\hat{p}_j \ge \lambda_d$; permanently eliminate toxic doses ($\Pr(p_j > \phi) > 0.95$) | Exact Beta-Binomial posterior + Pool-Adjacent-Violators (`PAVA`) isotonic regression | R/C++ floating-point implementations; off-by-one cohort size rounding or unguarded dose-skipping in custom trial scripts. |

#### 8.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial`:**
   - `Prog`: An `HL7 CQL` / `ELM` clinical pathway, an `Asbru` skeletal plan, a
     Rust `FDA GPCA` infusion-pump controller, or a `BOIN`/`SPRINT` dosing
     engine.
   - `Query`: Longitudinal `PatientState` (weight, BSA, eGFR, ANC, platelets,
     blood glucose trajectory, active medications, cohort DLT counts
     $(y_j, n_j)$).
   - `Out`: A `ClinicalOrder` (drug dose in $\text{mg/m}^2$ or $\text{U/h}$,
     infusion rate command, `HoldAndPageMD` alert, or next cohort dose level).
   - `SemObs`: The active therapeutic intervention
     `(Drug × DoseRate × Route × HoldStatus × AlarmState)`.
   - `Partial.ub` (`defined := False`): Represents **lethal over-infusion**
     (exceeding `FDA GPCA` Drug Library hard limits or lifetime anthracycline
     cardiotoxicity caps), **administering a contraindicated drug**, **silent
     `CQL` `null` fall-through on missing critical labs**, or **escalating a
     Phase I oncology trial into an eliminated toxic dose (`BOIN` boundary
     breach)**.
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
   - `Compiles NccnGuidelineLang EhrCqlRustLang codec clinicalSpec hospitalOrderSet`:
     Proves that a hospital's concrete EHR order-set engine (`t`) is a sound
     clinical refinement of the specialty society's guideline (`s`, resolving
     permitted clinical ranges such as "reduce dose by 20–25%" to a concrete 25%
     reduction).
   - `Abstracts StarPkPdEnvelopeLang InfusionPumpLang codec stochasticGlucoseBound pumpController`:
     Proves that the `STAR`/`SPRINT` pharmacokinetic/pharmacodynamic safety
     envelope (`v`) soundly bounds the bedside infusion controller (`s`).
   - `PartialBehaviorCodec` (Dimensional & Unit Safety): Translates between SI
     molar units ($\text{mmol/L}$ glucose, $\text{kg}$ weight) and US clinical
     units ($\text{mg/dL}$ glucose, $\text{lb}$ weight); `decodeOut = none`
     rejects unachievable pump stepper-motor rates or unrounded syringe
     concentrations, preventing $18\times$
     ($\text{mg/dL} \leftrightarrow \text{mmol/L}$) or $2.2\times$
     ($\text{lb} \leftrightarrow \text{kg}$) unit-confusion overdoses!
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`ProductiveOn` (Zero Unhandled Patient States in ICU Triage):** Clinical
     flowcharts routinely contain non-exhaustive boundary guards (e.g., Branch A
     handles `ANC >= 1500 ∧ Platelets >= 100k`, Branch B handles `ANC < 1000`,
     leaving `1000 <= ANC < 1500` with zero enabled actions—or in `HL7 CQL`, a
     missing lab value evaluates every branch guard to `null`). In an ICU
     emergency, a controller that steps to `.stuck` is life-threatening.
     Requiring `ProductiveOn PhysiologicallyPossiblePatient protocol` proves
     **total clinical triage completeness**: every patient state (including
     `Option.none` pending labs) produces a defined, safe clinical action (such
     as `HoldInfusionAndPageAttendingMD`).
   - **`InhabitedPre` (Clinical Trial Cohort Satisfiability):** Complex
     biomarker-stratified oncology master protocols frequently specify 30+
     inclusion/exclusion criteria that accidentally contradict each other,
     yielding an empty eligible patient cohort. `InhabitedPre` per trial arm
     mechanically proves that every stratified cohort is inhabited!
   - **`StepResult.externalCall`:** Models laboratory assay turnaround or
     attending-physician override callbacks, where `boundaryInv` guarantees that
     the patient is placed in a safe holding state (`KeepVeinOpenRate` /
     `HoldBolus`) *before* waiting for the external clinical callback.
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`:**
   - Models **IRB Single-Patient Compassionate Use exemptions** and **documented
     attending-physician clinical overrides** positively
     (`ob.id ∈ waived ∨ ob.prop` gated by `ClinicalGovernancePolicy`), ensuring
     a documented override for one patient never disables hard Drug Library
     max-rate checks.

---

### Finding 9: Cyber-Physical Rules of the Road (Aviation/Maritime/Road) and Medical Assurance Cases

`Basis: normative + documentation + source + derived`

#### 9.1 Domain Goals, Target Users, and Concrete Tool Inventory

Safety-critical cyber-physical systems (airborne collision avoidance, autonomous
road vehicles, autonomous surface vessels, and implantable/radiotherapy medical
devices) operate under legally mandated **Rules of the Road** (FAA/ICAO right of
way, maritime COLREGs, autonomous-driving blame attribution) and regulatory
**Assurance Cases** (FAA DO-178C, ISO 26262, IEC 62304). Six landmark tools
define this domain:

- **`KeYmaera X` (`LS-Lab/KeYmaeraX-release`) — `VerifyACAS` / `TCAS II`:** An
  axiomatic tactical theorem prover for **Differential Dynamic Logic
  ($d\mathcal{L}$)** created by André Platzer, Jean-Baptiste Jeannin, Khalil
  Ghorbal, Yanni Kouskoulas, et al. at CMU (CADE-25 2015, DOI
  `10.1007/978-3-319-21401-6_36`; TACAS 2015 / *J. ACM* 2017 for `ACAS X`). It
  verifies hybrid systems combining discrete control advisories with continuous
  ordinary differential equations ($x' = f(x) \ \& \ Q$) using a microkernel of
  ~2,000 lines of Scala and real quantifier elimination (`Mathematica` / `Z3`).
- **`Reluplex` (`guykatzz/ReluplexCav2017`) & `Marabou`
  (`NeuralNetworkVerification/Marabou`) — `ACAS Xu`:** Complete SMT-based deep
  neural network (DNN) verifiers created by Guy Katz, Clark Barrett, David L.
  Dill, Kyle Julian, and Mykel Kochenderfer at Stanford/Hebrew University (CAV
  2017, DOI `10.1007/978-3-319-63387-9_5`; CAV 2019 for `Marabou`). They extend
  the Simplex linear-programming algorithm with piecewise-linear `ReLU`
  splitting and symbolic bound tightening to verify 10 safety and maneuver
  properties across the 45 6-layer neural networks compressing the 2-gigabyte
  `ACAS Xu` unmanned-aircraft collision-avoidance lookup table.
- **`Mobileye RSS` (Responsibility-Sensitive Safety) & `ad_rss_lib`
  (`intel/ad-rss-lib`):** A formal mathematical model and open-source
  C++14/Python library created by Shai Shalev-Shwartz, Shaked Shammah, and Amnon
  Shashua at Mobileye/Intel (arXiv `1708.06374`, IEEE 2846-2022 standard)
  defining minimum safe longitudinal and lateral distances ($d_{\min}$) and
  mandatory "proper response" braking/steering envelopes so an autonomous
  vehicle never causes a preventable collision.
- **`CommonOcean` (`CommonRoad/commonocean-io`, `commonocean-rules-m`) &
  `CommonRoad` (`CommonRoad/commonroad-stl-monitor`) — Maritime `COLREGs` & Road
  Traffic Rules:** Motion-planning verification and runtime-monitoring suites
  developed by Matthias Althoff's Cyber-Physical Systems group at Technical
  University of Munich (TUM). They formalize international maritime collision
  regulations (**IMO COLREGs Rules 13–17**: overtaking, head-on, crossing
  give-way vs. stand-on, and emergency action) and road traffic codes in
  **Metric Temporal Logic (`MTL`)** and **Signal Temporal Logic (`STL`)**.
- **`NASA AdvoCATE` (Assurance Case Automation Toolset):** Developed by Ewen
  Denney and Ganesh Pai at NASA Ames Research Center (SAFECOMP / CAV / FAA
  assurance research), automating the construction, pattern instantiation, risk
  aggregation, and formal verification linking of **Goal Structuring Notation
  (`GSN`)** safety cases for UAS and aviation systems.
- **`PVS` / `PVSio-web` Alaris GP Infusion Pump UI Verifier (`Paolo Masci`,
  `Paul Curzon`, `Harold Thimbleby`, `Michael Harrison`):** Formal human-machine
  interface (HMI) models in SRI's `PVS` theorem prover verifying commercial
  Becton Dickinson **Alaris GP** data-entry chevron keys (`up`/`down`
  fast-and-slow numeric entry) against mode-confusion and wrap-around
  number-entry hazards.

#### 9.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Cyber-physical and assurance-case verification tools resolve three classic gaps
between continuous physics, discrete lookup tables/neural networks, and legal
responsibility:

1. **Continuous Hybrid Envelopes (`KeYmaera X`) vs. Compressed Discrete Tables /
  DNNs (`ACAS X` & `Reluplex`/`Marabou`):** FAA/Lincoln Laboratory's NextGen
  `ACAS X` replaces TCAS II's heuristic rules with a dynamic-programming Markov
  Decision Process (MDP) lookup table (or 45 `ACAS Xu` neural networks).
  However, an MDP table only maximizes expected reward on discretized grid
  points and provides zero hard guarantee against Near Mid-Air Collisions
  (`NMAC`: $|r| < 500\text{ ft} \land |\Delta h| < 100\text{ ft}$) between grid
  points! Jeannin and Platzer (`KeYmaera X`) solved this by deriving a
  **symbolic differential-game safe-able region** in $d\mathcal{L}$ (bounding
  parabolic vertical trajectories $\ddot{h} \ge a_{\min}$ after pilot delay
  $d_{\text{pilot}}$) and checking all millions of `ACAS X` table cells against
  that continuous envelope—discovering real unsafe cells under advisory
  reversals (`Climb` $\to$ `Descend`). Conversely, `Reluplex`/`Marabou` verify
  directly on the piecewise-linear `ACAS Xu` neural networks that within input
  polytopes (e.g., distant intruder with high closing speed), an unsafe advisory
  (`Weak Left` when `Strong Right` is required) is unsatisfiable (`UNSAT`).
2. **Blame-Free Inductive Safety (`Mobileye RSS`) vs. Multi-Vessel Legal
  Deadlocks (`CommonOcean COLREGs`):** A notorious failure mode of rule-based
  autonomous planners is the **"frozen robot problem"**: when 3 ships meet at a
  crossing (`COLREGs` Rule 15) or an oncoming vessel violates its give-way duty,
  a naive conjunction of `MTL` rules evaluates every candidate trajectory to
  `false`. `Mobileye RSS` avoids this on highways by defining inductive safe
  distances $d_{\min}$ where maintaining $d > d_{\min}$ guarantees that a
  bounded brake (`properResponse`) prevents a collision even if the leading car
  slams its brakes at $a_{\max,\text{brake}}$. In maritime `COLREGs`, **Rule
  17(b)** explicitly mandates a **hierarchical deontic override**: the stand-on
  vessel *must* maintain course and speed (Rule 17(a)(i)), *until* collision
  cannot be avoided by the give-way vessel alone, at which point the stand-on
  vessel is *obligated* to maneuver (Rule 17(b))!
3. **Formalizing Goal Structuring Notation (`NASA AdvoCATE`):** Traditional
  medical and aviation safety cases (GSN diagrams in PDF/Word) suffer from
  **implicit environmental assumptions** and **disconnected formal proofs**: a
  theorem proved in `PVS` or `KeYmaera X` assumes a sensor noise bound
  $\delta \le 5\text{ ft}$, while the hardware hazard log records
  $\delta \le 15\text{ ft}$. `AdvoCATE` links GSN `Solution` nodes directly to
  formal verification obligations and propagates `Assumption` and `Context`
  nodes structurally.

#### 9.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool / System | Cyber-Physical Domain | Specification Formalism | Verification Engine | TCB & Soundness Boundaries |
| :--- | :--- | :--- | :--- | :--- |
| `KeYmaera X` (`VerifyACAS`) | Airborne collision avoidance (`ACAS X` / `TCAS II`) | Differential Dynamic Logic ($d\mathcal{L}$) | ~2,000-LoC Scala axiom kernel + real QE (`Mathematica` / `Z3`) | External real quantifier-elimination oracle (`Mathematica` CAD) and simplified point-mass vertical kinematics. |
| `Reluplex` / `Marabou` (`ACAS Xu`) | Unmanned aircraft neural-network advisories | Quantifier-free linear arithmetic + `ReLU(x) = max(0, x)` | Simplex LP + ReLU case splitting + symbolic bound tightening | IEEE-754 floating-point LP simplex tolerances (mitigated by proof-producing Marabou certificates). |
| `Mobileye RSS` (`ad_rss_lib`) | Autonomous road vehicle longitudinal/lateral safety | Inductive worst-case braking kinematics ($d_{\min}$) | C++14 runtime safety shield + analytic kinematic proofs | Assumes piecewise-constant worst-case accelerations ($a_{\max,\text{accel}}, a_{\max,\text{brake}}$) and accurate ego/object state estimation. |
| `CommonOcean` / `CommonRoad` | Maritime `COLREGs` (Rules 13–17) & road traffic law | Metric / Signal Temporal Logic (`MTL` / `STL`) robustness degree | Quantitative trace monitoring + reachability shields | Discretized time steps $\Delta t$; multi-vessel conflicts require prioritized rule relaxation to avoid planner freezing. |
| `NASA AdvoCATE` | Aviation / UAS / medical GSN assurance cases | Goal Structuring Notation (`GSN`) + formal logic contracts | Pattern instantiation + external prover integration (`PVS`, `Frama-C`) | Unverified Eclipse/Java graphical workbench unless exported to a machine-checked proof kernel. |
| `PVS` Alaris UI Verifier | Infusion pump human-machine keypad entry | Higher-order logic transition systems (`PVS` / `PVSio-web`) | `PVS` interactive theorem prover + `Yices` | Gap between `PVS` HMI model and commercial embedded microcontroller C firmware. |

#### 9.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial`:**
   - `Prog`: An airborne `ACAS X` table-interpolation / neural flight controller
     in Rust, a `Mobileye RSS` (`ad_rss_lib`) trajectory shield, a `CommonOcean`
     `COLREGs` maneuver selector, or an Alaris infusion-pump keypad state
     machine.
   - `Query`: Relative multi-vehicle kinematics
     $(r, \dot{r}, \Delta h, v_0, v_i, \theta)$ or clinician keystroke sequences
     (`chevron_up`, `chevron_down`, `ok`).
   - `Out`: Selected maneuver advisory (`Climb`, `Descend`,
     `ProperResponseBrake`, `StarboardAlteration`) and resulting kinematic
     trajectory / displayed pump dose.
   - `SemObs`: Minimum separation distance (`HMD`, `VMD`), legal `COLREGs` /
     `RSS` maneuver compliance, or committed infusion rate.
   - `Partial.ub` (`defined := False`): Represents a **Near Mid-Air Collision
     (`NMAC`)**, an **unprovoked `COLREGs` Rule 14/15 right-of-way violation**,
     a **`Mobileye RSS` blameworthy collision**, or a **`PVS` Alaris keypad
     integer wrap-around** (where pressing `up` near the maximum dose wraps to a
     small value or vice versa without clinician confirmation).
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
   - `Abstracts KeymaeraSafeRegionLang AcasTableLang codec dlEnvelope acasLookupTable`:
     Directly formalizes Jeannin & Platzer's `VerifyACAS` architecture! The
     continuous $d\mathcal{L}$ safe-able region (`v`, proved safe in `theory/`
     via barrier/kinematic lemmas) is proved to soundly abstract (`Abstracts`)
     the discrete `ACAS X` lookup table or `Marabou`-verified neural network
     (`s`).
   - `Compiles AcasTableLang AirborneRustLang codec tableSpec flightRustCode`:
     Then proves that the embedded DO-178C Rust flight controller (`t`) refines
     the lookup table (`s`), composing with `Abstracts` by plain
     `Preorder.le_trans`!
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`ProductiveOn` (Eliminating the Autonomous "Frozen Robot Problem" in
     `COLREGs` and `RSS`):** In `CommonOcean` `COLREGs` and `Mobileye RSS`, a
     trajectory filter that rejects *all* candidate actions in a dense 3-vessel
     encounter steps to `.stuck` (or returns an empty safe-action set), causing
     the vessel to lose steerage. Requiring
     `ProductiveOn ValidKinematicEncounter colregsPlanner` proves that the
     prioritized rulebook (where `COLREGs` Rule 17(b) emergency collision
     avoidance overrides Rule 17(a)(i) stand-on course keeping) **always yields
     at least one defined, safe maneuver in every kinematic encounter**!
   - **`StepResult.externalCall`:** Models pilot response delay and demonic
     intruder/other-vessel maneuvers bounded by physical $g$-limits
     (`branches`), enforcing `boundaryInv` (the ego vehicle's current state
     remains inside the `KeYmaera X` / `RSS` invariant envelope before the
     environment steps).
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`
  (Machine-Checked `AdvoCATE` GSN Assurance Cases):**
   - Anneal's `ScopedVerificationResult` and `VerificationResultOn` provide a
     **kernel-checked formalization of a `NASA AdvoCATE` / FDA / FAA Goal
     Structuring Notation (GSN) Assurance Case**: top-level GSN `Goal` claims
     map to `obligations`, `Solution` evidence nodes map to Lean 4 kernel proofs
     of `ob.prop`, and GSN `Assumption` / hardware-context nodes (such as
     `.radarAltimeterNoiseBounded` or `.brakeActuatorLatencyUnder100ms`) map to
     positively scoped `waived` IDs checked by
     `TrustPolicy.isAllowed`—guaranteeing that two slightly mismatched hardware
     sensor assumptions can never contradict each other on the left of `→` and
     silently discharge the flight software safety proof!

---

### Finding 10: Customs Tariffs, Sanctions Screening, and Policy-as-Code / Privacy Compliance

`Basis: normative + documentation + source + derived`

#### 10.1 Domain Goals, Target Users, and Concrete Tool Inventory

Global trade compliance (Harmonized System tariff classification, Free Trade
Agreement Rules of Origin, OFAC 50%-rule beneficial-ownership sanctions) and
enterprise data-privacy / authorization enforcement (GDPR, HIPAA, cloud IAM)
require evaluating complex declarative policies over recursive trees, cyclic
corporate ownership graphs, and time-stamped audit streams. Five major tool
families anchor this domain:

- **`AWS Cedar` (`cedar-policy/cedar`, `cedar-policy/cedar-spec`) &
  `Open Policy Agent (OPA)` / `Rego` (`open-policy-agent/opa`):** Modern
  Policy-as-Code authorization engines. `OPA`/`Rego` (created by Styra and
  graduated by the CNCF) is a Datalog-derived declarative query language for
  Kubernetes admission control and microservices authorization. `Cedar`
  (developed by Michael Hicks, Emina Torlak, Kesha Hietala, et al. at AWS;
  OOPSLA 2024, DOI `10.1145/3649835`) is an expressive, fast, and analyzable
  ABAC/RBAC policy language built using **Verification-Guided Development**: its
  semantics, type-checker/validator, and symbolic compiler are formalized and
  proved sound in **Lean 4** (`cedar-spec`) and differentially tested against
  the production **Rust** implementation (`cedar`).
- **`Jeeves` (`jeanqasaur/jeeves`), `Legalease` (`Microsoft Grok`), &
  `PrivGuard`:** Academic and industrial privacy-compliance languages. `Jeeves`
  (Jean Yang, Armando Solar-Lezama, et al., POPL 2012, DOI
  `10.1145/2103656.2103669`) pioneered **policy-agnostic programming**, where
  sensitive values carry declarative confidentiality labels
  (`level = high | low`) and the runtime uses an SMT solver (`Z3`) or facet
  trees to project the appropriate view (`high` vs. anonymized `low`)
  automatically at output sinks. `Legalease` (Shayak Sen, Saikat Guha, Anupam
  Datta, Sriram Rajamani, Janice Tsai, Jeannette Wing, IEEE S&P / Oakland 2014)
  pairs a lattice-structured `ALLOW`/`DENY` privacy policy language with static
  information-flow taint tracking (`Grok`) across MapReduce/Cosmos big-data
  pipelines at Microsoft Bing. `PrivGuard` enforces GDPR/HIPAA
  purpose-limitation and differential-privacy budget (`epsilon`) accounting via
  static/runtime abstract interpretation.
- **`OpenSanctions` (`opensanctions/yente`, `opensanctions/followthemoney`) &
  Datalog / Graph `OFAC 50%-Rule` Beneficial-Ownership Engines:** Open-source
  entity-resolution and sanctions-screening infrastructure created by Friedrich
  Lindenberg using the **FollowTheMoney (`FtM`)** graph schema (`LegalEntity`,
  `Ownership`, `Directorship`), paired with recursive Datalog (`Soufflé` /
  `Ascent` in Rust) or matrix fixed-point solvers to enforce the US Treasury
  OFAC **50% Rule** (any entity owned $\ge 50\%$ in the aggregate, directly or
  indirectly, by one or more Specially Designated Nationals [SDNs] is itself
  blocked).
- **`HTSUS` (Harmonized Tariff Schedule of the United States) & `SAP GTS`
  (Global Trade Services) / `USMCA Rules-of-Origin` BOM Compilers:** Enterprise
  customs engines that classify physical goods into 10-digit HS/HTSUS codes
  under **General Rules of Interpretation (GRI 1–6)** and recursively evaluate
  multi-tier **Bills of Materials (BOMs)** against Free Trade Agreement (USMCA,
  EU-UK TCA) **Tariff-Shift** (change in chapter/heading/subheading) and
  **Regional Value Content (`RVC`)** Net-Cost / Transaction-Value formulas.
- **`MonPoly` (`eth-sri/monpoly`) & `MFOTL` (Metric First-Order Temporal
  Logic):** A runtime compliance monitoring and log-auditing engine developed by
  David Basin, Felix Klaedtke, Samuel Müller, and Eugen Zălinescu at ETH Zurich
  (CAV / JACM), checking infinite streams of time-stamped relational database
  and system events against GDPR, HIPAA, and financial separation-of-duty
  policies written in **Metric First-Order Temporal Logic (`MFOTL`)** with past
  and future bounded temporal operators
  ($\Diamond_{[0, 30\text{d}]}, \Box_{[0, 1\text{y}]}$) and aggregation (`SUM`,
  `CNT`).

#### 10.2 History, Intellectual Lineage, and Design Philosophy Tradeoffs

Compliance and policy-enforcement systems navigate three deep design tensions:

1. **`forbid`-Overrides-`permit` Decidability (`AWS Cedar`) vs. Datalog
  Recursion (`OPA` / `Rego`):** `OPA`/`Rego` provides full Datalog-style virtual
  documents and comprehension loops, which makes general policy equivalence or
  subsumption checking undecidable. By contrast, `AWS Cedar` intentionally
  bounds its language: every policy is a `permit` or `forbid` clause over
  `(principal, action, resource)` with hierarchy membership (`in` on a DAG) and
  `when`/`unless` predicates without unbounded recursion, and evaluation obeys
  **default-deny with `forbid`-overrides-`permit`**. Because `Cedar` has no
  unbounded loops, `cedar-spec` in **Lean 4** proves both that the `Cedar`
  validator is **type-sound** (a validated policy never raises a runtime type
  error) and that `Cedar`'s symbolic compiler to SMT (`Z3`/`cvc5`) is **sound
  and complete**, enabling push-button verification of policy equivalence and
  privilege-escalation bounds!
2. **Faceted Information Flow (`Jeeves`) vs. Compositional Lattice Clauses
  (`Legalease`) vs. Temporal Stream Monitoring (`MonPoly`):** `Jeeves` prevents
  developers from forgetting a privacy check at an output sink by attaching the
  policy directly to the data, though full SMT constraint solving at runtime
  incurs heavy overhead (later optimized via **faceted execution** by Austin and
  Flanagan, POPL 2012). `Legalease` avoids full logic syntax by restricting
  policies to nested `ALLOW`/`EXCEPT-DENY`/`EXCEPT-ALLOW` clauses over concept
  lattices (`DataType`, `Purpose`, `Role`), mirroring `Catala`'s legislative
  exceptions. However, many GDPR/HIPAA rules are **temporal** (e.g., HIPAA §
  164.506 or GDPR Art. 33: *"If a personal data breach occurs, the controller
  shall notify the supervisory authority within 72 hours"*). Static access
  control cannot check future obligations; `MonPoly` solves this by checking
  **safe-range `MFOTL`** formulas over relational event streams in $O(1)$
  amortized space per active time window.
3. **Cyclic Equity Ownership & Recursive BOM Rollups (`OpenSanctions` &
  `SAP GTS`):** Under the OFAC 50% Rule, shell companies often form
  **cross-holding cycles** ($A$ owns $40\%$ of $B$, $B$ owns $30\%$ of $A$, and
  an SDN owns $35\%$ of $A$ and $35\%$ of $B$). Computing whether an entity is
  blocked requires either a monotone Datalog fixed-point over direct control
  thresholds or solving the linear system $(I - W)^{-1} s$ of effective
  beneficial ownership. Similarly, in `SAP GTS` / `USMCA` Rules of Origin, the
  **Rollup / Absorption rule** dictates that once an intermediate sub-assembly
  qualifies as `Originating` (e.g., RVC $\ge 75\%$), $100\%$ of its value counts
  as originating when rolled up into the parent vehicle BOM—inducing a bottom-up
  catamorphism over the BOM tree.

#### 10.3 Ecosystem Comparison, Formal Theory, and TCB Analysis

| Tool / Engine | Compliance Domain | Policy / Rule Formalism | Verification / Analysis Engine | TCB & Soundness Boundaries |
| :--- | :--- | :--- | :--- | :--- |
| `AWS Cedar` | Cloud IAM & application authorization (ABAC/RBAC) | `permit`/`forbid` clauses over entity DAGs (`forbid` overrides `permit`) | **Lean 4** mechanized semantics, validator soundness, & symbolic SMT compiler (`cedar-spec`) + DRT | Lean 4 kernel (`cedar-spec`); translation from Lean 4 spec to production Rust (`cedar`) bridged by millions of Differential Random Tests (DRT). |
| `OPA` / `Rego` | Cloud-native / Kubernetes Policy-as-Code | Safe stratified Datalog with JSON comprehensions | Static type/safety checks + test runner (`opa test`) | Go/Wasm evaluator; no built-in SMT equivalence prover; partial evaluation can blow up on complex comprehensions. |
| `Jeeves` / `Legalease` / `PrivGuard` | GDPR/HIPAA data confidentiality & purpose limitation | Faceted values (`Jeeves`), concept-lattice exception trees (`Legalease`) | POPL mechanized non-interference proof (`Jeeves`); static dataflow (`Grok`) | Covert timing channels in `Jeeves`; completeness of manual data-store annotations in `Legalease`/`PrivGuard`. |
| `OpenSanctions` + Datalog 50%-Rule | OFAC / EU / UN sanctions & beneficial-ownership screening | `FollowTheMoney` entity graph + recursive Datalog ownership rules | Fuzzy name/entity matching (`yente`) + monotone graph fixed point | Entity-resolution false negatives (misspelled shell companies) and cyclic ownership truncation if recursion depth is bounded. |
| `HTSUS` / `SAP GTS` BOM Engine | Customs tariff classification (GRI 1–6) & FTA Rules of Origin | 10-digit HS tree + recursive BOM tariff-shift and `RVC` formulas | Enterprise ABAP/Rust rule evaluation | Unhandled GRI tie-breaking ambiguities and IEEE-754 float rounding near exact RVC thresholds (e.g., $74.999999\%$ vs. $75.0\%$). |
| `MonPoly` (`MFOTL`) | Runtime auditing of GDPR/HIPAA/financial logs | Metric First-Order Temporal Logic (`MFOTL`) with aggregation | Finite-table relational algebra monitor (`eth-sri/monpoly` in OCaml) | Requires formulas to be inside the syntactic **monitorable (`safe-range`) fragment**; out-of-order log timestamps require buffering watermarks. |

#### 10.4 Exact Mapping onto Anneal's Four `trusted/` Primitives

1. **`Language SemObs` & `Partial`:**
   - `Prog`: A `Cedar` / `OPA` policy set, a `Legalease` privacy rulebook, an
     `OpenSanctions` Datalog 50%-rule engine in Rust, a `USMCA` BOM origin
     calculator, or a `MonPoly` `MFOTL` runtime monitor.
   - `Query`: An authorization request
     `(principal, action, resource, context, entities)`, a recursive `BOMTree`,
     a corporate ownership graph, or a timestamped audit-log prefix.
   - `Out`: Authorization decision (`Allow` / `Deny` +diagnostics), faceted data
     projection, 10-digit `HtsCode` + `OriginStatus`, or `MFOTL` violation
     tuple.
   - `SemObs`: The externally visible enforcement decision (`Allow`/`Deny`,
     low-security projected view, duty payable, or emitted compliance alert).
   - `Partial.ub` (`defined := False`): Directly captures **`Cedar` evaluation
     type/entity errors** (which `Cedar`'s Lean 4 validator soundness theorem
     proves unreachable on well-typed policies:
     `L.sem policy ≤ L.WellFormedOn ValidRequest`!), **approving an export or
     payment to an OFAC-blocked entity ($\ge 50\%$ aggregate SDN ownership)**,
     **leaking high-confidentiality data to a low observer (`Jeeves`
     non-interference breach)**, or **missing a mandatory 72-hour GDPR breach
     notification deadline (`MonPoly` `MFOTL` violation)**.
2. **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
   - `Compiles CedarLeanSpecLang CedarRustEngineLang codec leanSpecModel rustCedarCrate`:
     Directly closes the last remaining gap in AWS `Cedar`'s Verification-Guided
     Development! While `cedar-spec` proves validator and symcc soundness in
     Lean 4 and relies on Differential Random Testing (DRT) to check the
     production Rust `cedar` crate, Anneal's `anneal-rustc-capture` + `Compiles`
     can verify in the **same Lean 4 kernel** that the production Rust `cedar`
     evaluator (`t`) refines the `cedar-spec` Lean model (`s`)!
   - `Abstracts FastSanctionsFilterLang ExactOfacGraphLang codec bloomGraphFilter exactOfac50Rule`:
     Proves that a high-throughput conservative pre-screening filter (`v`)
     soundly over-approximates the exact transitive corporate ownership fixed
     point (`s`), guaranteeing **zero false negatives** on sanctioned entities.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`:**
   - **`ProductiveOn` (Exhaustiveness of `HTSUS` GRI 1–6 & `Cedar` Total
     Evaluation):** Every physical good crossing a customs border *must* map to
     a valid 10-digit `HTSUS` code. Requiring
     `ProductiveOn ValidGoodsDescription htsClassifier` proves that chapter
     notes, exclusion notes, basket subheadings (`xxxx.xx.90`), and GRI 1–6
     tie-breakers form a **total, non-empty partition** over all goods.
   - **`InhabitedPre` (Treaty Origin Satisfiability & Non-Vacuous `Cedar`
     Policies):** Proves that complex multi-layered FTA origin rules (e.g.,
     `USMCA` automotive RVC + Labor Value Content + core parts + steel/aluminum
     thresholds) are simultaneously satisfiable by at least one supply-chain BOM
     configuration, and that every `Cedar` `permit` clause has at least one
     inhabited request not shadowed by a broader `forbid` clause!
   - **`StepResult.externalCall`:** Models external **Customs and Border
     Protection (CBP) Binding Ruling lookups** or **third-party supplier origin
     attestations**, enforcing `boundaryInv` (verified audit trail and signature
     validity) before granting preferential duty treatment.
4. **Positive Per-Obligation `VerificationResult` & `TrustPolicy`:**
   - Models **OFAC General Licenses (e.g., humanitarian/medical export
     exemptions)**, **Section 301 / 232 tariff exclusions**, and **HIPAA
     emergency "Break-the-Glass" access overrides** positively
     (`ob.id ∈ waived ∨ ob.prop` gated by `ComplianceTrustPolicy`).

---

### Finding 11: Cross-Domain Synthesis Matrix onto Anneal's Four Trusted Primitives

`Basis: source + derived`

Across all 10 domains and 65 surveyed tools, every domain-specific verification
obligation reduces without extra axioms to Anneal's four core `trusted/`
primitives in `Trusted/Refinement.lean` and `Trusted/StepResult.lean`:

| Domain & Representative Tools | Primitive 1: `Language SemObs` & `Partial.ub` (`defined := False`) | Primitive 2: `BehaviorCodec` / `PartialBehaviorCodec`, `Compiles` & `Abstracts` | Primitive 3: `ProductiveOn` & `InhabitedPre` + `EventualBehaviorOf` / `StepResult.externalCall` | Primitive 4: Positive Per-Obligation `VerificationResult` & `TrustPolicy` (`waived`) |
| :--- | :--- | :--- | :--- | :--- |
| **1. Statutory Law & Tax Compilers** (`Catala`, `OpenFisca`, `Blawx`, `L4`, `PolicyEngine`, `PSL Tax-Calculator`, `Oracle IA`, `DGFiP M`) | `Catala` `ConflictError` (incomparable exception priorities), deontic $\mathsf{O}(A) \land \mathsf{F}(A)$, or phase-out division-by-zero | Production Rust/C tax engine `Compiles` `Catala` statute (`obs_decodeOut` prevents `DGFiP M`/`OpenFisca` float drift); `PolicyEngine` METR bound `Abstracts` code | `InhabitedPre` prevents bureaucratic Catch-22s; `ProductiveOn` rules out `Catala` `EmptyError` (missing default); `EventualBehaviorOf` bridges $1 \to k$ worksheets | Statutory grandfather clauses, transitional safe harbors, and state Medicaid Section 1115 federalism waivers |
| **2. Commercial Contracts, Derivatives & Cap Tables** (`ISDA CDM`, `ACTUS`, `Marlowe`, `LexiFi MLFi`, `Daml`, `Ergo`, `OCF`, `Stipula`, `Symboleo`) | Conservation breach ($\sum \text{payout}_i \neq V$), negative payouts (`Marlowe`), missing `Daml` signatory, or `Stipula` linear-asset cloning | Closing disbursement script `Compiles` `OCF` corporate charter; Basel PFE / `ACTUS` envelope `Abstracts` `ISDA CDM` CSA | `ProductiveOn` proves algebraic fixed-point existence in circular SAFE/note waterfalls and `Marlowe`/`Stipula` escrow liquidity | Board waivers, Series Preferred anti-dilution consent overrides, and force-majeure carve-outs |
| **3. Smart Contracts, DeFi & AMM Solvency** (`Certora CVL`, `Halmos`, `KEVM`/`Kontrol`, `Move Prover`, `ConCert`, `Aeneas`, `Clockwork Finance`) | Value-conservation breach, $x' \cdot y' < x \cdot y$, or positive attacker Extractable Value (`Clockwork Finance` $>0$-EV rounding exploit) | Fixed-point `U256` Q64.96 contract `Compiles` rational AMM spec with pool-favored rounding; `Clockwork` $0$-EV bound `Abstracts` protocol | **`StepResult.externalCall`** enforces pre-call `boundaryInv` (catching classic & Curve read-only re-entrancy!); `ProductiveOn` proves withdrawals/liquidations never brick | Whitelisted ERC-20 token compliance and bounded-deviation Chainlink oracle assumptions |
| **4. Clearinghouses, LOB Matching & Ledgers** (`Imandra`, `TigerBeetle`, `Beancount`/`Ledger`, `TARGET2`/`CLS`, `SBE`/`QuickFIX`, `ORE`/`QuantLib`) | Price-Time Priority violation, crossed book, Reg NMS trade-through (`Imandra`), or unbalanced entry ($\Delta\text{Dr} \neq \Delta\text{Cr}$ in `TigerBeetle`) | Zero-alloc arena book `Compiles` `Imandra` list spec; `PartialBehaviorCodec` verifies zero-copy `SBE` wire framing; Basel VaR/ES `Abstracts` `ORE` | **`EventualBehaviorOf`** handles $1 \to (k+m)$ aggressive order sweep loops; `ProductiveOn` proves `TARGET2` LSM cycle-offsetting gridlock freedom | Limit-Up/Limit-Down (LULD) circuit-breaker halts, Self-Trade Prevention (STP) rules, and Basel internal-model waivers |
| **5. Mechanism Design, Auctions & Matching** (`SATFC`, `ForMaRE VCG`, `KidneySolver`, `Stable_Matching`, `Roth-Peranson`, `PowerModels.jl`) | Blocking pair (`Stable_Matching`), ABO/HLA-incompatible organ (`KidneySolver`), IR deficit, or profitable strategic misreport (DSIC breach) | Fast branch-and-bound solver `Compiles` `ForMaRE` VCG spec (preventing Nisan-Ronen DSIC loss); SOCP relaxation `Abstracts` AC-OPF grid | `ProductiveOn` proves stable matching existence (`Knuth-Tarski`); **`StepResult.externalCall`** wraps untrusted `Gurobi`/`SATFC` solvers with primal-dual certificate checks | `SATFC`/`KidneySolver` timeout optimality waivers (falling back to greedy feasible solutions while forbidding safety/IR waivers) |
| **6. Game Theory, Equilibria & Anti-Collusion** (`Gambit`, `OpenSpiel`, `PRISM-games`, `MCMAS`, `Calvano` Q-learning) | Profitable unilateral deviation (`OpenSpiel` `NashConv` $> \epsilon$), non-uniform epistemic strategy (`MCMAS`), or retaliatory punishment (`Calvano`) | Low-latency Rust bot `Compiles` `OpenSpiel`/`Gambit` blueprint; memoryless competitive Bertrand envelope `Abstracts` dynamic pricing bot | `InhabitedPre` + `ProductiveOn` enforce Kreps-Wilson belief consistency at off-path zero-probability info sets; `externalCall` models `rPATL`/`ATLK` opponent moves | $\epsilon$-Nash bounded-rationality tolerances and opponent-model domain restrictions |
| **7. Voting Systems, Social Choice & Governance** (`Verificatum`, `ElectionGuard`, `Belenios`, `Coq STV`, `Social_Choice_Types`, `OZ Governor`) | Quorum/timelock bypass (`OZ Governor`), invalid Chaum-Pedersen / shuffle ZKP (`ElectionGuard`/`Verificatum`), or STV quota breach | Production Rust tabulator `Compiles` `Pattinson et al.` Coq STV spec; `PartialBehaviorCodec` validates $\mathbb{G}_q$ subgroup transcripts | **`ProductiveOn`** proves **no reachable governance amendment can deadlock recovery** (*Nomic* immunity) and Meek STV fixed-point loops terminate | Statutory Electoral Officer tie-breaking lotteries and emergency guardian pause overrides |
| **8. Clinical Pathways, ICU Titration & Trials** (`HL7 CQL`/`FHIR`, `PROforma`/`Asbru`/`KIV`, `FDA GPCA` `Kind2`/`PVS`, `SPRINT`/`STAR`, `BOIN`/`CRM`) | Lethal over-infusion (`FDA GPCA`), silent `HL7 CQL` `null` lab fall-through, drug contraindication, or escalating past `BOIN` DLT boundary | Hospital EHR order set `Compiles` NCCN/`Asbru` guideline; **`PartialBehaviorCodec`** enforces UCUM unit conversions ($\text{mmol/L} \leftrightarrow \text{mg/dL}$); `STAR` PK/PD `Abstracts` pump | **`ProductiveOn`** guarantees **zero unhandled patient physiological states** in ICU triage; `InhabitedPre` proves clinical trial cohort inclusion criteria are satisfiable | IRB Single-Patient Compassionate Use exemptions and attending-physician documented clinical overrides |
| **9. Cyber-Physical Rules of Road & Assurance Cases** (`KeYmaera X` `ACAS X`, `Reluplex`/`Marabou`, `Mobileye RSS`, `CommonOcean` `COLREGs`, `AdvoCATE`, `Alaris PVS`) | Near Mid-Air Collision (`NMAC`), unprovoked `COLREGs` turn violation, `RSS` blameworthy crash, or `Alaris` UI chevron keypad wrap-around | Embedded DO-178C Rust flight code `Compiles` `ACAS X` table; `KeYmaera X` $d\mathcal{L}$ safe region `Abstracts` table / `Marabou` DNN | **`ProductiveOn`** eliminates the **"frozen robot problem"** in multi-vessel `COLREGs` Rule 17(b) & `RSS` encounters; `externalCall` bounds intruder $g$-limits | **Direct formalization of `NASA AdvoCATE` GSN Assurance Cases** (`waived` = positively scoped hardware/sensor context assumptions) |
| **10. Customs Tariffs, Sanctions & Privacy / IAM** (`AWS Cedar`, `OPA`/`Rego`, `Jeeves`, `Legalease`, `OpenSanctions`, `HTSUS`/`SAP GTS`, `MonPoly` `MFOTL`) | `Cedar` runtime type error, clearing an OFAC $\ge 50\%$ SDN-owned entity, `Jeeves` confidentiality leak, or `MonPoly` 72h GDPR breach violation | Production Rust `cedar` crate `Compiles` **Lean 4 `cedar-spec`** in the same kernel; fast sanctions filter `Abstracts` transitive ownership graph | `ProductiveOn` proves `HTSUS` GRI 1–6 forms a total partition of all goods; `InhabitedPre` proves `USMCA` BOM origin rules and `Cedar` `permit` clauses are non-vacuous | OFAC General Licenses (humanitarian exemptions), Section 301 tariff exclusions, and HIPAA "Break-the-Glass" emergency access |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **PROLEG, SPINdle, Flora-2 / ErgoAI, OASIS LegalRuleML, Docassemble, DataLex,
  `s(CASP)`, and Lawsky Tax Formalizations:** Defeasible deontic logic,
  Courteous Logic Programming overrides, and constructive default-negation
  solvers for statutory tax and administrative rules.
- **Certified Symbolic Management of Contracts in Coq (`patrickbahr/contracts`,
  ICFP 2015), BitML (CCS 2018), CLTool, and CLarva:** Coq-verified multi-party
  Peyton Jones-Eber derivatives and symbolic liquidity (`ProductiveOn`) model
  checking.
- **SolCMC (`solc` SMTChecker), VerX (ETH Zurich), SmartPulse (SmartLTL
  liveness), Scilla (Coq communicating automata), Quint/Apalache, Dafny-EVM, and
  Nethermind Clear (Lean 4 EVM/Cairo):** Automated CHC/temporal/liveness
  verifiers and Coq/Dafny/Lean 4 smart-contract verification frameworks.
- **Coq Formalization of Limit Order Books (Garg, Sarswat, Singh CPP 2021 / ITP
  2022), Formance `Numscript`, Arelle (`XBRL Formula 1.0`), and `EconCSLib`
  (Lean 4 Mechanism Design):** Machine-checked Coq continuous double auctions,
  atomic multi-leg double-entry DSLs, SEC/Basel XBRL validators, and Lean 4
  VCG/Myerson proofs.
- **Isabelle/Coq Extensive-Form Games (`Game_Theory` AFP), Libratus/DeepStack
  Safe Subgame Resolving, USC Teamcore Stackelberg Solvers, and `TuGames`:**
  Mechanized backward induction, safe subgame entry boundary invariants
  (`StepResult.externalCall`), and cooperative Core verifiers.
- **Swiss Post E-Voting, Civitas, sElect, `abcvoting` (Method of Equal Shares),
  CMS Bonnie/MADiE, MatchMiner, Systerel S3, and Isabelle `VeriMon`
  (`MFOTL_Monitor` AFP):** End-to-end verifiable voting, proportional approval
  budgeting, clinical eCQM/trial cohort matchers, and Isabelle-verified
  GDPR/HIPAA temporal monitors.

### Part II: Historical Verification, Compiler, and Operational Failure Postmortems

### Historical Failure Analysis 1. Real-World Exploits of Formally Verified and Audited Smart Contracts and DeFi Protocols

#### 1.1 Euler Finance (\$197M Exploit, March 13, 2023): Unverified EIP-14 Function-Boundary Omission of `checkLiquidity`

`Basis: documentation + source + derived`

On March 13, 2023 (Ethereum Mainnet block `16817996`), an attacker drained
approximately \$197 million in DAI, WBTC, stETH, and USDC from the Euler Finance
lending protocol across six transactions.

- **Technical mechanism:** In Euler's architecture, users deposit underlying
  ERC-20 assets to mint collateral shares (`EToken`, representing a claim on the
  pool's reserve) and can mint leveraged debt tokens (`DToken`) up to a
  collateral-adjusted health factor. Every balance-reducing or debt-increasing
  operation in `EToken.sol` (`withdraw`, `transfer`, `transferFrom`, `mint`)
  invoked `checkLiquidity(account)` before completion to verify that the
  account's risk-adjusted collateral value remained at least its liability
  value:
  $$\sum_{i} \text{collateral}_i \cdot c_i \ge \sum_{i} \frac{\text{debt}_i}{b_i}$$
  In July 2022, governance proposal **EIP-14** added a helper function
  `EToken.donateToReserves(uint subAccountId, uint amount)` intended to let
  users burn `eTokens` into protocol reserves to clear account dust. Although
  EIP-14 underwent standalone smart-contract audit review, `donateToReserves`
  decremented the caller's `eToken` collateral balance **without calling
  `checkLiquidity(msg.sender)`**.
- **Exploit execution:** Using a flash loan of 30M DAI from Aave, the attacker
  operated two contracts (`Violator` and `Liquidator`):
  1. `Violator` deposited 20M DAI, called `EToken.mint` at 10x leverage to
     create 195.6M `eDAI` and 200M `dDAI`, repaid 10M DAI of debt using the
     remaining flash-loaned funds, and minted another 195.6M `eDAI` and 200M
     `dDAI` (reaching 410M `eDAI` collateral against 390M `dDAI` debt).
  2. `Violator` called `donateToReserves(0, 100_000_000e18)`, burning 100M
     `eDAI` directly into reserves while leaving 390M `dDAI` debt intact.
     Because `checkLiquidity` was absent, the transaction succeeded, placing
     `Violator` at 310M `eDAI` vs. 390M `dDAI` (80M DAI of unbacked bad debt).
  3. In Euler's dynamic liquidation pricing formula, the liquidation discount
     scaled linearly with how far underwater the borrower was, without capping
     the discount at the point where collateral value fell below debt value.
     `Liquidator` called `liquidate` on `Violator`, absorbing the debt at a
     massive collateral bonus that transferred all 310M `eDAI` to `Liquidator`,
     which then withdrew the entire underlying reserve (38.9M DAI) after having
     only 30M DAI at risk.
- **Why per-function verification and differential audits missed it:** Prior
  formal and manual reviews verified existing functions (`withdraw`, `mint`,
  `liquidate`) under the implicit inductive invariant that **every reachable
  post-transaction state satisfies account solvency** (`HealthFactor(u) >= 1`
  unless underwater solely from external price movement). Differential review of
  EIP-14 checked local functional behavior of `donateToReserves` ("burns
  caller's own `eTokens`, cannot steal another user's balance") rather than
  re-verifying that *every* public entrypoint of the `Crate` preserved the
  global protocol representation invariant `AdtInv`.
- **Architectural lesson for Anneal:**
  1. **Mandatory whole-crate obligation completeness (`Trusted.CrateTheorem` and
     `EnsuresRetLibInv`):** In Anneal (`trusted/lean/Trusted/MirSemantics.lean`
     and
     `support/ProofGatedCompilationAndTrustPolicy.lean`),
     custom representation invariants (`AdtInv` / `LibInv`) are not optional
     per-function properties chosen ad hoc by a developer. Every `pubSafe`
     function in `Crate.fns` carries a mandatory `EnsuresRetLibInv` and
     `WellFormedOn` obligation in `CrateTheorem`. Adding a new public method
     like `donateToReserves` automatically adds its `EnsuresRetLibInv`
     preservation obligation to the crate's obligation inventory; if
     `donateToReserves` breaks the account solvency invariant, `CrateTheorem` is
     unprovable.
  2. **Positive per-obligation waiver tracking (`VerificationResult`):** If a
     new upgrade function is deployed without a proof of `EnsuresRetLibInv`,
     Anneal's `ScopedVerificationResult` forces the obligation ID
     `("donateToReserves", .ensuresRetLibInv)` to appear explicitly in the
     `waived` list audited against `TrustPolicy.isAllowed`, preventing silent
     regression across incremental governance upgrades.

#### 1.2 Curve Finance and Vyper Compiler Re-Entrancy Lock Collision (\$70M Exploit, July 30, 2023)

`Basis: source + execution + documentation`

On July 30, 2023, multiple Curve Finance liquidity pools (`alETH/ETH`,
`msETH/ETH`, `pETH/ETH`, and `CRV/ETH`) compiled with the Vyper smart-contract
compiler (versions `0.2.15`, `0.2.16`, and `0.3.0`) were exploited for
approximately \$70 million due to a compiler bug (`GHSA-5824-cm3x-3c38`) that
broke `@nonreentrant` mutual-exclusion locks.

- **Technical mechanism:** In Vyper source code, pool authors annotated both
  `remove_liquidity` and `add_liquidity` (as well as `exchange`) with the
  identical re-entrancy lock key `@nonreentrant('lock')`. Semantically, at the
  Vyper source level (`L_src`), all functions sharing the string key `'lock'`
  must read and write a single shared storage slot `slot("lock")`: entering
  `remove_liquidity` sets `storage[slot("lock")] := 1`, causing any re-entrant
  call to `add_liquidity` during an external ETH transfer callback to revert.
  However, in `vyper/semantics/analysis/data_positions.py` (introduced in commit
  `053f06f` for Vyper `0.2.15`), `set_reentrancy_key_position` computed storage
  offsets per function definition rather than per unique key name, incrementing
  the storage-slot counter each time it encountered `@nonreentrant('lock')` on a
  new function. Consequently, in the compiled EVM bytecode (`L_tgt`),
  `remove_liquidity` checked and set storage slot $k$, while `add_liquidity`
  checked and set storage slot $k + 1$.
- **Exploit execution:** During `remove_liquidity`, the Curve pool updated total
  LP token supply (`burnFrom`), transferred native ETH to the caller via a raw
  EVM `CALL` (triggering the attacker contract's `receive()` fallback *before*
  updating the pool's internal token balances `self.balances[i]`), and only
  updated `self.balances` after the `CALL` returned. Inside `receive()`, the
  attacker called `add_liquidity`: because `add_liquidity` checked slot $k + 1$
  (which was `0`), it bypassed the re-entrancy guard and minted new LP tokens
  against a corrupted intermediate state where LP `totalSupply` had already been
  decremented but `self.balances` still held the pre-withdrawal asset amounts.
- **Why source-level auditing and per-function testing missed it:** Source-level
  audits inspected the Vyper source code, where `@nonreentrant('lock')` was
  present on every state-mutating function. Unit tests tested single-function
  re-entrancy (`remove_liquidity` re-entering `remove_liquidity`, which shared
  slot $k$ and correctly reverted) rather than cross-function re-entrancy
  (`remove_liquidity` $\to$ `receive()` $\to$ `add_liquidity`) on the compiled
  bytecode.
- **Architectural lesson for Anneal:**
  1. **Verifying both source and compiled target (`Compiler.Verified`):** Vyper
     `0.2.15`–`0.3.0` is the canonical real-world demonstration of why
     source-only verification (`L_src.sem s ≤ spec`) is insufficient when the
     compiler is unverified. In Anneal's `Trusted/Refinement.lean` (`L420-425`),
     `Compiler.Verified C s spec` requires the three-way conjunction:
     $$L_{\text{src}}.\text{sem}\ s \le \text{spec} \;\land\; \text{Compiles}\ L_{\text{src}}\ L_{\text{tgt}}\ C.\pi\ s\ (C.\text{compile}\ s) \;\land\; L_{\text{tgt}}.\text{sem}\ (C.\text{compile}\ s) \le C.\pi\ \text{spec}$$
     Under `Compiles`, mapping `'lock'` in `remove_liquidity` to slot $k$ and in
     `add_liquidity` to slot $k+1$ breaks the `BehaviorCodec` storage-layout
     simulation (`Stage0Compiler.Compiles`) because the target bytecode allows a
     re-entrant trace that is impossible (`defined = True` with `.reverted` or
     unreachable) in the source semantics.
  2. **Structural call-site invariant checking (`StepResult.externalCall`):** In
     Anneal
     (`support/StructuralExternalCallAndCanaries.lean`),
     the raw ETH transfer `CALL` inside `remove_liquidity` is modeled by
     `StepResult.externalCall boundaryInv next`. Because `remove_liquidity`
     burned LP shares before updating `self.balances[i]`, the pool's
     representation invariant (`AdtInv`: `balances` coherent with `totalSupply`
     OR global re-entrancy lock bit held across *all* entrypoints viewing or
     mutating `balances`) is `false` at the call site if any entrypoint can
     observe the unlocked state.

#### 1.3 Cross-Contract Callback Re-Entrancy, Bridge Initialization, Flash-Loan Governance, and Rounding-Inflation Exploits (Wormhole, Nomad, Mango Markets, Beanstalk, Lendf.Me, Balancer, ERC-4626)

`Basis: source + execution + documentation + derived`

Between 2020 and 2023, over \$1.2 billion was lost across audited and partially
verified protocols due to five recurring boundary failure patterns:

1. **ERC-777 and Read-Only Cross-Contract Callback Re-Entrancy (Lendf.Me \$25M,
   April 19, 2020; Cream Finance \$18.8M, August 30, 2021; Balancer / Curve
   read-only re-entrancy, 2022–2023):**
   - *Mechanism:* Lendf.Me (a fork of Compound v1) implemented
     `supply(asset, amount)` without a re-entrancy lock, assuming
     `IERC20(asset).transferFrom` merely updated token balances. When supporting
     `imBTC` (an ERC-777 token that invokes `tokensToSend` on the sender before
     transferring), an attacker called `supply` a second time inside the
     `tokensToSend` callback before the outer `supply` updated `userBalances`,
     overwriting the first balance read and doubling credited collateral. Even
     when protocols added re-entrancy locks to *mutating* functions, **read-only
     re-entrancy** exploited `view` functions (`get_virtual_price()` in Curve or
     `getRate()` in Balancer) that lacked `@nonreentrant` guards: during a
     native ETH transfer in `remove_liquidity`, an attacker's `receive()`
     callback entered a *separate* lending protocol that queried Curve's
     `get_virtual_price()` while the Curve pool was mid-withdrawal
     (`totalSupply` reduced, `balances` not yet reduced), reading an
     artificially inflated LP token price and borrowing against it.
   - *Anneal primitive mapping:* Anneal's
     `StepResult.externalCall boundaryInv next` requires `boundaryInv = true`
     *at the moment control leaves the module*. If external code can query any
     public accessor (including read-only getters), `boundaryInv` must hold for
     the module's observable state before the external call executes
     (checks-effects-interactions), or every accessor must check the module lock
     so mid-transition states are unobservable.
2. **Capability-Handle Spoofing at FFI / Syscall Boundaries (Wormhole \$324M,
   February 2, 2022):**
   - *Mechanism:* On Solana, Wormhole's `verify_signatures` instruction checked
     Guardian secp256k1 signatures by calling the deprecated helper
     `solana_program::sysvar::instructions::load_instruction_at` on an
     `instruction_acc` `AccountInfo` passed by the caller. `load_instruction_at`
     did not verify that `instruction_acc.key == sysvar::instructions::id()`.
     The attacker passed a spoofed account whose raw byte buffer mimicked a
     previously executed `Secp256k1` precompile instruction, forging a
     `GuardianSet` attestation and minting 120,000 `wETH` (\$324M).
   - *Anneal primitive mapping:* In Anneal's `BehaviorCodec` and library
     boundary contract (`MirVal.satisfiesInv` / `AdtInv`), deserializing an
     external raw pointer or `AccountInfo` into a trusted system-capability type
     without verifying the address/tag predicate violates `decodeQuery` /
     `AdtInv` admission: `decodeOut = none` (and `WellFormedOn safetyPre`)
     rejects any pipeline that treats an unvalidated untrusted byte slice as a
     verified `Sysvar` capability.
3. **Default-Zero Map Lookup / Initialization Polarity Inversion (Nomad Bridge
   \$190M, August 1, 2022):**
   - *Mechanism:* In Nomad's `Replica.sol` upgrade (commit `945667b`),
     `initialize` called `_setRoot(0x00)`, setting `confirmAt[bytes32(0)] = 1`.
     For any unproven message `m`, `messages[keccak256(m)]` defaulted to
     `bytes32(0)` in EVM zero-initialized storage. When `process(m)` checked
     `acceptableRoot(messages[_messageHash])`, looking up `confirmAt[0x00]`
     returned `1 <= block.timestamp` (`true`), accepting arbitrary forged
     withdrawal messages without a Merkle proof.
   - *Anneal primitive mapping:* This is the exact runtime dual of Anneal's
     negative-polarity fail-open trap
     (`support/BehaviorCodecExpressiveness.lean`): mapping
     an uninitialized/unproven state (`0x00` or `.stuck`) to a passing boolean
     guard (`confirmAt[0x00] = 1`). In Anneal's `Partial` and `StepResult`,
     uninitialized or unstepped states map to `.stuck` / `defined = False`,
     never to a valid proof witness.
4. **Flash-Loan Instantaneous Quorum Capture (Beanstalk \$182M, April 17, 2022)
   and Thin-Book Self-Trade Oracle Manipulation (Mango Markets \$110M, October
   11, 2022):**
   - *Mechanism:* Beanstalk's `emergencyCommit(uint32 bip)` allowed a 2/3
     supermajority of staked Stalk/Silo deposits to execute an arbitrary
     `delegatecall` governance payload in the same block (`0` timelock delay
     after a 1-day BIP registration). The attacker flash-loaned \$1B in
     stablecoins, deposited them into the Silo to acquire 79% voting power for a
     single transaction, called `emergencyCommit` on a malicious BIP to drain
     \$182M, and repaid the flash loan in the same block. In Mango Markets, the
     attacker took opposing long and short `MNGO-PERP` positions across two
     accounts and bought spot `MNGO` on thin order books to pump the oracle mark
     price by 1,300% within minutes, borrowing \$110M against unrealized
     self-traded PnL exceeding the pool's total market depth.
   - *Anneal primitive mapping:* Both failures stem from verifying a 1-step
     transitional check (`votes >= 2/3` at a single instant, or
     `collateral * spotPrice >= debt`) without enforcing a multi-step trace
     invariant across `StepResult.externalCall` boundaries (`boundaryInv`
     requiring time-weighted average balances across strictly positive block
     intervals $\Delta t > 0$ and bounding collateral valuation by realizable
     liquidation depth).
5. **ERC-4626 Empty-Vault Rounding Inflation Attack:**
   - *Mechanism:* Standard ERC-4626 tokenized vaults compute shares minted on
     `deposit(assets)` as $\lfloor \text{assets} \cdot S / A \rfloor$, where $S$
     is `totalSupply` and $A$ is `totalAssets`. When a vault is empty
     ($S = 0, A = 0$), an attacker deposits `1 wei` ($S = 1, A = 1$), then
     directly transfers $10^{18}\text{ wei}$ of the underlying token to the
     vault address via `ERC20.transfer` ($S = 1, A = 10^{18} + 1$). When a
     legitimate victim subsequently deposits $1.9 \times 10^{18}\text{ wei}$,
     the vault computes
     $\lfloor 1.9 \times 10^{18} \cdot 1 / (10^{18} + 1) \rfloor = 1\text{ share}$
     ($S = 2, A = 2.9 \times 10^{18} + 1$). The attacker then redeems their 1
     share for
     $\lfloor 1 \cdot (2.9 \times 10^{18}) / 2 \rfloor = 1.45 \times 10^{18}\text{ wei}$,
     stealing $0.45 \times 10^{18}\text{ wei}$ of the victim's deposit via
     integer division truncation.
   - *Anneal primitive mapping:* Under
     `Compiles RealVaultSpec EvmVaultBytecode codec`, `BehaviorCodec` bounds the
     quantization error between ideal rational share accounting and `U256`
     floor/ceil division; if an attacker can perturb `totalAssets` via an
     out-of-band `StepResult.externalCall` (direct token donation) so that
     rounding error exceeds 1 basis point of a depositor's principal, `Compiles`
     fails unless virtual shares/assets offset (`dead shares`) are present.

#### 1.4 Certora CVL Vacuity Traps, `HAVOC_ECF` Optimism, KEVM Abstractions, and Move Prover / Bytecode Verifier Soundness Bugs

`Basis: documentation + source + derived`

Even when formal verification tools (Certora Prover, Runtime Verification KEVM,
and the Move Prover / Move Bytecode Verifier) are applied directly to smart
contracts, historical vulnerability disclosures show four tool-level failure
modes:

1. **CVL `require` Over-Constraint and Rule Vacuity (`--rule_sanity`):**
   - *Mechanism:* In Certora Verification Language (CVL), specifications mix
     `require P;` (which filters out execution traces where $\neg P$, placing
     $P$ on the left of $\to$) with `assert Q;`. In complex multi-contract
     specs, engineers frequently write helper functions containing `require`
     statements (e.g., constraining storage invariants, non-zero denominators,
     or timestamp bounds). Whenever two `require` clauses subtly contradict each
     other—or when every non-reverting path through a contract method violates a
     later `require`—the verification condition
     $\text{PathCondition} \land P_1 \land P_2 \implies Q$ holds **vacuously**
     (`False → Q`), and the Certora Prover reports a green checkmark
     (`VERIFIED`) without checking `Q` on a single execution path. Certora had
     to introduce `--rule_sanity basic/advanced` (checking satisfiability of
     $\text{PathCondition} \land \bigwedge_i P_i$) because vacuous specs
     repeatedly passed in production audits.
   - *Anneal primitive mapping:* Anneal eliminates this failure mode
     structurally in two ways:
     1. In `Trusted/Refinement.lean` (`L148-180`), `VerificationResultOn` always
        proves baseline `L_src.WellFormedOn pre` alongside `specs`, and
        `InhabitedPre pre` + `ProductiveOn pre prog` (`∃ q, pre q` and
        `∀ q, pre q → ∃ h, ∃ out, (sem prog q).val h out`) require a
        constructive witness that the precondition is inhabited and that the
        program produces at least one non-empty outcome on every admitted query.
     2. In `ScopedVerificationResult`
        (`support/ProofGatedCompilationAndTrustPolicy.lean`),
        concrete assumptions and waivers are placed **positively** on the right
        (`ob.id ∈ waived ∨ ob.prop`), never on the left of `→` where a
        contradiction could discharge `assert Q` via `False.elim`.
2. **Certora `HAVOC_ECF` vs. `HAVOC_ALL` External Call Optimism:**
   - *Mechanism:* When a verified contract makes an unresolved external call,
     Certora's default summary mode is `HAVOC_ECF` ("Havoc External Contract
     Fields"), which allows the external call to mutate other contracts' storage
     but **assumes the external call cannot re-enter and mutate the current
     contract's storage**. If a contract has a cross-function re-entrancy bug
     (such as the Lendf.Me ERC-777 or Vyper `@nonreentrant` bug), a CVL rule run
     under default `HAVOC_ECF` silently assumes re-entrancy is impossible and
     reports `VERIFIED`! Conversely, switching to `HAVOC_ALL` wipes the current
     contract's storage completely to arbitrary unvalidated values, breaking all
     representation invariants unless the user manually writes
     `requireInvariant` assumptions (which can re-introduce vacuity or unsoundly
     assume the broken invariant holds during re-entrancy).
   - *Anneal primitive mapping:* Anneal's
     `StepResult.externalCall boundaryInv next` paired with
     `CallerFramePreserved` and `AdtInv` solves the exact `HAVOC_ECF` vs.
     `HAVOC_ALL` dilemma: it neither assumes re-entrancy cannot happen
     (`HAVOC_ECF`) nor wipes private stack frames (`HAVOC_ALL`). Instead, it
     enforces that `boundaryInv` (`AdtInv` on all exposed state) holds *before*
     the external call, preserves unexposed caller-frame locals
     (`CallerFrameIsolated`), and demonically quantifies over all post-call
     states satisfying `AdtInv`, soundly covering arbitrary-depth re-entrant
     callbacks by fuel induction (`open_world_callback_composition_sound`).
3. **Move Prover / Move Bytecode Verifier Soundness and Reference-Borrow Bugs in
   Aptos and Sui (2022–2024):**
   - *Mechanism:* Move separates static verification into the on-chain **Move
     Bytecode Verifier** (which enforces type safety, resource linearity, and
     reference borrow checking in Rust before module publication) and the
     off-chain **Move Prover** (which translates Move bytecode to Boogie/Z3).
     Multiple critical soundness bugs were discovered in both layers:
     - In the Move Prover, integer bit-shift operations (`<<`, `>>`) and vector
       borrow-mutation summaries in the Boogie prelude historically modeled
       shifts without matching the Move VM's abort-on-shift-width-$\ge$-bitwidth
       check, allowing the Move Prover to verify functions as `aborts_if false`
       that aborted at runtime.
     - In the Move Bytecode Verifier on Aptos and Sui, reference-safety and
       type-instantiation verifier bugs (such as the 2022–2023 Zellic / OtterSec
       bytecode verifier disclosures in `reference_safety` and stack-usage
       verifiers, including integer overflow in `meter` / borrow-graph join
       states) allowed crafted Move bytecode to pass verification while aliasing
       mutable references (`&mut T`) and corrupting linear `Coin` resources.
   - *Anneal primitive mapping:* In the Move ecosystem, the Bytecode Verifier is
     a large procedural Rust pass (~15,000+ lines of
     graph/abstract-interpretation code) inside the TCB, and the Move Prover
     trusts both the Boogie translation and the Z3 SMT solver
     (`trustLevel > 0`). In Anneal, the borrow/type checker and SMT tactics live
     *outside* the kernel TCB in `theory/` or untrusted proof generation
     (`proof_gen.rs`), and the Lean 4 kernel checks a foundational proof of
     `Trusted.CrateTheorem` directly over small-step operational semantics gated
     by a 100%-mutation-killing `BoundaryCanarySuite`.

### Historical Failure Analysis 2. Statutory Tax, Social-Benefit Eligibility, and Accounting Ledger Failures

#### 2.1 French DGFiP `M`-Language Income Tax and Family-Benefit Bugs Uncovered by `Mlang` and `Catala` (2020–2021)

`Basis: source + execution + documentation`

Since 1990, the French *Direction Générale des Finances Publiques* (DGFiP) has
computed national personal income tax (*impôt sur le revenu*) for over 38
million households using a custom, non-Turing-complete domain-specific language
called **`M`** (~90,000 lines of declarative variable rules and verification
constraints compiled to C). In parallel, French social and family benefits
(*Allocations Familiales*, *Aide Personnalisée au Logement*) and US federal tax
deductions (such as Earned Income Tax Credit under 26 U.S.C. § 32 and Section
121 capital-gains exclusions) are drafted in legislative prose structured as
**default logic with hierarchical exceptions** (a base rule in subsection (a),
overridden by exceptions in (b) and (c), which are themselves overridden by
special cases in (d)).

When Merigoux, Monat, Chataing, and Protzenko reverse-engineered the DGFiP `M`
compiler into **`Mlang`** (CC 2021) and formalized French family-benefit and US
tax statutes in **`Catala`** (ICFP 2021, verified in $\text{F}^\star$), they
uncovered three systemic failure modes in production government code:

1. **Out-of-order exception flattening and priority inversions:** Because `M`
   and legacy COBOL/C agency engines lack first-class prioritized default terms,
   programmers manually flatten nested statutory exceptions into deeply nested
   `if-then-else` trees or sequential variable re-assignments. When Parliament
   enacts an amendment adding a new exception or modifying an income threshold,
   programmers patch an intermediate variable (`calcul_impot`) in a different
   file from the base rule. In the official French family-benefit (*Allocation
   de Soutien Familial* / *Allocations Familiales*) implementation analyzed by
   the `Catala` team, manual flattening inverted the statutory precedence
   between resource-ceiling phase-outs (*complément dégressif*) and child-age
   adjustments, causing edge-case households near the income ceiling to receive
   legally incorrect benefit amounts.
2. **Undefined variable evaluation and IEEE-754 / integer truncation workarounds
   in `M`:** In the DGFiP `M` codebase, uninitialized variables and division by
   zero were suppressed by ad-hoc runtime coercions (`undef` silently coerced to
   `0.0` in arithmetic contexts, and IEEE-754 `double` rounding discrepancies
   fixed via `floor(x + 0.000001)`). `Mlang` revealed that different C compilers
   and optimization levels could alter tax outcomes on boundary cent values if
   floating-point intermediate values were not pinned to an exact deterministic
   semantics.
3. **Missing default branches ("statutory holes"):** Formalizing Section 121 of
   the US Internal Revenue Code and French social security articles in
   `Catala`'s default calculus
   ($\text{default}\ \langle e_1, \dots, e_n \mid e_{\text{just}} \mapsto e_{\text{cons}} \rangle$)
   exposed inputs where *two* exceptions fired simultaneously without a
   statutory priority order (`ConflictError`), or where *no* rule fired because
   mutual exclusions left a gap (`EmptyError`).
- **Architectural lesson for Anneal:**
  1. **Distinguishing conflict (`Partial.ub`) from missing-default stuckness
     (`.stuck`) and enforcing `ProductiveOn`:** In `Catala`, a statutory
     conflict (`ConflictError`) or missing default (`EmptyError`) is a runtime
     exception unless statically discharged. Mapping legislative default logic
     into Anneal's `StepResult` (`trusted/lean/Trusted/StepResult.lean`) maps an
     unresolved equal-priority statutory conflict to `StepResult.failed .ub`
     (`defined = False`) and an unhandled statutory gap (`EmptyError`) to
     `ReachesPrefix.noStep` / `.stuck` (`isSafe = False`). Proving
     `ProductiveOn ValidTaxpayerProfile statuteProg` statically guarantees both
     **conflict-freedom** and **totality** across all taxpayer profiles before a
     tax-year engine is deployed.
  2. **Literate source-to-target refinement
     (`Compiles StatuteLang ProductionRustLang`):** Rather than hand-maintaining
     a flat imperative re-encoding of a statute, `Compiles` requires a
     machine-checked refinement proof that the optimized imperative/branch-free
     tax binary produces the exact cent-level `SemObs` outcome of the
     prioritized statutory specification.

#### 2.2 Australian Robodebt Automated Income-Averaging Scandal and Section 1073B Apportionment Mismatch (2015–2023)

`Basis: normative + documentation + derived`

Between July 2015 and November 2019, the Australian Department of Human Services
(Services Australia) operated the **Online Compliance Intervention (OCI)**—known
publicly as **Robodebt**—which automatically raised 470,000+ welfare overpayment
debts totaling AU\$1.76 billion against social-security recipients. In *Amato v
The Commonwealth of Australia* (Federal Court of Australia, VID611/2019, consent
orders November 27, 2019) and the **Royal Commission into the Robodebt Scheme**
(Final Report delivered July 7, 2023), the scheme—along with a separate
decades-long administrative practice under **Section 1073B of the *Social
Security Act 1991 (Cth)***—was ruled unlawful.

- **Technical and statutory root cause:** Under Sections 1067G and 1068 of the
  *Social Security Act 1991 (Cth)*, entitlement to Youth Allowance and Newstart
  Allowance is defined **per fortnightly instalment period**
  $t \in \{1, \dots, 26\}$ as a non-linear, piecewise-affine function with an
  income-free threshold $\theta$ and taper rates $\tau_1, \tau_2$:
  $$\text{Entitlement}(y_t) = \max\!\big(0,\; B_0 - \tau_1 \max(0, y_t - \theta_1) - \tau_2 \max(0, y_t - \theta_2)\big)$$
  where $y_t$ is the recipient's actual ordinary income earned in fortnight $t$.
  Because $\text{Entitlement}(\cdot)$ is **concave** (due to the
  $-\max(0, \cdot)$ phase-out tapers above threshold $\theta_1$), **Jensen's
  Inequality** implies that for any fluctuating income stream
  $(y_1, \dots, y_{26})$ with annual Australian Taxation Office (ATO) sum
  $Y = \sum_{t=1}^{26} y_t$ and mean $\bar{y} = Y / 26$:
  $$\sum_{t=1}^{26} \text{Entitlement}(y_t) \;\neq\; 26 \cdot \text{Entitlement}\!\left(\frac{Y}{26}\right)$$
  Specifically, a casual or seasonal worker who earned \$0 during 13 unemployed
  fortnights (legally entitled to full benefit $13 \cdot B_0$) and earned high
  wages during 13 employed fortnights (receiving \$0 benefit) had a positive
  average $\bar{y} = Y / 26 > \theta_1$. Robodebt's algorithm replaced unknown
  fortnightly $y_t$ values with the constant average $\bar{y} = Y / 26$,
  computing a phantom overpayment debt whenever
  $\text{Entitlement}(\bar{y}) < B_0$ during the recipient's unemployed
  fortnights—unless the recipient could produce years-old fortnightly payslips
  to refute the algorithm. Separately, under Section 1073B, agency software
  apportioned single payslips spanning employment dates across adjacent
  Centrelink assessment fortnights outside the statutory conditions permitted by
  the Act.
- **Architectural lesson for Anneal:**
  1. **Refinement vs. Abstraction polarity (`Compiles` vs. `Abstracts`) under
     lossy query projection (`BehaviorCodec`):** Robodebt is a textbook
     violation of `BehaviorCodec` query round-tripping
     (`decodeQuery_encodeQuery`) and refinement polarity. The statutory language
     `L_statute` requires a 26-vector query
     $q = (y_1, \dots, y_{26}) \in \mathbb{N}^{26}$, whereas the ATO
     data-matching feed provides only the scalar sum
     $Y = \sum_t y_t \in \mathbb{N}$. Because the projection
     $\pi(y_1, \dots, y_{26}) = \sum_t y_t$ is **non-injective** (many-to-one),
     there is no valid `BehaviorCodec` with `decodeQuery (encodeQuery q) = q`.
     Replacing $q$ with $(\bar{y}, \dots, \bar{y})$ computes only a **lower
     bound on entitlement** (an *upper bound* on debt), which goes in the
     **wrong order direction** (`≥` instead of `≤`) to justify a legal debt
     determination! In Anneal, if only coarse aggregate input $Y$ is available,
     the query must demonically quantify over all fortnightly vectors
     $\{(y_1, \dots, y_{26}) \mid \sum_t y_t = Y\}$, which permits raising a
     debt only for the minimum overpayment guaranteed across *every* possible
     distribution of $Y$ across the 26 fortnights.

#### 2.3 UK Post Office Fujitsu Horizon Accounting Ledger Bugs (1999–2019, *Bates & Others v Post Office Ltd* [2019] EWHC 3408 (QB))

`Basis: normative + documentation + source`

Between 1999 and 2015, the UK Post Office prosecuted more than 700
subpostmasters and subpostmistresses for false accounting and theft based on
shortfalls reported by the **Horizon** retail and accounting system (developed
by ICL / Fujitsu). In *Bates & Others v Post Office Ltd (No 6: Horizon Issues)*
`[2019] EWHC 3408 (QB)` (1,164 paragraphs plus a 461-paragraph Technical
Appendix delivered by Mr Justice Fraser on December 16, 2019), the High Court
established that Horizon contained at least 29 distinct software defects that
unilaterally corrupted branch balance sheets:

1. **The Callendar Square (Falkirk) Bug (`PEAK PC0061213`, 2000–2006):**
   - *Mechanism:* In Legacy Horizon, branch terminals wrote accounting
     transactions to a local Riposte message-store database, which replicated to
     central servers. When a Riposte message-table index became corrupted or
     experienced a network timeout during replication, the counter wrote
     duplicate transaction records into the central audit trail without
     displaying the duplicate on the local branch Roll-Over balance screen,
     creating phantom branch shortfalls of thousands of pounds.
2. **The Dalmellington Bug / Branch Outreach Issue (`PEAK PC0208735`,
   2010–2015):**
   - *Mechanism:* In Horizon Online (`HNG-X`), when a subpostmaster transferred
     cash between a main branch and an outreach sub-office ("Remming In"), the
     Java counter UI froze if a network packet was delayed while waiting for the
     backend BRDB (Branch Database) response. Because the UI did not disable the
     `Enter` key or attach an idempotency token (`TransactionUUID`) to the
     user's confirmation action, each press of `Enter` on the frozen screen
     queued and committed an additional duplicate cash receipt in the backend
     database (creating a £24,000 phantom shortfall at the Dalmellington branch
     in Scotland).
3. **The Receipts and Payments Mismatch Bug (`PEAK PC0203589`, August–October
   2010):**
   - *Mechanism:* In `HNG-X`, when a subpostmaster cancelled or rolled back a
     balance trading period transition after moving a discrepancy into a local
     suspense account, the local counter cache cleared the transaction while the
     central Oracle BRDB database retained it. Consequently, the branch's
     Receipts and Payments summary remained balanced locally on the counter
     terminal while the central ledger recorded a hidden shortfall (affecting
     62+ branches), which Fujitsu support staff ("SSC") manually edited in live
     production databases via raw SQL (`BRDB` direct injection) without branch
     visibility or audit signatures.
- **Architectural lesson for Anneal:**
  1. **Idempotency and conservation invariants in `BehaviorCodec` and
     `SemObs`:** In a double-entry accounting language `L_ledger`, `SemObs` is
     equipped with the Abelian group conservation invariant
     $\sum \text{Debits} - \sum \text{Credits} = 0$, and every external user
     action carries a unique idempotency key in `Query`. Under
     `Compiles SpecLedgerLang DistributedBranchLang codec`, a UI retry on a
     frozen screen corresponds to stuttering steps on the *same* logical query
     (`EventualBehaviorOf`); any backend implementation that commits $k > 1$
     ledger postings for a single logical confirmation violates `obs_decodeOut`
     and `Compiles`.
  2. **Divergence between local view and authoritative artifact (`SingleSource`
     binding):** The Receipts and Payments Mismatch bug—where the counter screen
     showed a balanced account while the central database recorded a debt—is the
     accounting analogue of the dual-emitter divergence identified in
     `support/ProofGatedCompilationAndTrustPolicy.lean`
     (where `.anneal/Mir.lean` and `.anneal/Prog.s` could diverge). Binding the
     displayed branch receipt and the central ledger commit to a single
     cryptographically hashed, kernel-checked transaction record eliminates
     split-brain accounting states.

#### 2.4 US SNAP and Medicaid (MAGI vs. Non-MAGI) Contradictory Eligibility Exceptions and Benefit Cliffs

`Basis: normative + documentation + derived`

In US federal and state public-benefits rules engines—governing the Supplemental
Nutrition Assistance Program (SNAP, 7 U.S.C. § 2014 / 7 C.F.R. § 273.9) and
Medicaid under the Affordable Care Act (42 U.S.C. § 1396a(e)(14), Modified
Adjusted Gross Income `MAGI` vs. legacy SSI-linked `non-MAGI`
aged/blind/disabled categories)—two structural specification bugs repeatedly
arise in state Integrated Eligibility Systems (IES):

1. **Contradictory Cross-Program Preconditions ("Bureaucratic Catch-22s"):**
   Under ACA Medicaid expansion, non-disabled adults are evaluated under IRS
   tax-household `MAGI` counting rules (42 C.F.R. § 435.603), whereas applicants
   turning 65 or qualifying via disability transition to `non-MAGI` SSI asset
   and deeming rules. In multiple state eligibility engines (and during
   2023–2024 post-PHE Medicaid "unwinding" auto-renewal redeterminations), state
   decision tables routed applicants who reported *both* self-employment tax
   deductions and disability indicators into a compound eligibility guard that
   required `isMagiHousehold = false` (due to disability screening) AND
   evaluated an income-disregard sub-table gated on `isMagiHousehold = true`,
   causing both branches to evaluate to `Ineligible` without conducting the
   federally mandated *ex parte* cross-category review (42 C.F.R. §
   435.916(f)(1)).
2. **Unbounded Marginal Effective Tax Rate (METR $> 100\%$) Cliffs:** When
   SNAP's 130% Federal Poverty Level (FPL) gross-income limit, Medicaid's 138%
   FPL cutoff, and Childcare Development Fund (CCDF) copayment steps interact
   without coupled monotonicity verification, a \$100/month wage increase across
   the 130% or 138% FPL boundary can trigger a \$3,000–\$8,000 net loss in
   household disposable resources.
- **Architectural lesson for Anneal:**
  1. **`InhabitedPre` per statutory category and `ProductiveOn` across category
     handoffs:** In Anneal, if a state rules engine partitions applicants into
     eligibility tracks $T_1, \dots, T_k$ with entry guards $\text{pre}_i$,
     requiring `InhabitedPre pre_i` for every statutory cohort prevents
     self-contradictory guard conjunctions (`isMagi ∧ ¬isMagi`), and requiring
     `ProductiveOn StatutorilyEligibleApplicant iesEngine` forces the *ex parte*
     fallback transition to fire rather than dropping the applicant into an
     unhandled rejection state.

### Historical Failure Analysis 3. Electronic Voting, Combinatorial Auction, and Financial Exchange Failures

#### 3.1 SwissPost / Scytl E-Voting Cryptographic Shuffle and Trapdoor Commitment Flaw (2019–2020, Haines, Lewis, Pereira, and Teague)

`Basis: source + normative + documentation`

In February–March 2019, Swiss Post published the source code and formal
specification of its electronic voting system (developed by Scytl and intended
for binding Swiss cantonal elections) for public intrusion testing. Within
weeks, Sarah Jamie Lewis, Olivier Pereira, and Vanessa Teague (later joined by
Thomas Haines in *"How not to prove your election outcome"*, IEEE S&P 2020,
`doi:10.1109/SP40000.2020.00055`) discovered fatal soundness flaws in both the
**Bayer-Groth verifiable mixnet shuffle proof** and the **Schnorr/Chaum-Pedersen
non-interactive zero-knowledge (NIZK) proofs** that allowed complete,
undetectable manipulation of election tallies despite passing the official
Universal Verifier.

- **Technical root cause (missing commitment-key trapdoor check and Fiat-Shamir
  under-hashing):**
  1. **Trapdoor Pedersen Commitment in the Bayer-Groth Shuffle:** To prove in
     zero knowledge that a mix node permuted and re-encrypted a vector of
     ElGamal ciphertexts $(C_1, \dots, C_N)$ without dropping or substituting
     votes, the Bayer-Groth protocol commits to the permutation matrix using a
     multi-pedersen commitment key
     $ck = (g, g_1, \dots, g_n) \in \mathbb{G}^{n+1}$ in a prime-order subgroup
     $\mathbb{G} \subset \mathbb{Z}_p^*$. Soundness of the Bayer-Groth shuffle
     proof holds **if and only if the prover does not know any discrete
     logarithm relation $\log_g(g_i)$ among the generators in $ck$**. If whoever
     generates $ck$ knows $x_i$ such that $g_i = g^{x_i} \pmod p$ (the
     commitment trapdoor), they can open a commitment to *any* forged
     permutation and produce a Bayer-Groth proof that passes verification with
     probability $1$. In Scytl's implementation (`CommitmentParamsGenerator`),
     the commitment generators $g_i$ were generated inside a trusted setup
     component **without emitting a verifiable seed derivation or NIZK proof of
     knowledge/indistinguishability**, and the Universal Verifier specification
     simply assumed $ck$ was trapdoor-free without checking how $g_i$ were
     constructed!
  2. **Insecure Fiat-Shamir Hash Serialization (`ExponentiationProof`):** In
     several Schnorr/Chaum-Pedersen NIZK proofs used for vote decryption and
     electoral-board key generation, Scytl concatenated variable-length strings
     into the Fiat-Shamir SHA-256 hash transcript without length prefixes or
     omitted the public statement generators from the hash challenge
     $e = H(\text{statement}, \text{commitment})$, allowing an attacker to shift
     field boundaries or choose statement bases *after* computing the challenge.
- **Architectural lesson for Anneal:**
  1. **Never treat a synthesized witness parameter as an unchecked TCB
     hypothesis (`TCBModel` and `TrustedBoundary.lean`):** The SwissPost/Scytl
     bug occurred because the Universal Verifier checked
     `VerifyShuffle(ck, C, C', π) = true` under the unverified implicit
     assumption `TrapdoorFree(ck)`. In Anneal
     (`support/ProofGatedCompilationAndTrustPolicy.lean`),
     any soundness premise that is not constructively discharged inside the
     verifier must either be verified from a transparent seed derivation (e.g.,
     hash-to-group nothing-up-my-sleeve construction checked by the auditor) or
     explicitly surface as a `TrustedAssumption` in `VerificationResultOn`. If a
     cryptographic parameter generator is unverified, placing `TrapdoorFree(ck)`
     silently outside the verifier allows a forged proof to pass at
     `trustLevel = 0`.
  2. **Injective transcript encoding (`BehaviorCodec`):** The Fiat-Shamir
     hash-concatenation flaw (`H(a || b) == H(a' || b')` for
     $(a, b) \neq (a', b')$) is a direct failure of `decodeQuery_encodeQuery`:
     any serialization into a verification challenge transcript must be a
     round-tripping injection so distinct public statements cannot collide on
     the same fiat-shamir challenge.

#### 3.2 Australian Senate Single Transferable Vote (STV) Tabulation Discrepancies (Pattinson, Tiwari, and Goré)

`Basis: source + execution + documentation`

In Australian Senate elections (governed by Section 273 of the *Commonwealth
Electoral Act 1918 (Cth)*), seats are allocated by **Single Transferable Vote
(STV)** using the **Inclusive Gregory Method**: when a candidate's tally $T_c$
exceeds the Droop quota $Q = \lfloor V / (S + 1) \rfloor + 1$, all ballots
currently assigned to $c$ are transferred to their next continuing preference at
a fractional **transfer value**:
$$\text{TV}_c = \frac{T_c - Q}{N_c}$$
where $N_c$ is the total number of ballot papers sitting in $c$'s pile.

When Dirk Pattinson, Mukesh Tiwari, and Rajeev Goré formalized the Australian
Senate STV rules in the **Coq theorem prover** and compared their extracted,
certifying tabulator against the Australian Electoral Commission's (AEC)
production `EasyCount` software and statutory text, they uncovered subtle
specification and arithmetic divergences:

1. **Order of Truncation in Fractional Transfer Values vs. Vote Totals:**
   Section 273(9B) of the *Commonwealth Electoral Act 1918* specifies that the
   transfer value $\text{TV}_c$ is truncated to 8 decimal places, and when a
   parcel of $k$ identical ballots is transferred at value $\text{TV}_c$, the
   votes added to the receiving candidate's tally are
   $\lfloor k \cdot \text{TV}_c \rfloor$ (dropping any fractional remainder).
   However, ambiguity in the statute over whether parcels from multiple prior
   transfers are grouped *before* or *after* multiplying by $\text{TV}_c$ and
   truncating to an integer changes candidate totals by up to $P$ votes (where
   $P$ is the number of distinct sub-parcels), which can flip the elimination
   order of marginal candidates in close sixth-seat Senate races (such as the
   2013 Western Australia Senate recount, which was decided by 14 votes out of
   1.3 million ballots before being voided).
2. **Tie-Breaking Non-Determinism vs. Deterministic Software Implementations:**
   The statute mandates that when two candidates have identical tallies at an
   elimination or surplus-transfer step and prior-round counts are also tied,
    the Australian Electoral Officer must decide the order by lot
    (angelic/external
   nondeterminism). Legacy tabulation implementations frequently broke ties
   implicitly via array index or candidate storage order (`0`-indexed ballot
   position) without pausing for an explicit external tie-break input.
- **Architectural lesson for Anneal:**
  1. **Separating statutory non-determinism (`Partial` outcome sets and
     `StepResult.externalCall`) from implementation choices (`Compiles`):** In
     Anneal, when a statute permits multiple valid outcomes (or requires an
     external Electoral Officer tie-break lot), the specification
     `L_statute.sem s` models the tie-break via `StepResult.externalCall` (or a
     multi-element outcome set `Out → Prop`). Under `Compiles`, a tabulation
     binary cannot silently invent a tie-break outcome without recording the
     external officer decision in `SemObs`, and exact fixed-point parcel
     truncation in `L_src` forces the compiled Rust tabulator to match the
     statutory parcel-grouping order to the single vote.

#### 3.3 Knight Capital \$440M Limit-Order-Book Router Failure (August 1, 2012, SEC Release No. 34-70694): Dead-Code Flag Reuse and Partial Deployment

`Basis: normative + documentation + derived`

On the morning of August 1, 2012, **Knight Capital Americas LLC**—then the
largest retail equity market maker in the United States—activated new software
in its **Smart Market Access Routing System (`SMARS`)** to participate in the
New York Stock Exchange's new Retail Liquidity Program (RLP). Within 45 minutes
of market open (9:30–10:15 AM EDT), `SMARS` routed 4 million unintended child
orders for 397 million shares across 154 NYSE-listed stocks in response to just
212 incoming retail parent orders, accumulating \$3.5 billion in net long
positions and \$3.15 billion in net short positions and inflicting a realized
pre-tax loss of **\$440 million** (SEC Administrative Proceeding File No.
3-15570, Exchange Act Release No. 34-70694, October 16, 2013).

- **Technical root cause (bitflag repurposing + dead-code cumulative-quantity
  omission + 1-of-8 server deployment drift):**
  1. **Dead-Code `Power Peg` Function with Removed Stop-Condition Check:** In
     2003, Knight deactivated an experimental order-execution algorithm called
     **`Power Peg`**, which was designed to move stock prices during test runs
     by repeatedly sending aggressive child orders and tracking cumulative share
     fills until the parent order's target quantity was reached. In 2005, during
     a refactoring of `SMARS`, developers moved the cumulative fill-quantity
     comparison out of the `Power Peg` function **without deleting the
     `Power Peg` function itself or testing whether it still terminated**. As a
     result, if `Power Peg` was ever invoked after 2005, it entered an unbounded
     loop that fired child orders into external exchanges at full line rate
     (`~97,000` orders/minute) without ever checking whether the parent order
     had already been 100% filled.
  2. **Order Bitflag Repurposing and 7-of-8 Server Deployment:** In July 2012,
     to route orders to the new NYSE RLP, Knight engineers repurposed the exact
     boolean bitflag in the internal `SMARS` order message struct that had
     previously gated `Power Peg`: in the new 2012 RLP build, setting that flag
     invoked the new RLP router and excised the call site to `Power Peg`.
     However, during manual deployment on July 27–31, 2012, a technician copied
     the new `SMARS` binary to only **7 of the 8 production `SMARS` servers**.
     When markets opened on August 1, 2012, upstream servers tagged retail
     parent orders with the repurposed RLP flag; the 1st through 7th `SMARS`
     servers routed them normally to the NYSE RLP, while the **8th server**
     (still running the un-updated binary) interpreted the repurposed bitflag as
     a command to execute the broken `Power Peg` loop.
- **Architectural lesson for Anneal:**
  1. **Unbounded loop / non-termination detection via `EventualBehaviorOf` and
     order-quantity conservation in `SemObs`:** In `EventualBehaviorOf`
     (`support/BehaviorCodecExpressiveness.lean`), a compiler
     or order-routing state machine that enters a non-terminating child-order
     emission loop on a finite parent order quantity $Q_{\text{parent}}$
     violates both `EventualBehaviorOf` termination alignment and the `SemObs`
     order-conservation invariant
     ($\sum_{j} q_{\text{child}, j} \le Q_{\text{parent}}$), stepping to
     `Partial.ub` as soon as cumulative child order quantity exceeds
     $Q_{\text{parent}}$.
  2. **Cryptographic single-source binary binding
     (`trusted/root-manifest.sha256` and `.olean`-bound emission):** Knight
     Capital's 8th server failed because the binary running in production was
     not cryptographically bound to the schema version of the wire protocol
     (`BehaviorCodec`). Anneal's single-source artifact binding
     (`support/ProofGatedCompilationAndTrustPolicy.lean`
     and `trusted/audit`) hashes the exact verified target artifact alongside
     its `BehaviorCodec` interface, rejecting mixed-version deployments where a
     wire tag's `decodeQuery` meaning has changed.

#### 3.4 Multi-Object Vickrey / VCG Auction Revenue Collapse and Sybil/Shill-Bidding Vulnerabilities (New Zealand 1990 Spectrum Auction; Ausubel and Milgrom 2006)

`Basis: documentation + derived`

The **Vickrey-Clarke-Groves (VCG)** mechanism is the crown jewel of normative
economic mechanism design: for any quasi-linear utility profile
$u_i(x, p_i) = v_i(x) - p_i$, allocating the social-welfare-maximizing outcome
$x^* \in \arg\max_x \sum_i b_i(x)$ and charging each winner their marginal
externality on other bidders:
$$p_i = \max_{x} \sum_{j \neq i} b_j(x) \;-\; \sum_{j \neq i} b_j(x^*)$$
is **Dominant-Strategy Incentive Compatible (DSIC)**—truthful bidding
($b_i = v_i$) is a dominant strategy for every isolated individual agent $i$.

Despite this mathematically proven theorem, real-world deployments of VCG and
sealed-bid Vickrey auctions have suffered catastrophic economic failures:

1. **The 1990 New Zealand Radio/Television Spectrum Auction Collapse (McMillan
   1994):** Advised by economic consultants relying on the theoretical
   efficiency of Vickrey's second-price theorem, the New Zealand government
   auctioned UHF television and cellular spectrum licenses using simultaneous
   sealed-bid second-price auctions without reserve prices. Because bidder
   valuations were publicly observable only after the fact and competition in
   regional niches was thin, revenues collapsed to **NZ\$36 million** against a
   projected **NZ\$250 million**: in one notorious case, a bidder submitted a
   truthful valuation bid of **NZ\$100,000** for a nationwide spectrum license
   and paid the second-highest bid of **NZ\$6**; in another lot, a bidder bid
   **NZ\$7 million** and paid **NZ\$5,000**.
2. **The Ausubel-Milgrom "Lovely but Lonely Vickrey Auction" Sybil / False-Name
   and Core-Violation Paradox (Ausubel & Milgrom 2006; Yokoo, Sakurai, and
   Matsubara 2004):** Ausubel and Milgrom proved that whenever goods exhibit
   **complementarities** (superadditive valuations $v(A \cup B) > v(A) + v(B)$),
   the VCG mechanism violates **Core Stability**, **Revenue Monotonicity**, and
   **Sybil / False-Name Proofness**:
   - Consider Goods $A$ and $B$. Bidder 1 is a national carrier who values the
     package $\{A, B\}$ at \$2B (and single items at \$0). Bidders 2 and 3 are
     regional carriers who value $A$ at \$2B and $B$ at \$2B respectively.
   - Under VCG, Bidders 2 and 3 win $A$ and $B$ (total welfare \$4B vs. \$2B).
     What does Bidder 2 pay? Without Bidder 2, the optimal allocation gives $B$
     to Bidder 3 (welfare \$2B). With Bidder 2, Bidder 3 still gets \$2B. Thus
     Bidder 2's VCG payment is $\$2\text{B} - \$2\text{B} = \$0$, and by
     symmetry Bidder 3 also pays **\$0**! Even though Bidder 1 offered \$2B in
     cash for $\{A, B\}$, the VCG mechanism hands $\{A, B\}$ to Bidders 2 and 3
     for **zero revenue** (an outcome outside the Core, since Bidder 1 and the
     seller form a blocking coalition).
   - Worse, **a single bidder can profitably cheat VCG via a Sybil attack**: if
     only Bidder 1 ($v(\{A, B\}) = \$2\text{B}$) is present in the auction,
     Bidder 1 can create two pseudonymous shell accounts ("Bidder 2" bidding
     \$2B on $A$ and "Bidder 3" bidding \$2B on $B$), win both licenses, and
     reduce their own VCG payment to **\$0**!
- **Architectural lesson for Anneal:**
  1. **Multi-agent coalitional and Sybil framing in `StepResult.externalCall`
     and relational `Query` specifications:** Standard DSIC proves safety only
     against *unilateral single-ID deviations*
     $(v_i, v_{-i}) \to (v'_i, v_{-i})$ under the closed-world assumption that
     agent identities $i \in \{1, \dots, n\}$ are fixed and non-colluding. In an
     open-world environment (permissionless smart contracts or shell-company
     spectrum bidding), an adversary's action space in `StepResult.externalCall`
     includes **identity splitting**
     ($1 \text{ physical agent} \mapsto k \text{ Sybil IDs}$). In Anneal,
     verifying a mechanism under open-world identity creation requires lifting
     `Query` to partition-equivalence classes of bids or proving
     **Core-Selecting / False-Name-Proof** postconditions (`L.SpecOn`) where
     total payments satisfy no-blocking-coalition constraints
     ($\sum_{i \in S} p_i \ge v_j(S)$ for every losing bidder $j$).

### Historical Failure Analysis 4. Medical Device Firmware and Aviation Collision-Avoidance Rule Failures

#### 4.1 Becton Dickinson / CareFusion Alaris GP Infusion Pump Interactive Number-Entry and Rounding Anomalies Uncovered in PVS (Masci and Thimbleby)

`Basis: source + execution + documentation`

Volumetric bedside infusion pumps deliver high-risk intravenous medications
(insulin, norepinephrine, heparin, potassium chloride, chemotherapy) where a 10x
rate error is rapidly fatal. Between 2005 and 2015, the US FDA received over
56,000 adverse event reports and 710 deaths associated with infusion pumps,
prompting the FDA's **Infusion Pump Improvement Initiative (2010)** and the UL
2800 / IEC 60601-2-24 safety standards.

When Paolo Masci, Harold Thimbleby, Paul Curzon, Patrick Oladimeji, and Rimvydas
Rukšėnas formally modeled the **CareFusion (BD) Alaris GP Volumetric Infusion
Pump** user-interface firmware in the **PVS (Prototype Verification System)**
theorem prover (CAV 2013, FM 2014, SAFECOMP 2015), they discovered that the
pump's interactive number-entry state machine violated basic **Predictability,
Reversibility, and Monotonicity** properties under realistic clinician
keystrokes:

1. **Asymmetric Chevron Step-Size and Clamping / Saturation Traps:** The Alaris
   GP lacks a numeric 0–9 keypad; clinicians adjust the infusion rate
   ($\text{mL/h}$) and Volume to be Infused ($\text{VTBI}$) using four chevron
   keys (`double-up` $\mathord{\uparrow\uparrow}$, `single-up`
   $\mathord{\uparrow}$, `single-down` $\mathord{\downarrow}$, `double-down`
   $\mathord{\downarrow\downarrow}$) whose increment step sizes change
   dynamically by decade ($0.1, 1, 10, 100\text{ mL/h}$) and depend on internal
   floating-point timer scaling. Masci and Thimbleby proved in PVS that:
   - **Irreversibility ($\downarrow(\uparrow(x)) \neq x$):** Starting from valid
     fractional rates (e.g., $x = 99.7\text{ mL/h}$), pressing `double-up` snaps
     and rounds the display to an integer decade boundary ($100\text{ mL/h}$),
     after which pressing `double-down` steps to $90\text{ mL/h}$ rather than
     returning to $99.7\text{ mL/h}$.
   - **Silent Upper-Bound Clamping Drop:** When entering a target rate near the
     configured hard ceiling (`MaxRate`), a single extra press of
     $\mathord{\uparrow\uparrow}$ saturates at `MaxRate` without an audible
     modal lock, causing subsequent compensating presses of
     $\mathord{\downarrow}$ by a clinician looking at the paper chart to compute
     from `MaxRate` rather than the intended value.
2. **Missing Decimal Point / Key-Bounce 10x–100x Overdose on Numeric Keypads (B.
   Braun / Hospira / Alaris PC Unit):** On keypad-based pumps modeled in
   Thimbleby's *Press On* and PVSio-web studies, entering `1`, `.`, `5` when the
   decimal-point key suffers contact bounce or when a leading zero is omitted in
   modes that silently ignore `.` above $100\text{ mL/h}$ parses `1.5` as
   **`15`** (10x overdose) or `10.5` as **`105`** without raising a syntax error
   (`StepResult.stuck` / modal confirmation prompt).
- **Architectural lesson for Anneal:**
  1. **Total, prefix-free input parsing in `BehaviorCodec` (`decodeOut = none` /
     invalid-input rejection):** In Anneal's `PartialBehaviorCodec`
     (`support/BehaviorCodecExpressiveness.lean`),
     `decodeQuery` and `decodeOut` must reject syntactically malformed or
     ambiguous keystroke sequences (such as two decimal points `1..5`, an
     ignored decimal point above a decade threshold, or an unacknowledged
     saturation clamp) by returning `none` (or transitioning to an explicit
     modal error state in `SemObs`), rather than silently coercing `1.5`
     $\mapsto$ `15`.
  2. **Algebraic reversibility as a 2-step `SpecOn` invariant:** Requiring
     $\text{stepDown}(\text{stepUp}(s)) = s$ for all interior states
     $s < \text{MaxRate}$ is a direct `L.SpecOn` relational obligation on the UI
     `SmallStepMachine`.

#### 4.2 Therac-25 Radiation Therapy Linear Accelerator Race Conditions and 8-Bit Counter Overflow (1985–1987, Leveson and Turner 1993)

`Basis: documentation + source + derived`

Between June 1985 and January 1987, the **Therac-25** computer-controlled
medical linear accelerator (manufactured by Atomic Energy of Canada Limited,
AECL) delivered massive radiation overdoses (15,000–25,000 rads of raw 25 MeV
electron beam instead of 200 rads of X-ray photon therapy) to six patients
across clinics in the United States and Canada, killing three and permanently
maiming three. Nancy Leveson and Clark Turner's landmark forensic investigation
(*"An Investigation of the Therac-25 Accidents"*, IEEE Computer 26(7):18–41,
July 1993, `doi:10.1109/MC.1993.274940`) traced the accidents to two distinct
bugs in the PDP-11 assembly real-time executive after AECL removed the hardware
mechanical interlocks present in the earlier Therac-20:

1. **The `Treat` / `Hand` / `Datent` 8-Second Cursor-Edit Race Condition
   (Kennestone, Ontario, and Yakima accidents):**
   - *Mechanism:* The PDP-11 software ran concurrent tasks communicating through
     shared memory without locks. When the radiation technician typed treatment
     parameters on the DEC VT100 terminal, the keyboard handler (`Datent`) wrote
     the mode (`X` for 25 MeV X-ray vs. `E` for low-current Electron mode) into
     a shared variable `MEOS` (2-byte mode/energy word) and set the shared
     variable `Data Entry Complete` (`Tphase = 1`) as soon as the cursor reached
     the bottom `Command` line. Once `Tphase` transitioned, the `Treat` task
     read `MEOS` to configure the bending magnets (`Ptime`, taking ~8 seconds)
     and independently verified that the rotating turntable (`Hand` task) had
     placed the heavy tungsten X-ray target/beam-flattener in the beam path.
     **However, `Datent` only copied edits into the magnet-setting parameter
     block on initial entry, unless it noticed the cursor had moved back up.**
     If an experienced operator typed `X` (X-ray, setting high 25 MeV beam
     current), realized they meant `E` (Electron), and used the VT100 `Up-Arrow`
     key to overwrite `X` with `E`
      and return to the `Command` line *within the 8-second magnet-setting
      window*,
     the turntable task saw the updated `E` (rotating the tungsten target *out*
     of the beam path for low-energy electrons) while the magnet/beam-current
     task never re-read the edited memory word (because the `Datent` completion
     flag was already non-zero), firing a raw, unattenuated 25 MeV high-current
     electron beam directly into the patient!
2. **The Tyler Overflow Bug (8-Bit Shared Flag `Class3` Incrementing to `0`):**
   - *Mechanism:* In the `House` housekeeping task (`Set-Up Test` phase), a
     1-byte unsigned shared variable named `Class3` held the error count of
     collimator/turntable position checks: `Class3 == 0` meant **all interlocks
     verified safe**, whereas `Class3 != 0` meant **unsafe / inhibit beam**.
     Instead of assigning `Class3 := 1` (`MOVB #1, CLASS3`) when a check failed,
     the assembly routine executed `INCB CLASS3` (incrementing `Class3` by 1 on
     every 16.7 ms cycle while the upper collimator was still aligning). Every
     **256th pass** (~4.2 seconds), the 8-bit `INCB CLASS3` wrapped around from
     `255` (`0xFF`) to **`0` (`0x00`)**! If the operator pressed the `Set` key
     during that exact 16.7 ms tick when `Class3 == 0`, the software concluded
     the collimator was aligned and enabled the high-energy beam while the
     field-light mirror was still in the beam path.
- **Architectural lesson for Anneal:**
  1. **Machine-word modular wraparound vs. mathematical `Nat` in target
     semantics (`BoundaryCanarySuite`):** The Therac-25 `INCB CLASS3` bug
     (`255 + 1 = 0` turning an error counter into `0 = Safe`) is the exact
     real-world catastrophe that motivates Anneal's `BoundaryCanarySuite` guard
     modular wraparound and boundary-check mutation canaries (`support/StructuralExternalCallAndCanaries.lean`)
     (`support/StructuralExternalCallAndCanaries.lean`
     and `support/BehaviorCodecExpressiveness.lean`),
     which refutes any trusted evaluator that models fixed-width registers
     (`u8`/`u64`) using unbounded `Nat` addition instead of modular wraparound
     or checked overflow traps.
  2. **Call-site / actuation-site invariant re-verification
     (`StepResult.externalCall`):** In the Therac-25 cursor-edit race, the
     system checked magnet/turntable consistency at the *beginning* of an
     8-second asynchronous hardware routine while allowing concurrent
     shared-state mutation before firing the electron gun. Under Anneal's
     `StepResult.externalCall boundaryInv next`, firing the physical actuator
     (the electron beam) is an external transition whose `boundaryInv`
     (`BeamCurrent == Low ∨ TurntablePosition == XRayTargetLocked`) must
     evaluate to `true` on the **current state at the exact step of beam
     actuation**, not 8 seconds earlier.

#### 4.3 TCAS II Mid-Air Collision over Überlingen (July 1, 2002) and ACAS X Hybrid-Systems Boundary Bugs Uncovered in `KeYmaera` (Jeannin and Platzer 2015–2017)

`Basis: normative + source + documentation`

Airborne Collision Avoidance Systems (**TCAS II** and its FAA NextGen successor
**ACAS X**) issue vertical Resolution Advisories (`RA`: `Climb` at
$\ge 1500\text{ ft/min}$, `Descend` at $\le -1500\text{ ft/min}$,
`Increase Climb`, `Maintain`, or `Reversal`) when two aircraft approach a Near
Mid-Air Collision (NMAC) cylinder ($|h_1 - h_2| < 100\text{ ft}$ vertically and
$r < 500\text{ ft}$ horizontally).

Two major classes of failures—one fatal operational disaster and one set of
formally discovered design defects—illustrate the verification hazards of
cyber-physical rulebooks:

1. **The 2002 Überlingen Mid-Air Collision (Bashkirian Airlines Flight 2937 and
   DHL Flight 611, July 1, 2002; German BFU Investigation Report `AX001-1-2/02`,
   May 2004):**
   - *Mechanism:* At 21:35 UTC over Überlingen, Germany, a Tupolev Tu-154M (BTC
     2937) and a Boeing 757-200SF (DHX 611) converged at Flight Level 360
     ($36,000\text{ ft}$). At 43 seconds before impact, **TCAS II v7.0**
     simultaneously issued coordinated complementary advisories: `Descend` to
     DHL 611 and `Climb` to BTC 2937. However, 7 seconds earlier, an overloaded
     Zurich air traffic controller had verbally instructed BTC 2937 to
     *descend*. Following Russian aviation manual priorities that treated ATC
     instructions as superseding TCAS, the BTC 2937 crew descended—matching DHL
     611's TCAS-commanded descent! Under TCAS II v7.0 logic (**Change 7.0**), a
     reversal logic condition (`Change E7`) required `TCAS` to detect that the
     intruder was failing to follow its RA and reverse DHL 611's advisory from
     `Descend` to `Climb`; however, Change 7.0 suppressed the reversal when
     vertical separation was initially increasing or gated on a delayed altitude
     crossing threshold, so DHL 611's TCAS **never issued a `Climb` reversal**
     (issuing only `Increase Descent` at 22 seconds before impact), and both
     aircraft descended into each other at $29,300\text{ ft}$, killing all 71
     aboard. This led to Eurocontrol/FAA **TCAS II Version 7.1** (`CP112E`),
     which patched the `reversal` state-machine guard for non-compliant
     intruders.
2. **ACAS X Unsafe Advisory Regions Uncovered via `KeYmaera` Hybrid-Systems
   Verification (Jeannin, Ghorbal, Kouskoulas, Gardner, Schmidt, Zawadzki, and
   Platzer, TACAS 2015 / EMSOFT 2015 / STTT 2017,
   `doi:10.1007/s10009-016-0434-1`):**
   - *Mechanism:* Unlike TCAS II's handwritten rule tables, FAA's **ACAS X**
     generates a compressed multi-gigabyte lookup table by solving a discretized
     Markov Decision Process (MDP) via dynamic programming over state tuples
     $(h, \dot{h}_{\text{own}}, \dot{h}_{\text{int}}, \tau, \text{prevRA})$.
     Jeannin, Platzer, and co-authors formulated a continuous Differential
     Dynamic Logic ($\text{d}\mathcal{L}$) safe-able region invariant in the
     **`KeYmaera`** theorem prover (accounting for 5-second pilot response
     delay, $g/4$ to $g/3$ vertical acceleration bounds, and two-sided
     upper/lower parabolic trajectory envelopes) and checked the industrial ACAS
     X Run 13 lookup table against the proved hybrid envelope. They discovered
     **thousands of state-space points where the ACAS X MDP lookup table issued
     unsafe advisories** that could lead to an NMAC even under nominal pilot
     response:
     - **MDP Soft-Penalty Tradeoff ("Goodharting the Reward Function"):**
       Because the MDP solver optimized a numeric reward function combining a
       large finite penalty for NMAC ($-10,000$) with small penalties for
       issuing disruptive alerts or reversals ($-10$), in boundary states where
       an NMAC had low probability under the assumed Gaussian vertical-rate
       transition kernel, the MDP preferred issuing a weak advisory
       (`Do Not Descend` instead of `Climb`) to save the alert penalty—violating
       hard worst-case kinematic safety!
     - **Multilinear Interpolation & Discretization Artifacts:** Between
       discrete grid vertices $(h_i, \dot{h}_j, \tau_k)$, continuous aircraft
       kinematics crossed the parabolic safety boundary inside a grid cell whose
       corners were all marked safe.
- **Architectural lesson for Anneal:**
  1. **Separating hard safety (`Partial.ub` / `WellFormedOn`) from soft
     optimization (`specs`):** The ACAS X MDP failure—where a numeric cost
     function traded off a hard collision-avoidance constraint against a soft
     pilot-comfort penalty—demonstrates why Anneal
     (`Trusted/Refinement.lean:145-180`) strictly separates the non-negotiable
     baseline safety lattice (`Partial.ub` and `L_src.WellFormedOn pre`, where
     `defined = False` is the top element $\top$ that cannot be averaged away by
     probabilities) from secondary functional preferences (`specs`).
  2. **Sound upward abstraction of discrete lookup tables by continuous
     envelopes (`Abstracts L_hybridEnvelope L_lookupTable`):** Following Jeannin
     and Platzer's architecture, a 2-gigabyte MDP lookup table synthesized by an
     untrusted numerical solver need not be trusted: Anneal's `Abstracts`
     relation checks in Lean that every discrete cell of the lookup table
     refines the symbolic $\text{d}\mathcal{L}$ safe-separation inequality
     (including cell-width Lipschitz/Taylor interpolation padding), while
     `StepResult.externalCall` models non-compliant intruder maneuvers (such as
     the Überlingen BTC 2937 descent) via demonic choice over physical aircraft
     acceleration bounds.

### Historical Failure Analysis 5. Cross-Domain Synthesis Matrix: Mapping Historical Failures to Anneal's Four Trusted Primitives

`Basis: derived`

The table below synthesizes all 14 historical postmortem classes across DeFi,
statutory law, accounting, voting, auctions, financial markets, medical devices,
and aviation, showing the exact failure mechanism and the corresponding Anneal
primitive in `trusted/lean/Trusted/` (and its reference-corpus hardening
extensions) that closes the vulnerability class:

| Historical Incident / System | Domain & Date | Primary Failure Mechanism | Anneal Primitive 1: `Language`, `SemObs` & `Partial` (`defined` vs. `Partial.ub`) | Anneal Primitive 2: `BehaviorCodec`, `Compiles` & `Abstracts` | Anneal Primitive 3: `StepResult.externalCall`, `EventualBehaviorOf`, `ProductiveOn` & `InhabitedPre` | Anneal Primitive 4: `VerificationResult`, `TrustPolicy` & `BoundaryCanarySuite` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Euler Finance (\$197M)** | DeFi Lending (`2023-03-13`, EIP-14) | New `donateToReserves` function omitted `checkLiquidity` health check, allowing self-inflicted bad debt and profitable self-liquidation | `Partial.ub` on account solvency breach (`collateral * c < debt / b`) | `Compiles` requires every lowered entrypoint to preserve `SemObs` reserve solvency | `ProductiveOn` ensures healthy liquidations succeed without reverting | Whole-crate `CrateTheorem` (`EnsuresRetLibInv` on all `pubSafe` fns); unproved upgrade methods must be explicitly listed in `waived` |
| **Curve Finance / Vyper `@nonreentrant` (\$70M)** | Smart-Contract Compiler (`2023-07-30`, Vyper `0.2.15`–`0.3.0`) | `data_positions.py` allocated distinct storage slots to `remove_liquidity` and `add_liquidity` sharing `@nonreentrant('lock')` | Source semantics blocks re-entrant entry; target EVM bytecode exhibits cross-function state corruption (`Partial.ub`) | **`Compiler.Verified` & `Compiles`:** target bytecode fails storage-slot simulation against source lock semantics | **`StepResult.externalCall`:** raw ETH `CALL` before `self.balances` update violates `boundaryInv` if any entrypoint can enter unlocked | Rejects trusting source-only audits (`L_src.sem s ≤ spec`) without target compilation proof (`Compiles`) |
| **Lendf.Me (\$25M) & Balancer/Curve Read-Only Re-Entrancy** | DeFi Callbacks (`2020-04-19` / `2022–2023`) | ERC-777 `tokensToSend` and native ETH `receive()` callbacks re-entered mutating or `view` oracle functions (`get_virtual_price`) mid-update | `Partial.ub` on share-price or balance-conservation violation | `obs_decodeOut` preserves observable oracle price invariants across external boundaries | **Direct hit for `StepResult.externalCall`:** `boundaryInv = false` steps immediately to `.failed .ub` if `AdtInv` is broken at callback site | `BoundaryCanarySuite` includes explicit re-entrant callback refutation canary (`canary_reentrant_callback_rejected`) |
| **Wormhole (\$324M), Nomad (\$190M), Beanstalk (\$182M) & ERC-4626 Inflation** | Bridges, Governance & Vaults (`2022`) | Spoofed `Sysvar` account (`load_instruction_at`), `confirmAt[0x00] = 1` zero-root bug, 0-delay flash-loan `emergencyCommit`, and `1 wei` share rounding | Unproven message acceptance or share theft > rounding bound is `Partial.ub` | `PartialBehaviorCodec` (`decodeOut = none`) rejects unvalidated `Sysvar` capability pointers and bounds rational-to-`U256` rounding drift | `StepResult.externalCall` models flash-loan / donation interleavings; `EventualBehaviorOf` enforces multi-block timelock separation | Polar admission guards (`ConstIsSafe` / non-zero root canaries) prevent mapping default `0x00` to verified `true` |
| **Certora CVL Vacuity, `HAVOC_ECF` & Move Prover / Verifier Bugs** | Formal Verifiers (`2020–2024`) | Contradictory `require` rules passing vacuously (`--rule_sanity`), `HAVOC_ECF` ignoring re-entrancy, and Boogie/bytecode borrow-checker bugs | `WellFormedOn pre` proved alongside `specs` so vacuous functional specs never weaken baseline safety | Proof-gated compilation eliminates intermediate verifier IR (`Boogie` / `AnSSA`) from the TCB via `Preorder.le_trans` | `InhabitedPre pre` + `ProductiveOn pre prog` statically refute vacuous `require` preconditions; `externalCall` replaces optimistic `HAVOC_ECF` | Positive per-obligation `ScopedVerificationResult` (`ob.id ∈ waived ∨ ob.prop`) prevents `False.elim` explosion from contradictory assumptions |
| **French DGFiP `M`-Language & Family-Benefit Bugs (`Mlang` / `Catala`)** | Statutory Tax & Benefits (`2020–2021`, ICFP/CC 2021) | Manual flattening of statutory exception hierarchies inverted priority of family-benefit phase-outs; `undef` coerced to `0.0` | Equal-priority statutory conflict maps to `Partial.ub`; missing default (`EmptyError`) maps to `.stuck` | `Compiles StatuteLang RustLang` proves imperative tax binary refines declarative prioritized default calculus | `ProductiveOn ValidHousehold statute` proves every taxpayer profile resolves to a unique, non-stuck legal determination | `TrustPolicy` tracks transitional tax-year rounding waivers explicitly |
| **Australian Robodebt & Section 1073B Apportionment** | Welfare Compliance (`2015–2023`, Royal Commission `2023-07-07`) | Replaced 26 fortnightly income inputs $(y_1, \dots, y_{26})$ with annual average $Y/26$ inside a concave entitlement formula (violating Jensen's Inequality) | Raising an overpayment debt exceeding actual fortnightly statutory liability is `Partial.ub` | **Refinement vs. Abstraction polarity:** non-injective sum projection $Y = \sum y_t$ violates `decodeQuery_encodeQuery`; averaging goes in the wrong lattice direction (`≥` vs. `≤`) | Demonic choice (`StepResult.choice .demonic`) over all $(y_1, \dots, y_{26})$ summing to $Y$ bounds provable minimum debt | Rejects unlawful administrative assumptions via `TrustPolicy` audit |
| **UK Post Office Fujitsu Horizon (`Bates v Post Office`)** | Retail Accounting Ledger (`1999–2019`, `[2019] EWHC 3408`) | Frozen UI `Enter` retries (**Dalmellington**), duplicate Riposte rows (**Callendar Square**), and local-cache/central-DB split-brain (**Receipts & Payments Mismatch**) | Unbalanced double-entry posting ($\sum \text{Dr} \neq \sum \text{Cr}$) or phantom duplicate debit is `Partial.ub` | `BehaviorCodec` with idempotency keys maps repeated UI retries to stuttering on 1 logical transaction (`obs_decodeOut`) | `EventualBehaviorOf` collapses $k$ network retry steps into 1 committed transaction; single-source binding prevents local/central split-brain | Eliminates blind legal presumption of correctness in unverified software (`trustLevel` accounting) |
| **US SNAP & Medicaid (`MAGI` vs. `non-MAGI`) Engines** | Social Benefits (`2014–2024`) | Contradictory cross-category guards (`isMagi ∧ ¬isMagi`) dropping disabled self-employed applicants without *ex parte* review | Unhandled applicant drop is `.stuck` (`defined = False`) | `Compiles FederalStatute StateIesEngine` enforces federal 42 C.F.R. § 435.916 floor | **`InhabitedPre` & `ProductiveOn`:** proves every statutory eligibility category is inhabited and *ex parte* fallback is total | State Section 1115 waivers modeled as positive `waived` IDs in `VerificationResult` |
| **SwissPost / Scytl E-Voting Shuffle & Commitment Flaw** | Cryptographic E-Voting (`2019–2020`, IEEE S&P 2020) | Universal Verifier assumed commitment key $ck = (g, g_1, \dots, g_n)$ had no known discrete-log trapdoor without checking seed/NIZK construction; non-injective Fiat-Shamir hashing | Accepting a forged tally proof is `Partial.ub` | `decodeQuery_encodeQuery` enforces injective length-prefixed serialization into Fiat-Shamir transcripts | Constructive witness verification of setup parameters inside the verifier | **Universal `TCBModel` realizability:** prohibits hiding `TrapdoorFree(ck)` as an unchecked implicit TCB assumption |
| **Australian Senate STV Tabulation (`EasyCount` vs. Coq)** | Election Tabulation (`2013–2020`, Pattinson et al.) | Ambiguous parcel-grouping order before integer truncation $\lfloor k \cdot \text{TV}_c \rfloor$ and implicit array-index tie-breaking | Dropping valid votes or unauthorized tie-break is `Partial.ub` | `Compiles StatutoryStv CertifyingTabulator` pins exact rational-to-fixed-point parcel truncation | `StepResult.externalCall` models statutory Electoral Officer lot-drawing for exact ties; `ProductiveOn` proves loop termination | Audited certificate checker verifies round-by-round transfer log |
| **Knight Capital `SMARS` `Power Peg` (\$440M)** | Equity Order Routing (`2012-08-01`, SEC Rel. `34-70694`) | Repurposed RLP bitflag triggered dead `Power Peg` code (missing cumulative fill check) on 1 of 8 servers left un-updated | Emitting child orders with $\sum q_{\text{child}} > Q_{\text{parent}}$ is `Partial.ub` | `BehaviorCodec` binds wire bitflag semantics to exact protocol version | **`EventualBehaviorOf`:** rejects non-terminating child-order emission loops that never reach `.terminated` | Single-source `.olean`-bound artifact hashing prevents 7-of-8 server binary/codec drift |
| **New Zealand 1990 Spectrum Auction & VCG Sybil Paradox** | Mechanism Design (`1990` / Ausubel & Milgrom `2006`) | Thin competition (NZ\$100k bid paying NZ\$6) and superadditive package bids enabling \$0-payment Core violations and Sybil split-bidding | Profitable Sybil deviation or Core blocking-coalition breach is `Partial.ub` | `Compiles MechanismSpec SolverCode` pairs MILP solver with primal-dual certificate checker | `StepResult.externalCall` models open-world Sybil identity splitting ($1 \mapsto k$ pseudonyms); `ProductiveOn` proves market clearing | Separates NP-hard optimality timeout waivers (`waived`) from strict Individual Rationality and Core safety |
| **Alaris GP Pump (`PVS`), Therac-25 & TCAS II / ACAS X (`KeYmaera`)** | Medical Devices & Aviation (`1985–2017`) | Alaris chevron rounding/10x key-bounce; Therac-25 8-bit `INCB CLASS3` wraparound & 8s cursor race; Überlingen reversal failure & ACAS X MDP soft-penalty unsafe cells | Overdose, unshielded 25 MeV beam, or Near Mid-Air Collision (NMAC) is `Partial.ub` ($\top$, never traded off against soft penalties) | `Abstracts HybridEnvelope AcasLookupTable` verifies discrete MDP tables against continuous $\text{d}\mathcal{L}$ barrier certificates; `decodeOut = none` rejects malformed keystrokes | `StepResult.externalCall` re-verifies `boundaryInv` at exact beam-firing step and models non-compliant intruder aircraft maneuvers | **`BoundaryCanarySuite` (modular wraparound and boundary-check mutation canaries in `support/StructuralExternalCallAndCanaries.lean`):** kills 8-bit/64-bit modular wraparound bugs (`255 + 1 = 0`) and maps GSN hardware assumptions to `TrustPolicy` |

## Boundaries

### Part I — Real-World Tool Survey Boundaries

The following scope boundaries and distinctions govern reuse of this report:

- **No bundled external DSL parsers in `trusted/` (`unsupported` / by design):**
  Anneal's `trusted/` directory intentionally contains only the Lean 4
  refinement and small-step kernel definitions (`trusted/lean/`), the `.olean`
  auditor (`trusted/audit/`), `cargo-anneal`, and `anneal-rustc-capture`.
  Translating external specifications (`Catala`, `Marlowe`, `CVL`, `HL7 CQL`,
  `Cedar`, `MFOTL`) into Lean 4 `Language` definitions or verifying Rust engines
  implementing them happens entirely in user crates or `theory/` libraries
  outside the TCB.
- **Cryptographic hardness and physical ODE modeling assumptions
  (`known not to apply` to pure trace refinement without domain libraries):** In
  Domain 7 (`Verificatum`, `ElectionGuard`, `Belenios`) and Domain 9
  (`KeYmaera X`, `Mobileye RSS`, `STAR`), computational soundness against a
  polynomial-time adversary (DDH / Fiat-Shamir random oracle) or continuous ODE
  trajectory containment ($x' = f(x)$) requires domain-specific mathematical
  theories in `theory/`. Anneal's `trusted/` primitives verify the discrete
  executable verifier, state machine, or lookup-table interpolation code and
  bind those domain theorems via `Abstracts` and `TrustPolicy` without adding
  real-analysis or cryptographic axioms to `trusted/lean/`.
- **Empirical black-box fuzzers (`Slither`, `Echidna`, `Medusa`) and unverified
  floating-point simulators (`OpenFisca`, `ORE`, `Calvano` tabular scripts)
  (`known not to apply` as deductive proof witnesses):** While fuzzing and Monte
  Carlo simulation falsify invariants (`∃ q, ¬ (sem p q).defined`), a finite
  fuzzing campaign does not construct a Lean 4 proof term for `L.sem p ≤ spec`.
  To discharge an Anneal obligation, external solver or simulation outputs must
  be paired with a verified certificate checker or inductive proof in `theory/`.
- **Closed-source commercial engines (`Oracle Intelligent Advisor`,
  `LexiFi MLFi`, `SAP GTS`, `Certora` internal Kotlin decompiler)
  (`not examined` at implementation source level):** Where upstream source code
  is proprietary, findings in this report rely on published normative
  specifications, peer-reviewed papers, and public SDK schemas rather than
  direct source inspection of the proprietary binaries.

### Part II — Historical Verification Failure Postmortem Boundaries

To prevent future agents from over-generalizing the historical comparisons in
this report, the following boundaries apply:

1. **Not examined — direct execution of third-party blockchain VMs, `Catala`,
   `PVS`, or `KeYmaera X` inside Anneal's build:** The findings on Euler
   Finance, Vyper, Certora, Move, `Catala`, Robodebt, Horizon, SwissPost/Scytl,
   Australian STV, Knight Capital, VCG auctions, Alaris GP, Therac-25, and TCAS
   II / ACAS X are established from primary source repositories, CVEs, court
   judgments, regulatory inquiry reports, and peer-reviewed verification papers
   (`documentation`, `normative`, and `source` evidence). Anneal's repository
   (`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`) currently targets
   Rust (`Runtime(PostCleanup)` MIR and x86-64 machine code) checked in Lean 4;
   instantiating `Language` for EVM bytecode, `Catala` default terms, or hybrid
   ODE flowpipes is an architectural design mapping (`derived`), not a currently
   shipping compiler backend in `trusted/rustc-capture/`.
2. **Known not to apply — purely economic or human-organizational failures
   outside formal specifications:** Formal verification of software and
   mechanisms in Anneal cannot by itself prevent a legislature from enacting a
   socially regressive tax schedule, an auctioneer from setting a zero reserve
   price in a thin single-item market (as in parts of the 1990 New Zealand
   spectrum auction), or an air traffic controller from issuing a verbal command
   contradicting an onboard TCAS advisory (as at Überlingen) unless the formal
   environmental model (`StepResult.externalCall` and `Query`) explicitly
   includes non-compliant human/counterparty behavior in its demonic choice set.
3. **Unsupported — probabilistic expected-value tradeoffs over `Partial.ub`:**
   Anneal's `Partial B` type constructor
   (`trusted/lean/Trusted/Refinement.lean:245-261`) models Undefined Behavior
   (`defined = False`) as the single qualitative top element `Partial.ub`.
   Quantitative Markov Decision Process (MDP) reward tradeoffs (such as ACAS X's
   expected-cost scoring) cannot be used to relax `defined = True`; any
   probabilistic or expected-utility reasoning must live inside the defined
   payload `B` (`Out → Prop` instantiated over probability mass functions in
   `theory/`) while preserving hard `defined = True` safety envelopes
   unconditionally.

## Evidence

### Part I — Real-World Tool Survey Evidence

### 1. Pinned Anneal Repository Evidence (`source` + `execution`)

- **Core refinement lattice, `Partial`, `Language`, `Compiles`, `Abstracts`, and
  `VerificationResultOn`:**
  `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`,
  `trusted/lean/Trusted/Refinement.lean:207-472`.
- **Small-step transition trees, `StepResult`, `PrefixOutcome`, `ReachesPrefix`,
  and `BehaviorOf`:** `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`,
  `trusted/lean/Trusted/StepResult.lean:58-199`.
- **Hardened `BehaviorCodec`, `PartialBehaviorCodec`, `EventualBehaviorOf`,
  `ProductiveOn`, and `InhabitedPre`:**
  `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`,
  `support/BehaviorCodecExpressiveness.lean` and
  `support/BehaviorCodecExpressiveness.lean`.
- **Structural `StepResult.externalCall`, pre-call `boundaryInv`, and
  straight-line fuel induction (`open_world_callback_composition_sound`):**
  `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`,
  `support/StructuralExternalCallAndCanaries.lean`
  and `support/StructuralExternalCallAndCanaries.lean:148-482, 5250-5295`.
- **Positive per-obligation `ScopedVerificationResult`, `TrustPolicy` gating,
  and `TCBModel` realizability:**
  `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`,
  `support/ProofGatedCompilationAndTrustPolicy.lean`
  and `support/ProofGatedCompilationAndTrustPolicy.lean`.

### 2. Primary Literature, Normative Specifications, and Upstream Repositories (`normative` + `documentation`)

- **Domain 1 (Statutory Law & Tax Compilers):**
  - Denis Merigoux, Nicolas Chataing, and Jonathan Protzenko, *"Catala: A
    Programming Language for the Law"*, Proc. ACM Program. Lang. 5 (ICFP 2021),
    Article 77, DOI `10.1145/3473582`; repository `CatalaLang/catala`.
  - Sarah B. Lawsky, *"A Logic for Statutes"*, Florida Tax Review 21(1), 2017.
  - French DGFiP `M` language extractor and compiler: `MLang/mlang`.
  - `OpenFisca` (`openfisca/openfisca-core`), `PolicyEngine`
    (`PolicyEngine/policyengine-us`), `PSL Tax-Calculator`
    (`PSLmodels/Tax-Calculator`), `Blawx` (`Lexpedite/blawx`), `L4`
    (`smucclaw/dsl`).
- **Domain 2 (Legal Contracts, Derivatives & Cap Tables):**
  - Simon Peyton Jones, Jean-Marc Eber, and Julian Seward, *"Composing
    Contracts: An Adventure in Financial Engineering"*, ICFP 2000, DOI
    `10.1145/351240.351267` (foundation of `LexiFi MLFi`).
  - Pablo Lamela Seijas and Simon Thompson, *"Marlowe: Financial Contracts on
    Blockchain"*, ISoLA 2018 / FMBC 2020; repository
    `input-output-hk/marlowe-cardano`.
  - FINOS `ISDA Common Domain Model (CDM)` (`finos/common-domain-model`,
    `finos/rune-dsl`), `ACTUS` (`actusfrf/actus-core`), `Daml`
    (`digital-asset/daml`), `Accord Project Ergo` (`accordproject/ergo`),
    `Open Cap Format` (`Open-Cap-Table-Coalition/Open-Cap-Format-OCF`),
    `Stipula` (`stipula-language/stipula`), and `Symboleo`
    (`Smart-Contract-Modelling-uOttawa/Symboleo-JS-2`).
- **Domain 3 (Smart Contracts, DeFi & AMM Solvency):**
  - David L. Dill, Wolfgang Grieskamp, Junkil Park, Shaz Qadeer, Meng Xu, and
    Jingyi Emma Zhong, *"The Move Prover"*, CAV 2020, LNCS 12224, DOI
    `10.1007/978-3-030-53288-8_7`.
  - Danil Annenkov, Jakob Botsch Nielsen, and Bas Spitters, *"ConCert: A Smart
    Contract Certification Framework in Coq"*, CPP 2020, DOI
    `10.1145/3372885.3373829`; repository `AU-COBRA/ConCert`.
  - Kushal Babel, Philip Daian, Mahimna Kelkar, and Ari Juels, *"Clockwork
    Finance: Automated Analysis of Economic Security in Smart Contracts"*, IEEE
    S&P 2023, DOI `10.1109/SP46215.2023.10179346`; repository
    `kushalbabel/Clockwork-Finance`.
  - `Certora Prover` (`Certora/CertoraProver`), `Halmos` (`a16z/halmos`), `Hevm`
    (`ethereum/hevm`), `KEVM`/`Kontrol` (`runtimeverification/evm-semantics`,
    `runtimeverification/kontrol`), `Mi-Cho-Coq` (`nomadic-labs/mi-cho-coq`),
    `Aeneas` (`AeneasVerif/aeneas`), `Slither`/`Echidna`/`Medusa`
    (`crytic/slither`, `crytic/echidna`, `crytic/medusa`).
- **Domain 4 (Financial Clearinghouses, LOB Matching & Ledgers):**
  - Grant Olney Passmore and Denis Ignatovich, *"Formal Verification of
    Financial Algorithms"*, CADE-26 (2017), LNCS 10395, DOI
    `10.1007/978-3-319-63046-5_3`; repository `imandra-ai/imandra-docs`.
  - `TigerBeetle` (`tigerbeetle/tigerbeetle`), `Beancount`
    (`beancount/beancount`), `Ledger` (`ledger/ledger`),
    `Simple Binary Encoding` (`real-logic/simple-binary-encoding`), `QuickFIX`
    (`quickfix/quickfix`), `Open-Source Risk Engine (ORE)`
    (`OpenSourceRisk/Engine`), and `QuantLib` (`lballabio/QuantLib`).
- **Domain 5 (Mechanism Design, Auctions & Matching Markets):**
  - Kevin Leyton-Brown, Paul Milgrom, and Ilya Segal (with Neil Newman et al.),
    *"Economics and Computer Science of a Radio Spectrum Reallocation"*, PNAS
    114(28), 2017, DOI `10.1073/pnas.1616385114`; repository `ubc-tea/SATFC`.
  - Marco B. Caminati, Manfred Kerber, Christoph Lange, and Colin Rowat, *"Set
    Theory or Higher Order Logic to Represent Auction Concepts in Isabelle?"* /
    Isabelle AFP entry `VCG` (*Combinatorial Vickrey-Clarke-Groves Auctions*).
  - Peter Gammie, *"Stable Matching"*, Isabelle Archive of Formal Proofs (AFP
    `Stable_Matching`, 2016).
  - John P. Dickerson, David F. Manlove, Benjamin Plaut, Tuomas Sandholm, and
    James Trimble, *"Position-Indexed Formulations for Kidney Exchange"*, ACM EC
    2016; repository `JohnDickerson/KidneySolver`.
  - `MATPOWER` (`MATPOWER/matpower`) and `PowerModels.jl`
    (`lanl-ansi/PowerModels.jl`).
- **Domain 6 (Game Theory & Equilibrium Verification):**
  - Emilio Calvano, Giacomo Calzolari, Vincenzo Denicolò, and Sergio Pastorello,
    *"Artificial Intelligence, Algorithmic Pricing, and Collusion"*, American
    Economic Review 110(10), 2020, DOI `10.1257/aer.20190623`.
  - Marta Kwiatkowska, Gethin Norman, David Parker, and Gabriel Santos,
    *"PRISM-games 3.0: Stochastic Game Verification with Concurrency, Equilibria
    and Time"*, CAV 2020 / TACAS 2020, DOI `10.1007/978-3-030-45237-7_21`;
    repository `prismmodelchecker/prism-games`.
  - Alessio Lomuscio, Hongyang Qu, and Franco Raimondi, *"MCMAS: An Open-Source
    Model Checker for the Verification of Multi-Agent Systems"*, CAV 2009 / STTT
    2017, DOI `10.1007/s10009-015-0378-x`; repository `lomuscio/mcmas`.
  - `Gambit` (`gambitproject/gambit`) and `OpenSpiel`
    (`google-deepmind/open_spiel`).
- **Domain 7 (Voting Systems, Social Choice & Governance):**
  - Douglas Wikström, *"A Commitment-Consistent Proof of a Shuffle"* /
    `Verificatum` mixnet (`verificatum/verificatum-vmn`).
  - Microsoft `ElectionGuard` Specification & SDK (`microsoft/electionguard`).
  - Véronique Cortier, Pierrick Gaudry, and Stéphane Glondu, *"Belenios: A
    Simple Private and Verifiable Electronic Voting System"*, Foundations of
    Security, Protocols, and Equational Reasoning (2019); repository
    `belenios/belenios`.
  - Dirk Pattinson and Mukesh Tiwari (with Rajeev Goré, Jeremy Dawson, Milad
    Ghale), *"Schulze and Ranked-Choice Voting in Coq"* / *"Verifying Single
    Transferable Vote"*, VoteID 2015, LNCS 9269, DOI
    `10.1007/978-3-662-48899-7_12`.
  - Manuel Eberl, *"Social Choice Types"* / *"Randomised Social Choice"*,
    Isabelle Archive of Formal Proofs (`Social_Choice_Types`, 2016).
  - `OpenZeppelin Governor` (`OpenZeppelin/openzeppelin-contracts`).
- **Domain 8 (Clinical Pathways & Medical Device Calculators):**
  - HL7 International, *Clinical Quality Language (CQL) Release 1.5*
    Specification; repository `cqframework/clinical_quality_language`.
  - Ying Yuan, Kenneth R. Hess, Susan G. Hilsenbeck, and Donald A. Berry (and
    Suyu Liu & Ying Yuan), *"Bayesian Optimal Interval Design: A Simple and
    Well-Performing Design for Phase I Oncology Trials"*, JRSS Series C / Series
    B (2015/2016), DOI `10.1111/rssb.12089`.
  - FDA Generic PCA Infusion Pump (`GPCA`) verification models in `Kind2`
    (`kind2-mc/kind2`) and `PVSio-web` (`masci/pvsio-web`); `Asbru` / `KIV`
    formal clinical guideline proofs; `SPRINT` / `STAR` glycemic protocols.
- **Domain 9 (Cyber-Physical Rules of the Road & Assurance Cases):**
  - Nathan Fulton, Stefan Mitsch, Jean-Baptiste Jeannin, Brandon Bohrer, and
    André Platzer, *"KeYmaera X: An Axiomatic Tactical Theorem Prover for Hybrid
    Systems"*, CADE-25 (2015), DOI `10.1007/978-3-319-21401-6_36`; Jean-Baptiste
    Jeannin et al., *"Formal Verification of ACAS X, an Industrial Airborne
    Collision Avoidance System"*, TACAS 2015 / *J. ACM* 2017; repository
    `LS-Lab/KeYmaeraX-release`.
  - Guy Katz, Clark Barrett, David L. Dill, Kyle Julian, and Mykel J.
    Kochenderfer, *"Reluplex: An Efficient SMT Solver for Verifying Deep Neural
    Networks"*, CAV 2017, DOI `10.1007/978-3-319-63387-9_5`; `Marabou` (CAV
    2019, `NeuralNetworkVerification/Marabou`).
  - Shai Shalev-Shwartz, Shaked Shammah, and Amnon Shashua, *"On a Formal Model
    of Safe and Scalable Self-Driving Cars"* (`Mobileye RSS`), arXiv
    `1708.06374`; repository `intel/ad-rss-lib`.
  - Hanna Krasowski, Sebastian Scherer, and Matthias Althoff, *"CommonOcean:
    Composable Benchmarks for Motion Planning on Marine Vessels"* / COLREGs MTL
    monitoring (`CommonRoad/commonocean-io`).
  - Ewen Denney and Ganesh Pai, *"Tool Support for Assurance Case Development"*
    (`NASA AdvoCATE`), Automated Software Engineering 25(3), 2018.
- **Domain 10 (Customs Tariffs, Sanctions & Policy-as-Code Compliance):**
  - Joseph W. Cutler, Craig Disselkoen, Aaron Eline, Shaobo He, Kyle Headley,
    Michael Hicks, Kesha Hietala, Eleftherios Ioannidis, John Kastner, Anwar
    Mamat, Darin McAdams, Matt McCutchen, Neha Rungta, Emina Torlak, and Andrew
    Wells, *"Cedar: A New Language for Expressive, Fast, Safe, and Analyzable
    Authorization"*, Proc. ACM Program. Lang. 8 (OOPSLA1 2024), Article 118, DOI
    `10.1145/3649835`; repositories `cedar-policy/cedar` and
    `cedar-policy/cedar-spec`.
  - Jean Yang, Kuat Yessenov, and Armando Solar-Lezama, *"A Language for
    Automatically Enforcing Privacy Policies"* (`Jeeves`), POPL 2012, DOI
    `10.1145/2103656.2103669`.
  - Shayak Sen, Saikat Guha, Anupam Datta, Sriram Rajamani, Janice Tsai, and
    Jeannette M. Wing, *"Bootstrapping Privacy Compliance in Big Data Systems"*
    (`Legalease` / `Grok`), IEEE S&P (Oakland) 2014, DOI `10.1109/SP.2014.28`.
  - David Basin, Felix Klaedtke, Samuel Müller, and Eugen Zălinescu,
    *"Monitoring Metric First-Order Temporal Properties"* (`MonPoly` / `MFOTL`),
    J. ACM 62(2), 2015; repository `eth-sri/monpoly`.
  - `Open Policy Agent` (`open-policy-agent/opa`) and `OpenSanctions`
    (`opensanctions/yente`, `opensanctions/followthemoney`).

### Part II — Historical Verification Failure Postmortem Evidence

All observations in this report were gathered and cross-checked on `2026-10-31`
against the following primary sources:

1. **Anneal Verification Framework and Hardening Corpus (`source` +
   `execution`):**
   - `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`:
     - `trusted/lean/Trusted/Refinement.lean` (`Preorder`, `Partial`,
       `Partial.ub`, `Language`, `SpecOn`, `WellFormedOn`, `Compiles`,
       `Abstracts`, `Compiler.SoundOn`, `Compiler.Verified`,
       `TrustedAssumption`, `TrustPolicy`, `VerificationResultOn` at
       `L207-472`).
     - `trusted/lean/Trusted/StepResult.lean` (`TerminationKind`, `StepResult`,
       `PrefixOutcome.isSafe`, `ExecQuery`, `ExecOut`, `SmallStepMachine`,
       `ReachesPrefix`, `BehaviorOf` at lines 58–199).
     - `trusted/lean/Trusted/MirSemantics.lean` (`AdtInv`,
       `MirVal.satisfiesInv`, `FnKind`, `EnsuresRetLibInv`, `CrateTheorem`).
   - `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`
     (`zerocopy/reference` branch):
     - `support/BehaviorCodecExpressiveness.lean`
       and `support/BehaviorCodecExpressiveness.lean` (`BehaviorCodec`,
       `PartialBehaviorCodec`, `EventualBehaviorOf`, `ProductiveOn`,
       `InhabitedPre`).
     - `support/StructuralExternalCallAndCanaries.lean`
       and `support/StructuralExternalCallAndCanaries.lean`
       (`StepResult.externalCall`, `CallerFramePreserved`,
       `open_world_callback_composition_sound`, `BoundaryCanarySuite`).
     - `support/ProofGatedCompilationAndTrustPolicy.lean`
       and `support/ProofGatedCompilationAndTrustPolicy.lean` (`TCBModel`,
       `ScopedVerificationResult`, positive per-obligation waiver isolation).
     - `support/BehaviorCodecExpressiveness.lean`
       (four-quadrant semantic polarity matrix and negative-polarity vacuity
       prevention).
     - `support/ProofGatedCompilationAndTrustPolicy.lean`
       (whole-crate obligation inventory and single-source `.olean`-bound
       emission).
2. **DeFi Exploits and Smart-Contract Verification (`source` +
   `documentation`):**
   - **Euler Finance:** Governance proposal EIP-14 commit introducing
     `donateToReserves` in `contracts/modules/EToken.sol` without
     `checkLiquidity`; Ethereum Mainnet block `16817996` (`2023-03-13`);
     Omniscia and Certora post-incident analyses of EIP-14 and Euler V2
     invariant verification.
   - **Curve Finance / Vyper Compiler:** GitHub Security Advisory
     `GHSA-5824-cm3x-3c38` (`vyperlang/vyper`, `2023-07-30`, affecting versions
     `0.2.15`, `0.2.16`, `0.3.0`), root-caused to per-function storage-slot
     incrementing in `vyper/semantics/analysis/data_positions.py`
     (`set_reentrancy_key_position`).
   - **Wormhole, Nomad, Beanstalk, Mango Markets, Lendf.Me, ERC-4626:** Wormhole
     Solana bridge exploit (`2022-02-02`, unvalidated `Sysvar: Instructions`
     account in `verify_signatures` via `load_instruction_at`); Nomad
     `Replica.sol` upgrade (`2022-08-01`, `confirmAt[bytes32(0)] = 1` accepting
     unproven messages); Beanstalk Farms governance exploit (`2022-04-17`,
     single-block flash-loan supermajority in `emergencyCommit`); Mango Markets
     oracle manipulation (`2022-10-11`, US DOJ SDNY indictment and conviction of
     Avraham Eisenberg); Lendf.Me ERC-777 `imBTC` `tokensToSend` re-entrancy
     (`2020-04-19`); OpenZeppelin ERC-4626 virtual-shares defense documentation.
   - **Certora, KEVM, and Move Prover / Bytecode Verifier:** Certora Prover
     documentation on `--rule_sanity` (`basic` / `advanced` vacuity detection)
     and external call summaries (`HAVOC_ECF` vs. `HAVOC_ALL`); Aptos/Sui Move
     Bytecode Verifier reference-safety and stack-usage advisories (Zellic /
     OtterSec disclosures, 2022–2023) and Move Prover Boogie shift/borrow
     modeling analyses.
3. **Statutory Tax, Social Benefits, and Accounting Ledgers (`normative` +
   `documentation` + `source`):**
   - **`Mlang` and `Catala`:** Denis Merigoux, Raphaël Monat, and Jonathan
     Protzenko, *"A Modern Compiler for the French Tax Code"*, CC 2021
     (`doi:10.1145/3446804.3446850`); Denis Merigoux, Nicolas Chataing, and
     Jonathan Protzenko, *"Catala: A Programming Language for the Law"*, Proc.
     ACM Program. Lang. 5 (ICFP 2021), Article 77 (`doi:10.1145/3473582`),
     `CatalaLang/catala`.
   - **Australian Robodebt & Section 1073B:** *Report of the Royal Commission
     into the Robodebt Scheme* (Commissioner Catherine Holmes AC SC, July 7,
     2023, ISBN `978-1-921091-92-6`); *Amato v The Commonwealth of Australia*
     (Federal Court of Australia, VID611/2019); Commonwealth Ombudsman reports
     on *Social Security Act 1991 (Cth)* Section 1073B income apportionment
     (2023–2024).
   - **UK Post Office Horizon:** *Bates & Others v Post Office Ltd (No 6:
     Horizon Issues)* `[2019] EWHC 3408 (QB)` (Mr Justice Fraser, December 16,
     2019, including the Technical Appendix detailing `PEAK PC0061213` Callendar
     Square, `PEAK PC0208735` Dalmellington / Branch Outreach, and
     `PEAK PC0203589` Receipts and Payments Mismatch bugs).
   - **US SNAP & Medicaid:** 7 U.S.C. § 2014 / 7 C.F.R. § 273.9 (SNAP income and
     deduction rules); 42 U.S.C. § 1396a(e)(14) and 42 C.F.R. §§ 435.603,
     435.916(f)(1) (`MAGI` vs. `non-MAGI` *ex parte* redetermination mandates).
4. **Voting, Auctions, and Financial Exchanges (`normative` + `documentation` +
   `source`):**
   - **SwissPost / Scytl E-Voting:** Sarah Jamie Lewis, Olivier Pereira, and
     Vanessa Teague, *"Ceci n'est pas une preuve: How not to prove your election
     outcome"* (March 2019); Thomas Haines, Sarah Jamie Lewis, Olivier Pereira,
     and Vanessa Teague, *"How not to prove your election outcome"*, 2020 IEEE
     Symposium on Security and Privacy (S&P), pp. 644–660
     (`doi:10.1109/SP40000.2020.00055`).
   - **Australian Senate STV:** Dirk Pattinson and Mukesh Tiwari, *"Votes as
     Proofs: Modular Formalisation of STV in Coq"* / Rajeev Goré, Dirk
     Pattinson, and Mukesh Tiwari (ITP / IJCAR / E-Vote-ID); *Commonwealth
     Electoral Act 1918 (Cth)* Section 273.
   - **Knight Capital:** U.S. Securities and Exchange Commission, *In the Matter
     of Knight Capital Americas LLC*, Exchange Act Release No. 34-70694, Admin.
     Proc. File No. 3-15570 (October 16, 2013).
   - **VCG and Spectrum Auctions:** Lawrence M. Ausubel and Paul Milgrom, *"The
     Lovely but Lonely Vickrey Auction"*, Chapter 1 in *Combinatorial Auctions*
     (MIT Press, 2006, pp. 17–40); John McMillan, *"Selling Spectrum Rights"*,
     Journal of Economic Perspectives 8(3):145–162 (1994); Makoto Yokoo, Yuko
     Sakurai, and Shigeo Matsubara, *"The Effect of False-Name Bids in
     Combinatorial Auctions: New Fraud in Internet Auctions"*, Games and
     Economic Behavior 46(1):174–188 (2004).
5. **Medical Devices and Aviation Collision Avoidance (`normative` + `source` +
   `documentation`):**
   - **Alaris GP Infusion Pump (`PVS`):** Paolo Masci, Rimvydas Rukšėnas, Paul
     Curzon, and Harold Thimbleby / Patrick Oladimeji et al., formal models of
     the CareFusion Alaris GP volumetric pump in `PVS` and `PVSio-web` (CAV
     2013, FM 2014, SAFECOMP 2015); Harold Thimbleby, *Press On: Principles of
     Interaction Programming* (MIT Press, 2007) and *Fix IT* (Oxford University
     Press, 2021).
   - **Therac-25:** Nancy G. Leveson and Clark S. Turner, *"An Investigation of
     the Therac-25 Accidents"*, IEEE Computer 26(7):18–41 (July 1993,
     `doi:10.1109/MC.1993.274940`).
   - **Überlingen TCAS II & ACAS X (`KeYmaera`):** German Federal Bureau of
     Aircraft Accidents Investigation (BFU), *Investigation Report AX001-1-2/02*
     (May 2004, Überlingen mid-air collision on July 1, 2002); Jean-Baptiste
     Jeannin, Khalil Ghorbal, Yanni Kouskoulas, Ryan Gardner, Aurora Schmidt,
     Erik Zawadzki, and André Platzer, *"A Formally Verified Hybrid System for
     Safe Advisories in the Next-Generation Airborne Collision Avoidance
     System"*, International Journal on Software Tools for Technology Transfer
     (STTT) 19(6):717–741 (2017, `doi:10.1007/s10009-016-0434-1`; earlier
     versions in TACAS 2015 and EMSOFT 2015).

## Revalidation

### Part I — Real-World Tool Survey Revalidation

To revalidate the architectural mappings and Anneal primitive correspondences in
this report after changes to `trusted/lean/` or the hardening corpus:

1. **Verify the four Anneal primitive signatures in `trusted/lean/`:** Inspect
  `trusted/lean/Trusted/Refinement.lean` (`Partial`, `Partial.ub`, `Language`,
  `Language.SpecOn`, `Language.WellFormedOn`, `Compiles`, `Abstracts`,
  `TrustPolicy`, `VerificationResultOn`) and
  `trusted/lean/Trusted/StepResult.lean` (`StepResult`, `PrefixOutcome`,
  `ReachesPrefix`, `BehaviorOf`) at `joshlf/anneal` to confirm that `Partial.ub`
  remains the top element of `Partial B` (`defined := False`) and that
  `Compiles` and `Abstracts` compose by `Preorder.le_trans`.
2. **Rerun the mechanized Lean 4 support developments in the sibling hardening
  packages:** Execute Lean 4 kernel checking
  (`lean -DElab.async=false -Ddebug.skipKernelTC=false`) on:
   - `support/BehaviorCodecExpressiveness.lean`
     (verifying `PartialBehaviorCodec` and `EventualBehaviorOf`),
   - `support/StructuralExternalCallAndCanaries.lean`
     (verifying `StepResult.externalCall` and
     `open_world_callback_composition_sound`), and
   - `support/ProofGatedCompilationAndTrustPolicy.lean`
     (verifying `ScopedVerificationResult` positive per-obligation waiver
     isolation).
3. **Check `Cedar` (`cedar-policy/cedar-spec`) and `Catala`
  (`CatalaLang/catala`) upstream Lean 4 / F* alignment:** When evaluating direct
  Lean 4 integration with external verified DSLs (in particular
  `cedar-policy/cedar-spec`, which is natively mechanized in Lean 4), compare
  `cedar-spec`'s `lean-toolchain` version against `trusted/lean/lean-toolchain`
  (`leanprover/lean4:v4.34.1`) to determine whether `cedar-spec` theorems can be
  imported directly into a `theory/` verification library or bridged via
  `PartialBehaviorCodec`.

### Part II — Historical Verification Failure Postmortem Revalidation

To verify that Anneal's trusted primitives and reference-corpus hardening models
continue to block the four cross-domain failure classes documented in this
report after any modification to `trusted/lean/Trusted/` or `theory/Anneal/`:

1. **Re-verify the mechanized Lean 4 proofs for `BehaviorCodec`,
   `EventualBehaviorOf`, `StepResult.externalCall`, `ScopedVerificationResult`,
   and `BoundaryCanarySuite`:** Run the Lean 4.34.1 kernel checker with
   asynchronous elaboration disabled and kernel type-checking enforced across
   the preserved support modules in the companion Anneal hardening reports on
   `refs/heads/reference`:

   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/BehaviorCodecExpressiveness.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/StructuralExternalCallAndCanaries.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/ProofGatedCompilationAndTrustPolicy.lean
   ```

2. **Check the discriminating theorems corresponding to each historical failure
   archetype:**
   - *Curve/Vyper compiler divergence & Knight Capital loop rejection:* Verify
     that `eventual_wellFormed_iff_prefix_wellFormed` and
     `PartialBehaviorCodec.comp` in `BehaviorCodecExpressiveness.lean` elaborate
     with zero axioms and reject infinite-loop targets (`loopBody`).
   - *Lendf.Me / Balancer callback re-entrancy & Therac-25 actuation-site
     check:* Verify that `canary_reentrant_callback_rejected` and
     `open_world_callback_composition_sound` in
     `StructuralExternalCallAndCanaries.lean` reject mid-call invariant breaches
     (`boundaryInv = false`) while accepting restored-before-call frames.
   - *Certora vacuity, SwissPost/Scytl unchecked setup assumptions & Euler
     per-obligation waivers:* Verify that `contradictory_hTcb_proves_ub_crate`,
     `alwaysUbCrate_unprovable_under_universal_tcb`, and
     `scoped_omission_isolates_buggy_fn` in
     `ProofGatedCompilationAndTrustPolicy.lean` elaborate with zero axioms.
   - *Therac-25 `Class3` wraparound & Move verifier bit-shift/overflow checks:*
     Verify that `currentX86Model_fails_BoundaryCanarySuite` and
     `instBoundaryCanarySuiteFixedX86Model` in
     `StructuralExternalCallAndCanaries.lean` kill all 13/13 target-semantics
     guard mutations.
