# Security, Cryptography, Zero-Knowledge Proofs, Quantitative Resource Bounds, Wire Formats, and FFI Boundaries: Real-World Tools, Historical Failures, and Anneal Refinement Mapping

## Summary

### Part I — Real-World Verification Tools and Refinement Architecture Mapping

Across six high-assurance domains—constant-time and speculative side-channel
verification (Category 6.1), cryptographic primitives and protocol game-hopping
(Category 6.2), zero-knowledge proof circuits and zkVMs (Category 6.3),
worst-case execution time and stack bounds (Category 6.4), verified zero-copy
wire-format parsers (Category 6.5), and cross-language FFI, CHERI hardware
capabilities, and secret zeroization (Category 6.6)—production verification
tools repeatedly confront four structural failure modes that Anneal's four
`trusted/lean/` primitives resolve with a single unified kernel interface:

1. **Soundness–completeness and safety–liveness duality (`Compiles` +
   `ProductiveOn` + `InhabitedPre`):** In zero-knowledge circuits (`Picus`,
   `Coda`, `Garden`, `LAMPE`), under-constrained circuits violate downward
   refinement (`Compiles`), whereas over-constrained circuits satisfy
   `Compiles` vacuously by admitting zero witnesses unless paired with
   `ProductiveOn` and `InhabitedPre`. The same duality governs non-aborting
   cryptographic simulators (`EasyCrypt`, `SSProve`), non-rejecting zero-copy
   parsers (`EverParse`, `Vest`), and feasible WCET/stack configurations
   (`CompCertS`, `Stacking`).
2. **Representation-invariant observable spines (`Language SemObs`,
   `BehaviorCodec`, `obs_decodeOut`, and fail-closed `decodeOut = none`):**
   Whether projecting pair executions to public control-flow and cache leakage
   traces (`CompCert-CT`, `Jasmin`), coupling randomness tapes in game hops
   (`EasyCrypt`, `CertiCrypt`), enforcing non-malleable parser round-trips
   (`EverParse`, `Narcissus`, `Vest`), or verifying dead-store-resistant secret
   erasure (`Secret-Erasure CompCert`, `zeroize`), `BehaviorCodec`'s partial
   bijection laws (`decodeOut_encodeOut`, `encodeOut_of_decodeOut`) and
   fail-closed `decodeOut = none` rule out representation spoofing, non-canonical
   field elements, unaligned pointer casts, and residual secret bytes.
3. **Variable-step dilation and open-world boundary framing
   (`EventualBehaviorOf` and `StepResult.externalCall`):** Cryptographic
   oracles (`EasyCrypt`, `Tamarin`), Fiat-Shamir transcript challenges and zkVM
   precompiles (`RISC Zero`, `SP1`, `Jolt`), FFI transitions (`DimSum`,
   `CompCertO`, `VeriFFI`, `RLBox`), and multi-cycle instruction timing models
   (`AbsInt aiT`, `CerCo`, `Iris` time credits) require variable-step trace
   alignment (`EventualBehaviorOf`) and pre-call invariant enforcement plus
   demonic environment return branching (`StepResult.externalCall boundaryInv
   branches`).
4. **Positive per-obligation assumption tracking (`VerificationResult policy
   waived obligations`):** Cryptographic hardness assumptions (LWE, DDH, ROM),
   FRI/KZG commitment conjectures, hardware microarchitectural timing tables,
   and external SMT/CAS certificates (`SAW`, `CryptoLine`, `Picus`) must be
   recorded as positive per-obligation waivers (`ob.id ∈ waived ∨ ob.prop`)
   rather than negative hypotheses (`hTcb → ...`) so that an idealized
   microarchitectural or computational model cannot discharge unrelated memory
   or arithmetic safety obligations via `False.elim`.

### Part II — Historical Verification Failures, Postmortems, and Architectural Defenses

Across thirty years of high-assurance systems engineering, the most severe
vulnerabilities in verified or heavily audited cryptography, zero-knowledge
proof (ZKP) circuits, hard real-time embedded controllers, and cross-language
wire-format parsers have rarely stemmed from broken mathematical conjectures or
unsound theorem-prover kernels. Instead, they share a recurring structural
anatomy: **semantic gaps at the boundary between an idealized specification
model and a concrete compiler, hardware microarchitecture, witness generator, or
serializer**. Evaluating these historical postmortems against Anneal's four
trusted primitives (`Trusted/Refinement.lean`, `BehaviorCodec` /
`PartialBehaviorCodec`, `Trusted/StepResult.lean`, and `VerificationResultOn` /
`TrustPolicy` / `ScopedVerificationResult`) yields four foundational lessons:

1. **Compiler-induced constant-time violations and microarchitectural escapes
   (`Obs` adequacy and `Compiles` trace preservation):** Mainstream optimizing
   compilers (`Clang`/LLVM, `GCC`, `MSVC`, and `rustc`) validate transformations
   solely against architectural return-value and memory-state refinement,
   routinely rewriting branchless bitwise selection masks
   (`(a & mask) | (b & ~mask)`) into secret-dependent conditional branches or
   spilling secret registers to unzeroized stack slots (Simon, Chisnall, &
   Anderson EuroS&P 2018; Kaufmann et al. CANS 2016; Schneider et al. 2024;
   `curve25519-dalek` / `cmov` CVE-2024-58262). Even when binary control flow
   and memory addresses are secret-independent, variable-latency instructions
   such as `idiv`/`udiv` in `ML-KEM`/Kyber (`KyberSlash1` and `KyberSlash2`,
   Dec 2023) and data-dependent hardware mechanisms such as x86/ARM Dynamic
   Voltage and Frequency Scaling (`Hertzbleed`, CVE-2022-23823) and Apple
   Silicon Data Memory-Dependent Prefetchers (`Augury` 2022; `GoFetch` USENIX
   Security 2024) leak secret keys because the leakage observation alphabet
   `Obs` omitted instruction-operand latency $\lambda(\mathsf{op}, v_1, v_2)$
   or pointer-value cache prefetch side effects. In Anneal, preserving
   constant-time or side-channel noninterference across compilation requires
   instantiating `SmallStepMachine` with an explicit leakage observation type
   `Obs`, proving trace-preserving `Compiles` (which rejects unverified LLVM
   backend rewrites unless mediated by single-source verified codegen), and
   recording unmodeled silicon hazards (DMP, DVFS) as explicit, auditable
   `TrustPolicy` obligations rather than silent model omissions.
2. **Cryptographic carry-propagation and protocol state-machine bugs
   (exhaustive bitvector domain coverage and `StepResult.externalCall`):**
   Multi-limb arithmetic bugs in OpenSSL (`bn_sqr8x_internal` CVE-2014-3570;
   `x86_64-mont5.pl` Montgomery squaring CVE-2015-3193), `libgcrypt`
   (CVE-2017-7526), and curve libraries occur on $2^{-32}$ or $2^{-64}$
   carry-chain boundary inputs that evade random testing and motivated
   `Fiat-Crypto` (Erbsen et al. S&P 2019) and `CryptoLine` (Polyakov et al. CAV
   2018). At the protocol layer, the 17-year-old Needham-Schroeder flaw (Lowe
   1995), TLS `3SHAKE` (Bhargavan et al. 2014), WPA2 `KRACK` (Vanhoef &
   Piessens CCS 2017, CVE-2017-13077), and TLS `Raccoon` (Merget et al. 2020,
   CVE-2020-1968) arose when symbolic models omitted active intruder
   interleaving, session-resumption context binding, retransmission-induced
   nonce resets, or leading-zero timing side channels. In Anneal,
   `PartialBehaviorCodec` enforces canonical multi-limb decoding across 100% of
   `(L.sem s q)` inputs (`WellFormedOn`), while `StepResult.externalCall
   boundaryInv next` enforces call-site state invariants (such as one-time
   nonce monotonicity and key separation) across every re-entrant adversary or
   network callback.
3. **Zero-knowledge proof under-constrained, over-constrained, and Frozen Heart
   bugs (`Compiles` + `ProductiveOn` duality and `PartialBehaviorCodec`):**
   Empirical analysis of 141 SNARK vulnerabilities (Chaliasos et al. USENIX
   Security 2024) across `Circomlib` (`MiMC`, `BabyJubJub`
   `Edwards2Montgomery`, `Num2Bits`/`AliasCheck`), Tornado Cash, Semaphore,
   Aztec 2.0, Polygon zkEVM, Scroll, `RISC Zero`, and `SP1` demonstrates that
   separating imperative witness generation (`<--` or host-oracle hints) from
   polynomial constraints (`===` over $\mathbb{F}_p$) splits correctness into
   two dual failure modes: **under-constrained circuits** (where constraints
   accept bogus witnesses, violating `Compiles`) and **over-constrained
   circuits** (where valid inputs admit zero witnesses, violating
   `ProductiveOn`). In Anneal, pairing `Compiles` ($t \le \pi_c(s)$) with
   `ProductiveOn` ($\forall q,\; \mathsf{pre}\;q \implies \exists h\;o,\;
   \mathsf{val}\;h\;o$) over a `PartialBehaviorCodec` whose `decodeOut` maps
   non-canonical field limbs ($\ge 2^w$ or $\ge p$) to `none` simultaneously
   blocks under-constrained proof forgery and over-constrained completeness
   freezes, while `StepResult.externalCall` blocks Trail of Bits' **Frozen
   Heart** Fiat-Shamir vulnerability by requiring `boundaryInv` to verify that
   all public inputs and prior phase commitments are absorbed into the sponge
   transcript before sampling challenge scalars.
4. **WCET timing anomalies, embedded stack overflows, and parser malleability
   (`EventualBehaviorOf` non-additivity and `encodeOut_of_decodeOut`
   injectivity):** On out-of-order microprocessors, a local L1 cache *hit* can
   trigger a globally *longer* execution time than a cache *miss* due to
   functional-unit contention (Lundqvist & Stenström RTSS 1999), falsifying
   compositional basic-block WCET addition unless pipeline/cache state is
   carried in `State`. In safety-critical firmware, the Toyota ETCS-i
   unintended-acceleration stack overflow (Bookout v. Toyota 2013; Koopman
   2014) and static stack analyzer blind spots (`cargo-call-stack` on indirect
   vtable calls and nested interrupts) show why stack-depth bounds must be
   enforced in target semantics (`X86Semantics.lean`) and audited via
   `ScopedVerificationResult`. Finally, parser differential and malleability
   exploits—Bitcoin DER signature malleability (BIP-62/BIP-66), X.509
   null-prefix attacks (CVE-2009-2408), Android Master Key ZIP differentials
   (CVE-2013-4787 / CVE-2013-8619), and Android `Parcel` deserialization
   mismatches (CVE-2014-7911)—all exploit non-injective parsing where two
   distinct wire byte sequences $b_1 \neq b_2$ decode to the same logical value
   or decode differently across two parsers. Anneal's `PartialBehaviorCodec`
   injectivity law (`encodeOut_of_decodeOut : decodeOut o₂ = some o₁ →
   encodeOut o₁ = o₂`) mathematically enforces canonical, non-malleable wire
   formats and rejects ambiguous encodings (`decodeOut o₂ = none`).

## Applicability

This package unifies the real-world verification tool mapping and the historical verification failure postmortems for this domain against the durable `joshlf/anneal` repository revisions (`24367bd1a8c784f2578535954f9915e24894a56f`, `5fc1139f2208b3c9cfb513573c4a731cc32bb457`, and `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`) and the self-contained Lean 4 (`v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) refinement definitions below.

### Self-Contained Anneal Refinement Primitives (`Language`, `Behavior`, `StepResult`, `VerificationResult`)

To ensure this report is self-contained without depending on unmerged development branches, the core Lean 4 refinement definitions referenced throughout Part I and Part II are given inline below:

```lean
/-- Constructive partial behavior cell representing `B ∪ {UB}`. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Pointwise refinement preorder on `Partial (Out → Prop)`:
`p₁ ≤ p₂` iff every defined specification query `h₂ : p₂.defined` is defined in
`p₁` (`h₁ : p₁.defined`) and every outcome permitted by `p₁` satisfies `p₂`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language (SemObs : Type := Unit) where
  Prog  : Type
  Query : Type
  Out   : Type
  dom   : Prog → Query → Prop := fun _ _ => True
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out

def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Behavior L.Query L.Out :=
  fun q => { defined := pre q, val := fun _ o => post q o }

/-- Non-vacuity witness: at least one query in `dom` satisfies `pre`. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

abbrev InhabitedPre {Query : Type} (pre : Query → Prop) : Prop :=
  ∃ q, pre q

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog` against `(pre, post)`
within `prog`'s own domain `L.dom prog`. -/
def Language.Verified {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn (L.dom prog) pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Partial behavior codec between two languages `L₁` and `L₂` sharing `SemObs`. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  encodeOut : L₁.Out → L₂.Out
  decodeOut : L₂.Out → Option L₁.Out
  decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  encode_of_decode_some : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂
  obs_decodeOut : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- A named proof obligation with a private constructor so proof authors cannot
forge weaker propositions under a trusted obligation identifier. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

abbrev Obligation.assumed {Id : Type} (id : Id) : Obligation Id :=
  ⟨id, False⟩

structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

/-- Positive per-obligation verification gate preventing Principle-of-Explosion
contamination from waived or assumed obligations. -/
def VerificationResult {Id : Type} [DecidableEq Id]
    (policy : TrustPolicy Id) (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

inductive ChoiceKind where
  | demonic
  | angelic

inductive FailureKind where
  | ub
  | fuelExhausted

inductive Terminal (Val : Type) where
  | normal (v : Val)
  | panic
  | abort

/-- Single-step operational outcome for `SmallStepMachine`. -/
inductive StepResult (State Obs Val : Type) where
  | step (next : State) (obs : List Obs := [])
  | choice (kind : ChoiceKind) (branches : State → List Obs → Prop)
  | terminated (term : Terminal Val) (obs : List Obs := [])
  | failed (kind : FailureKind)
  | stuck

/-- Structural external-call boundary guard checking `boundaryInv` at the call
transition before branching demonically over environment return states. -/
def StepResult.externalCall {State Obs Val : Type}
    (boundaryInv : Bool) (branches : State → List Obs → Prop) :
    StepResult State Obs Val :=
  if boundaryInv then .choice .demonic branches else .failed .ub

inductive EventualOut (Obs Val : Type) where
  | terminated (trace : List Obs) (term : Terminal Val)
  | diverges
```

### Part I Applicability — Real-World Verification Tools

This report applies to Anneal's four foundational `trusted/lean/` verification
primitives as mechanized in the `reference` branch corpus at commit
`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` (Specifically within packages
`anneal-behavior-codec-and-progress-refinement-2026`,
`anneal-polar-ctfe-admission-and-semantic-polarity-2026`,
`anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`, and
`anneal-structural-external-calls-and-tcb-mutation-testing-2026`), and compares
their formal expressive power, trusted computing base (TCB) boundaries, and
encoding patterns against 75 real-world verification tools and frameworks across
Categories 6.1 through 6.6.

Relationship among subjects: Anneal's `trusted/lean/` primitives serve as the
target meta-theoretical framework; each external tool family identified in
`REPORT.json` is examined for its upstream problem domain, historical lineage,
verification tradeoffs, formal semantics, TCB boundary, and exact structural
embedding into Anneal's primitives. Claims about upstream tool behavior are
scoped to the cited primary publications and repositories; derived mappings
onto Anneal's primitives are labeled `Basis: derived` and explicitly state the
instantiation of `Language SemObs`, `BehaviorCodec`, `Compiles`/`Abstracts`,
`ProductiveOn`, `EventualBehaviorOf`, `StepResult.externalCall`, and
`VerificationResult`.

### Part II Applicability — Historical Verification Failures and Postmortems

This report synthesizes primary postmortems, CVEs, and academic literature across
security, cryptography, zero-knowledge proof systems, real-time WCET/stack
analysis, and wire-format parsing, and maps their failure modes onto the pinned
Anneal verification architecture identified in `REPORT.json`:

| Subject | Identity / Coordinates | Scope in This Report |
| :--- | :--- | :--- |
| Anneal Core Framework | `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` (`trusted/lean/Trusted/Refinement.lean`, `Trusted/StepResult.lean`, `Trusted/MirSemantics.lean`) | Baseline definitions of `Preorder`, `Partial`, `Behavior`, `Language`, `Compiles`, `Abstracts`, `StepResult`, `ReachesPrefix`, `BehaviorOf`, `TrustPolicy`, and `VerificationResultOn`. |
| Anneal MIR-to-x86-64 Branch | `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457` (`trusted/lean/Trusted/X86Semantics.lean`, `theory/Anneal/Compiler/NaiveCodegen.lean`, `Peephole.lean`) | Target ISA small-step operational model (`X86Machine`), stack-slot bounds, `#DE` division traps (`idiv`/`udiv`), and assembly emission boundary. |
| Anneal Reference Hardening Corpus | `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` (`reports/anneal-*`) | Mechanized hardening primitives: `PartialBehaviorCodec`, `EventualBehaviorOf`, `ProductiveOn`, `StepResult.externalCall`, `ScopedVerificationResult`, `TCBModel`, and `BoundaryCanarySuite`. |
| Constant-Time & Side-Channel Postmortems | EuroS&P 2018; CANS 2016; USENIX Security 2024; `KyberSlash1/2`; `Hertzbleed` (CVE-2022-23823/24436); `Augury`; `GoFetch`; CVE-2024-58262 | Compiler optimization of branchless masks, variable-time division instructions, DVFS frequency throttling, and Apple Silicon DMP pointer-value prefetching. |
| Cryptographic Arithmetic & Protocols | CVE-2014-3570; CVE-2015-3193; CVE-2017-7526; CVE-2017-13077 (`KRACK`); CVE-2020-1968 (`Raccoon`); Lowe (1995); `3SHAKE`; `Fiat-Crypto`; `CryptoLine` | Multi-limb carry propagation bugs on rare inputs and symbolic-vs-computational protocol state-machine and timing vulnerabilities. |
| Zero-Knowledge Proof Postmortems | Chaliasos et al. (USENIX Security 2024); Trail of Bits `Frozen Heart` (2022); `Circomlib`, Tornado Cash, Semaphore, Aztec 2.0, Polygon zkEVM, Scroll, `RISC Zero`, `SP1` | Under-constrained and over-constrained R1CS/Plonkish/AIR circuits, field-aliasing bugs, zkVM guest-host oracle hints, and Fiat-Shamir transcript omissions. |
| WCET, Stack Bounds & Parser Differentials | Lundqvist & Stenström (RTSS 1999); Toyota ETCS-i (2013/2014); `cargo-call-stack`; BIP-62/66; CVE-2009-2408; CVE-2013-4787/8619; CVE-2014-7911 | Out-of-order CPU timing anomalies, RTOS stack overflows, indirect/ISR call-graph gaps, and non-injective ASN.1/ZIP/Parcel parser differentials. |

Separate exact upstream observation from architectural synthesis: the historical
CVEs and papers establish concrete failure mechanisms in their respective C,
Rust, assembly, Circom, and protocol implementations, while the mappings to
Anneal's four `trusted/` primitives are derived structural analyses showing how
Anneal's type and theorem signatures prevent or isolate each class of defect.

## Findings

### Part I — Real-World Verification Tools Mapped to Anneal's Refinement Primitives

### Cross-domain architectural synthesis: Anneal's four trusted primitives

**Basis: source + derived.** Across the Anneal `reference` corpus packages at
`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`, the kernel-checked verification
boundary is factored into four orthogonal primitives:

1. **`Language SemObs` and `Partial` (`Prog`, `Query`, `Out`, `obs : Out →
   SemObs`, `defined` vs. `Partial.ub`):** Every semantic domain `L : Language
   SemObs` assigns to a program `prog : L.Prog` and query `q : L.Query` a
   demonic nondeterministic specification `L.sem prog q : Partial L.Out`,
   comprising a safety bit `defined : Prop` (where `defined = False` is
   `Partial.ub`) and an inhabited outcome predicate `val : defined → L.Out →
   Prop`, equipped with an observable projection `L.obs : L.Out → SemObs`.
2. **`BehaviorCodec L₁ L₂` (including `PartialBehaviorCodec`), `Compiles`, and
   `Abstracts`:** A codec connects two languages sharing `SemObs` via
   `encodeQuery`, `decodeQuery` (`decodeQuery_encodeQuery`), `encodeOut`, and
   `decodeOut : L₂.Out → Option L₁.Out` satisfying `decodeOut_encodeOut`,
   `encodeOut_of_decodeOut`, and `obs_decodeOut` (`decodeOut o₂ = some o₁ →
   L₂.obs o₂ = L₁.obs o₁`). Downward compilation `Compiles L₁ L₂ c s t`
   requires that on every encoded query where source `s` is `defined`, target
   `t` is `defined` and every target outcome `o₂` decodes to `some o₁` (never
   `none`!) satisfying `s`. Upward abstraction `Abstracts L₁ L₂ c v s`
   soundly lifts concrete execution `s` into an abstract verification domain
   `v`.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:** `InhabitedPre pre` and `ProductiveOn pre prog`
   rule out vacuous preconditions and miracle/empty-witness implementations
   (`val h = ∅`). `EventualBehaviorOf` provides fuel-independent trace
   refinement across variable-step compilation passes (`1`-to-`k` instruction
   expansion or loop unrolling) without `Classical.choice` while rejecting
   silent divergence. `StepResult.externalCall boundaryInv branches` enforces a
   pre-call invariant `boundaryInv` at open-world interaction points and
   universally quantifies over demonic environment return `branches`.
4. **Positive per-obligation waiver envelopes (`VerificationResult policy
   waived obligations`):** Every verification obligation `ob` in `obligations`
   must satisfy `ob.id ∈ waived ∨ ob.prop`, and every `id ∈ waived` must be
   permitted by `policy : TrustPolicy`. Because unproved environmental or
   cryptographic assumptions never appear as negative hypotheses (`hTcb →
   ...`), an inconsistent or idealized external assumption cannot collapse the
   proof of unrelated obligations via `False.elim`.

---

### Category 6.1: 2-safety, constant-time, speculative constant-time, and information-flow control (IFC)

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Cryptographic implementations
and high-assurance kernels must satisfy **relational hyperproperties** (in the
sense of Clarkson and Schneider, *Hyperproperties*, JCS 2010), most notably
**2-safety non-interference** and **cryptographic constant-time (CT)**: for any
two executions starting from states $(s_1, s_2)$ that agree on public inputs
($s_1 \equiv_{\text{pub}} s_2$) while differing arbitrarily on secret keys or
plaintexts, the externally observable leakage traces must be identical
($\mathcal{L}(s_1) = \mathcal{L}(s_2)$). In the baseline architectural CT
model, $\mathcal{L}$ records all conditional branch outcomes, memory access
addresses (cache-line or byte granularity), and variable-latency arithmetic
operands (such as hardware division `UDIV`/`IDIV`). Under **Speculative
Constant-Time (SCT)** (Spectre-v1/PHT, Spectre-v4/STL, RSB), $\mathcal{L}$
additionally includes transient microarchitectural fetches and loads triggered
along mispredicted branch or store-bypass paths up to a speculation window $w$.
Target users include cryptographic library authors (`BoringSSL`, `AWS-LC`,
`pq-crystals`, `libcrux`, `Dalek`), compiler engineers preventing C/Rust/LLVM
optimizations from introducing secret-dependent branches (the "compiler-induced
timing gap" documented by Kaufmann et al. and Simon et al., EuroS&P 2018), and
hardware RTL designers preventing cross-domain cache and bus timing leaks.

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`CompCert-CT` (`knothed/CompCert-ct`, Barthe, Blazy, Grégoire, Laporte,
  Oliveira, Pichardie, Poitrenaud, Triqueneaux; CCS 2018 / POPL 2020):**
  Extends Xavier Leroy's Coq-verified `CompCert` C compiler with leakage-aware
  operational semantics across all intermediate languages (`Clight`, `Cminor`,
  `RTL`, `LTL`, `Linear`, `Mach`, assembly) and proves that compilation
  preserves constant-time non-interference from source to machine code.
- **`Jasmin` (`jasmin-lang/jasmin`, Almeida, Barbosa, Barthe, Blot, Grégoire,
  Laporte, Oliveira, Pacheco, Schmidt, Strub; CCS 2017 / POPL 2020 / CCS
  2021):** A Coq-verified compiler for an assembly-like structured language
  ("assembly in the head of the programmer") targeting x86-64/AVX2 and ARMv7/v8.
  Provides built-in static and relational verification for memory safety,
  constant-time (`jasminc -checkCT`), and speculative constant-time (`jasminc
  -checkSCT` / selective speculative load hardening `SLH`), with direct
  extraction to `EasyCrypt`.
- **`FaCT` (`PLSysSec/FaCT`, Cauligi, Soeller, Johannesmeyer, Brown, Wahby,
  Jero, Sherwood, Jhala, Stefan, Ristenpart; PLDI 2019):** A Rust-like domain
  specific language and secrecy-typed compiler (`public` vs. `secret` type
  qualifiers) that automatically transforms secret-dependent conditionals and
  array accesses into constant-time bitwise/cmov idioms and lowers to LLVM IR.
- **`ct-verif` (`imdea-software/verifying-constant-time`, Almeida, Barbosa,
  Barthe, Dupressoir, Emmi; USENIX Security 2016):** Verifies constant-time C
  code compiled to LLVM IR by constructing a **self-composition product
  program** in `SMACK`/`Boogie` and discharging 2-safety assertions with `Z3`.
- **`Binsec/Rel` and `Binsec/Haunted` (`binsec/Rel`, Daniel, Bardin, Rezk; IEEE
  S&P 2020 and CAV 2021):** Binary-level Relational Symbolic Execution (RelSE)
  on x86/ARM/RISC-V executables lifted to DBA IR. `Binsec/Rel` shares symbolic
  expressions across the paired runs when public values coincide ("on-the-fly
  relational state sharing"), while `Binsec/Haunted` extends RelSE to
  speculative constant-time by simultaneously tracking architectural and
  transient "ghost" executions in a single symbolic pass without unrolling a
  separate speculation tree per branch.
- **`Blade` (Vassena, Disselkoen, von Gleissenthall, Cauligi, Kıcı, Jhala,
  Tullsen, Stefan; POPL 2021):** A static flow-sensitive type system and
  automatic repair algorithm implemented in the `Cranelift` WebAssembly
  compiler (`PLSysSec`) that constructs a transient def-use graph from
  speculative loads ("sources") to address-dependent memory operations
  ("sinks") and computes a minimal cut to insert speculative protection
  primitives (`protect` via masks/cmov rather than full `lfence` serialization).
- **`Spectector` (`spectector/spectector`, Guarnieri, Köpf, Morales, Reineke,
  Sánchez; IEEE S&P 2020):** Formalizes **Speculative Non-Interference (SNI)**—
  requiring that a program leaks no more under speculative semantics than under
  standard sequential semantics—and verifies x86 assembly via symbolic
  execution in CIAO Prolog + `Z3`.
- **`Pitchfork` (`PLSysSec/haybale-pitchfork`, Cauligi et al., PLSysSec 2020):**
  A Rust symbolic execution engine built on `haybale` (LLVM bitcode symbolic
  executor using `boolector`) that verifies constant-time execution of Rust and
  C cryptographic crates (`ring`, `subtle`, `libsodium`) and pinpoints exact
  source lines where secret taint reaches a branch condition or memory index.
- **`CacheAudit` (`cacheaudit/cacheaudit`, Doychev, Feld, Köpf, Mauborgne,
  Reineke; CCS 2013 / TISSEC 2015):** Static abstract-interpretation analyzer
  for x86 binaries that computes quantitative upper bounds on cache side-channel
  leakage (in bits of Shannon/min-entropy over LRU/FIFO/PLRU cache state, time,
  or trace observations).
- **`Constantine` (Borrello, Querzoni, Giuffrida; CCS 2021) and `SC-Eliminator`
  (Wu, Guo, Schaumont, Wang; ISSTA 2018):** LLVM compiler passes that eliminate
  secret-dependent control flow and data-cache accesses via control-flow
  linearization (predicated execution) and oblivious scatter-gather memory
  preloading.
- **`Cartesian Hoare Logic (CHL)` / `Descartes` (Sousa and Dillig, PLDI 2016),
  `Blazer` (Antonopoulos et al., CCS 2017), and `Themis` (Chen, Feng, Dillig;
  CCS 2017):** Program logics and automated verifiers for $k$-safety
  hyperproperties in Java/bytecode, using product-program trace alignment and
  decomposition into loop-free partitions to detect algorithmic timing
  side-channels.
- **`SecVerilog` (Zhang, Wang, Suh, Myers; ASPLOS 2015), `Silver` (Kopf et al.),
  and `Iodine` (Gleissenthall, Gökhan Kıcı, Stefan, Jhala; CCS 2019):**
  Hardware-level information-flow and constant-time verifiers for Verilog RTL;
  `SecVerilog` uses dependent security labels on wires/registers, while `Iodine`
  checks pipeline-aware constant-time execution of hardware designs without
  manual label annotations using relational clock-aligned invariants.
- **`Jif` (Myers et al., Cornell), `FlowCaml` (Simonet and Pottier, ICFP 2002),
  and `LIO` (Stefan, Russo, Mitchell, Mazières; Haskell Symposium 2011):**
  Foundational language-based Information-Flow Control (IFC) systems enforcing
  termination-insensitive or termination-sensitive non-interference via static
  security lattices (`Jif`, `FlowCaml`) or monadic floating-label runtime checks
  (`LIO`).

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.** Tools in Category 6.1 divide along three
architectural axes:

- **Source/IR level vs. binary/compiler preservation:** Source- and LLVM-level
  tools (`ct-verif`, `Pitchfork`, `FaCT`, `Constantine`, `Blazer`, `Themis`)
  benefit from structured loops and rich type/pointer provenance, making
  product construction fast, but they remain vulnerable to downstream LLVM back-
  end passes (`SimplifyCFG`, `SelectOptimize`, register spilling) that rewrite
  constant-time `select`/bitwise masks back into conditional branches (as shown
  by `Binsec/Rel` and Kaufmann et al.). Conversely, binary-level analyzers
  (`Binsec/Rel`, `Spectector`, `CacheAudit`) verify actual machine instructions
  with zero compiler trust, at the cost of bounded loop unrolling or difficult
  alias recovery. `CompCert-CT` and `Jasmin` bridge both worlds by verifying
  compilation preservation in Coq.
- **2-Safety Self-Composition vs. Type Systems vs. Abstract Interpretation:**
  Security type systems (`FaCT`, `Blade`, `SecVerilog`, `Jif`, `FlowCaml`) are
  compositional and run in milliseconds, but over-approximate value-dependent
  invariants (rejecting benign branches on public bounds or masked secrets
  unless explicit declassification is used). Relational symbolic execution and
  product programs (`ct-verif`, `Binsec/Rel`, `Jasmin -checkCT`, `CHL`,
  `Iodine`) are path- and value-precise (allowing branches on expressions that
  provably evaluate identically in both runs), while `CacheAudit` trades relational
  2-safety for quantitative single-run abstract domain counting (`#outputs`).
- **Architectural CT vs. Speculative CT (SCT):** Architectural CT (`ct-verif`,
  `CompCert-CT`, `Pitchfork`, `FaCT`) assumes sequential ISA semantics. Under
  Spectre-v1/v4, a bounds check `if (i < len) { y = arr2[arr1[i] * 64]; }` is
  architecturally constant-time when `i` and `len` are public, yet leaks secret
  memory `arr1[i]` when mispredicted! `Spectector`, `Blade`, `Binsec/Haunted`,
  and `Jasmin -checkSCT` extend the operational semantics with microarchitectural
  prophecy/oracle directives (`Step_spec`), revealing whether fences (`lfence`)
  or dataflow masking (`SLH` / `protect`) are required.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`CompCert-CT`:** Mechanized in Coq. Every transition $S \xrightarrow{e, l}
  S'$ emits both external I/O events $e$ and a micro-leakage event $l \in
  \text{Leakage}$ (branch boolean, memory address). Compiler passes are proved
  using **leakage-preserving backward/forward simulations** where stack block
  allocations are related by a public-offset-preserving memory injection $j :
  \text{block} \to \text{Option}(\text{block} \times \mathbb{Z})$. TCB: Coq
  kernel, source/target leakage semantics, and assembly printer.
- **`Jasmin`:** Core language and x86-64/ARM compiler verified in Coq;
  `-checkCT` and `-checkSCT` rely on an OCaml abstract analyzer or reduction to
  `EasyCrypt` relational Hoare logic (`pRHL`).
- **`ct-verif`, `Binsec/Rel`, `Spectector`, `Pitchfork`, `Blade`:** Unverified
  analyzers (OCaml/Rust/Prolog) discharging verification conditions via external
  SMT solvers (`Z3`, `Bitwuzla`, `Boolector`) without proof-certificate replay
  in a proof kernel.

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.** Anneal's four primitives express 2-safety constant-time,
speculative non-interference, and quantitative cache bounds without adding any
new axiom to `trusted/lean/`:

1. **`Language SemObs` & `Partial` (Synchronized Product Language
   `L_ct2`):**
   - For any base language `L` (such as `MirSemantics` or `X86Semantics`) with
     step-level leakage trace $\vec{\ell} \in \text{List LeakEvent}$ (branch
     targets, effective load/store addresses, division operands, and under SCT,
     transient speculative load addresses), construct the **paired 2-safety
     language `L_ct2`** in `theory/`:
     - `Prog := L.Prog`
     - `Query := { (q₁, q₂) : L.Query × L.Query // PubEq q₁ q₂ }` (two inputs
       agreeing on all public parameters and public memory regions, while secret
       regions vary freely).
     - `Out := { (o₁, o₂) : L.Out × L.Out // LeakageTrace o₁ = LeakageTrace o₂ }`
     - `SemObs`: Public output projection paired with the shared leakage trace
       `(PubObs o₁, LeakageTrace o₁)`.
     - `defined` vs. `Partial.ub`: `(L_ct2.sem prog ⟨q₁, q₂⟩).defined` holds iff
       both runs `L.sem prog q₁` and `L.sem prog q₂` are `defined` (memory-safe)
       **and** for all outcomes $o_1$ of $q_1$ and $o_2$ of $q_2$,
       $\text{LeakageTrace}(o_1) = \text{LeakageTrace}(o_2)$! Any secret-dependent
       branch, secret-dependent cache/memory address, or speculative transient
       load discrepancy sets `defined = False` (`Partial.ub`).
2. **`BehaviorCodec L₁ L₂`, `Compiles`, and `Abstracts`:**
   - **Leakage-Preserving Compilation (`CompCert-CT` / `Jasmin`):** In
     `Compiles L_mir_ct2 L_x86_ct2 codec s t`, `SemObs` includes the public
     leakage trace (or public stack-offset bijection via `codec`).
     `obs_decodeOut` guarantees that the compiled x86-64 binary's branch and
     memory-access trace matches the source MIR's certified constant-time
     leakage spine (`L_x86_ct2.obs o₂ = L_mir_ct2.obs o₁`). If an LLVM-style
     backend optimization rewrites a branchless `cmov`/`select` into a
     secret-dependent jump `jne`, the two paired x86-64 runs diverge in
     `LeakageTrace`, yielding `decodeOut o₂ = none` (or `defined = False`),
     which falsifies `Compiles`!
   - **Type-Based / Taint Abstraction (`FaCT`, `Blade`, `SecVerilog`,
     `CacheAudit`):** `Abstracts L_secType L_mir_ct2 codec v s` lifts paired
     concrete executions `s` into a single-pass security-lattice abstract
     interpreter `v` (tracking `Public` vs. `Secret` labels and `Transient`
     speculative taint, or `CacheAudit` abstract cache sets). Proving
     `Abstracts` once in `theory/` allows fast linear-time type/taint checking
     on `v` to discharge `defined` on `L_mir_ct2`.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **`ProductiveOn` & `InhabitedPre`:** Prevents a constant-time transformation
     (`FaCT` / `Blade` / `SC-Eliminator`) from "eliminating leakage" by trapping
     all secret inputs in an unreachable precondition (`pre = ∅`) or aborting
     the execution (`val = ∅`).
   - **`EventualBehaviorOf`:** Crucial for **instruction-level constant-time
     dilation**: when a single MIR bitwise select expands to a 3-instruction
     constant-time mask sequence in x86-64 (`neg`, `and`, `xor`), both paired
     runs expand by the *exact same* deterministic step count $k$, so
     `EventualBehaviorOf` on `L_ct2` preserves lockstep timing equivalence
     across variable-length lowering passes.
   - **`StepResult.externalCall boundaryInv branches`:** Models **speculative
     execution oracles (`Spectector`/`Binsec/Haunted`)** and **cross-module calls**:
     at a call boundary or speculative barrier, `boundaryInv` asserts that all
     transient speculative registers are masked (`SLH` predicate register is
     architecturally synced) and no secret value resides in public caller-saved
     registers before yielding to `branches`.
4. **`VerificationResult` and `TrustPolicy`:**
   - Hardware constant-time guarantees depend on explicit **microarchitectural
     leakage assumptions** (e.g., `X86Mul64ConstantLatency`,
     `NoDataDependentOverclocking_DMP`, `SpectreV1WindowBounded_250`,
     `CacheLineGranularity_64B`). Representing each hardware leakage assumption
     as a positive obligation ID in `VerificationResult` (`ob.id ∈ waived ∨
     ob.prop`) audited by `TrustPolicy` makes the exact hardware leakage model
     explicit—so moving a crate from a desktop CPU to an embedded Cortex-M0+
     with variable-time 32-bit `MULS` simply rejects the `X86Mul64ConstantLatency`
     waiver in `TrustPolicy` without invalidating the mathematical proofs.

---

### Category 6.2: Cryptographic primitives, BigInt arithmetic, and protocol game-hopping

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Cryptographic engineering spans
two tightly coupled verification layers:

1. **Mathematical and side-channel correctness of low-level primitives:**
   Multi-precision modular arithmetic over prime fields $\mathbb{F}_p$ (such as
   Curve25519 $\mathbb{F}_{2^{255}-19}$, NIST P-256, secp256k1, BLS12-381) and
   polynomial rings $\mathbb{Z}_q[X]/(X^n + 1)$ (ML-KEM/Kyber, ML-DSA/Dilithium)
   relies on unsaturated radix-$2^{51}$ or Montgomery radix-$2^{64}$ limbs,
   delayed carry propagation, Barrett/Montgomery reductions, and Number-Theoretic
   Transforms (NTT). A single missed carry bit (such as CVE-2014-3570 in OpenSSL
   `BN_sqr`, firing with probability $2^{-64}$, or CVE-2017-5754 / P-256 carry
   bugs) enables private-key recovery via invalid-curve or fault attacks.
2. **Computational and symbolic security of cryptographic protocols:**
   Multi-party and network protocols (TLS 1.3, Signal Double Ratchet, Messaging
   Layer Security RFC 9420, WireGuard, SSH, AWS KMS) must preserve secrecy,
   forward secrecy, post-compromise security, and authentication against active
   adversaries. Proofs proceed either in the **computational model** (Bellare–
   Rogaway game-hopping or Canetti's Universal Composability [UC], bounding an
   adversary's distinguishing advantage $\text{Adv}(\mathcal{A}) \le \sum_i
   \epsilon_i(\lambda)$ via reductions to DDH, LWE, orPRF/ROM assumptions) or
   in the **symbolic Dolev–Yao model** (unbounded sessions over ideal term
   algebras with equational theories).

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`Fiat-Crypto` (`mit-plv/fiat-crypto`, Erbsen, Philipoom, Gross, Sloan,
  Chlipala; IEEE S&P 2019):** A Coq library and certifying compiler pipeline
  that synthesizes straight-line, constant-time finite-field arithmetic in C,
  Rust, Go, Java, and Bedrock2 from high-level associative/distributive ring
  specifications, using abstract interpretation over limb range intervals to
  prove absence of integer overflow during delayed carry chains. Deployed in
  BoringSSL, Chrome, Android, Firefox (`nss`), WireGuard, and the Linux kernel.
- **`HACL*` and `EverCrypt` (`project-everest/hacl-star`, Zinzindohoué,
  Bhargavan, Protzenko, Beurdouche; CCS 2017 and Protzenko et al.; IEEE S&P
  2020):** Part of Project Everest (Inria / Microsoft Research / CMU). `HACL*`
  writes cryptographic primitives in `Low*` (a shallow embedding of C inside
  dependently typed `F*`), verifies memory safety, secret independence, and
  functional equivalence to pure mathematical RFC specs using `Z3`, and extracts
  readable C via `KaRaMeL` (`KreMLin`). `EverCrypt` unifies `HACL*` C code with
  `Vale` assembly under a single agile multiplexing API with CPU feature
  auto-detection (`AVX2`, `AVX-512`, `NEON`).
- **`Vale` (Bond, Hawblitzel, Kapritsos, Leino, Lorch, Parno, Rane, Setty,
  Thompson; USENIX Security 2017):** A verification framework for high-speed
  assembly language (AES-GCM, SHA-256, Poly1305, Curve25519 in x86-64/ARM)
  that generates verification conditions in `Dafny` and `F*` from annotated
  assembly procedures.
- **`Libjade` (`formosa-crypto/libjade`, Barbosa et al., Formosa Crypto):** A
  formally verified C-callable cryptographic library written in `Jasmin` and
  verified with `EasyCrypt` for functional correctness, ABI compliance, and
  constant-time/speculative-constant-time security (including X25519, ChaCha20-
  Poly1305, SHA-3, ML-KEM/Kyber, and ML-DSA/Dilithium).
- **`Cryptol` (`GaloisInc/cryptol`) and `SAW` (`GaloisInc/saw-script`, Dockins,
  Foltz, Tomb et al., CAV 2016; AWS `s2n` / `AWS-LC` verification, USENIX
  Security 2020 / CAV 2021):** `Cryptol` is Galois's domain-specific functional
  language for bit-precise cryptographic specifications. The Software Analysis
  Workbench (`SAW`) symbolically executes LLVM bitcode, x86-64 machine code,
  JVM bytecode, and `Cryptol` models into shared `SAWCore` terms and proves
  equivalence via AIG bit-blasting (`ABC`), SAT, and SMT (`Z3`/`Yices`), with
  HOL-style term-rewriting tactics for compositional sub-proofs.
- **`CryptoLine` (`fmlab-iis/cryptoline`, Tsai, Bowditch, Wang, et al.; CCS 2014
  / CCS 2019 / CAV):** Specialized verifier for low-level multi-limb assembly
  arithmetic (`OpenSSL`, `BoringSSL`, `pqm4` NTT) that splits verification into
  two orthogonal conditions: **algebraic polynomial equations** (discharged by
  Computer Algebra Systems `Singular`/`Macaulay2` via Gröbner bases) and
  **bitvector range/carry-overflow constraints** (discharged by `Boolector` /
  `Bitwuzla`).
- **`EasyCrypt` (`easycrypt/easycrypt`, Barthe, Grégoire, Heraud, Béguelin;
  CRYPTO 2011 / CCS 2011):** The flagship interactive proof assistant for
  code-based game-playing cryptographic proofs, combining an ambient higher-
  order logic with a **Probabilistic Relational Hoare Logic (`pRHL`)** over
  imperative `pWhile` programs and a quantitative Hoare logic for bounding
  failure event probabilities ($\Pr[G : E]$).
- **`CryptoVerif` (Blanchet; IEEE S&P 2006 / 2008):** An automatic and
  semi-automatic protocol verifier in the **computational model** that
  represents games in a probabilistic process calculus and applies pre-proved
  cryptographic game transformations (IND-CPA, INT-CTXT, ROM, CDH/GDH) to bound
  distinguishing advantage and extract OCaml/F* implementations.
- **`SSProve` (`SSProve/ssprove`, Abate, Haselwarter, Rivas, Van Muylder,
  Winterhalter, Hriţcu, Maillard, Spitters; CSF 2021), `FCF` (Petcher and
  Morrisett, POST 2015), and `CertiCrypt` (Barthe, Grégoire, Zanella Béguelin;
  POPL 2009):** Foundational Coq mechanizations of computational cryptography.
  `CertiCrypt` and `FCF` embed probabilistic games and couplings in Coq;
  `SSProve` formalizes **State-Separating Proofs** (Brzuska et al., ASIACRYPT
  2018) inside Coq's relational `pRHL` (`Relational` / `Monadic` effect
  systems), enabling modular algebraic composition of game packages.
- **`CryptHOL` (Basin, Lochbihler, Sefidgar; Journal of Cryptology 2020):** A
  foundational framework in `Isabelle/HOL` for game-based cryptographic proofs
  using generative probabilistic monads (`GPV`) and Lifting/Transfer packages.
- **`Owl` (`secure-foundations/owl`, Gancher, Gibson, Singh, Dharanikota, Parno;
  IEEE S&P 2023):** A compositional verification framework for cryptographic
  protocols that encodes computational security properties (IND-CCA, PRF, MAC,
  Diffie-Hellman) into an **information-flow and refinement type system** checkable
  by SMT (`Z3`), paired with the `OwlC` compiler that extracts verified,
  constant-time Rust code (`WireGuard`, `HPKE`, `TLS 1.3`).
- **`Tamarin Prover` (`tamarin-prover/tamarin-prover`, Meier, Schmidt, Cremers,
  Basin; CAV 2013):** Symbolic protocol verifier based on **multiset rewriting
  rules**, equational theories (Diffie-Hellman, bilinear pairings, XOR), and
  guarded first-order temporal trace properties, supporting both automated
  backward constraint solving and interactive proof guidance (used to standardize
  TLS 1.3, 5G-AKA, EMV, and Apple iMessage PQ3).
- **`ProVerif` (Blanchet; CSFW 2001 / IEEE S&P 2016) and `DeepSec` (Cheval,
  Kremer, Rakotonirina; IEEE S&P 2018):** Symbolic applied pi-calculus
  verifiers; `ProVerif` translates protocols into Horn clauses for unbounded-
  session secrecy, correspondence, and observational equivalence, while
  `DeepSec` decides exact trace equivalence for bounded-session protocols via
  constraint-solving decision trees.
- **`Squirrel Prover` (`squirrel-prover/squirrel-prover`, Baelde, Delaune,
  Jacomme, Koutsos, Moreau; CCS 2021):** An interactive first-order logic proof
  assistant for cryptographic protocols with **computational soundness**
  (Computationally Complete Symbolic Attacker `CCSA` logic), reasoning directly
  about unbounded sessions and mutable state without explicit probability
  calculations.
- **`DY*` (Bhargavan, Bichhawat, Do, Hosseyni, Küsters, Schmitz, Würtele;
  EuroS&P 2021) and `MLS*` (Bhargavan, Beurdouche, Naldurg et al., CCS 2023):**
  A modular symbolic Dolev–Yao verification framework embedded directly inside
  `F*` using a global trace invariant over timestamped protocol events, enabling
  verification of executable `F*`/Rust protocol code (such as the TreeKEM group
  key agreement in RFC 9420 `MLS*`).
- **`Libcrux` (`cryspen/libcrux`, Cryspen / AWS) and `hax` (`hacspec/hax`,
  Bhargavan, Buyse, Hospes, Protzenko, et al.):** `hax` is a Rust compiler
  frontend that translates safe Rust AST/THIR into multiple verification
  backends (`F*`, `Coq`, `ProVerif`, `EasyCrypt`, and `Lean`), powering
  `Libcrux`'s formally verified Rust implementations of ML-KEM (FIPS 203),
  ML-DSA (FIPS 204), X25519, and SHA-3 deployed in Firefox, NSS, and Rosenpass.

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Correct-by-construction synthesis (`Fiat-Crypto`) vs. post-hoc verification
  (`SAW`, `CryptoLine`, `Vale`, `hax`):** `Fiat-Crypto` achieves complete
  proof-kernel foundational assurance (Coq) with zero manual per-prime proof
  effort by parameterizing the compiler over the prime $p$ and limb layout,
  whereas `SAW` and `CryptoLine` verify existing hand-written assembly (`AWS-LC`,
  `OpenSSL`) automatically using external SAT/SMT/CAS solvers. `HACL*`,
  `Libjade`, and `Libcrux`/`hax` occupy the middle ground: developers write code
  in a structured subset (`Low*`, `Jasmin`, or safe Rust) and prove functional
  refinement interactively (`F*`, `EasyCrypt`).
- **Foundational game-hopping (`SSProve`, `CertiCrypt`, `CryptHOL`) vs.
  standalone relational logics (`EasyCrypt`, `CryptoVerif`) vs. Type-Based
  Computational Security (`Owl`):** `EasyCrypt` provides rapid proof iteration
  for game hops via SMT-discharged `pRHL` rules, while `SSProve` and `CryptHOL`
  reduce the TCB to the Coq/Isabelle kernel via monadic state-separating
  packages. However, game-hopping across a 20-message protocol can require
  dozens of manual intermediate games; `Owl` eliminates explicit intermediate
  games by baking IND-CPA/PRF/DH hybrid reductions into typing rules, trading
  arbitrary reduction expressiveness for 10x smaller proof scripts and direct
  Rust extraction.
- **Symbolic Dolev–Yao (`Tamarin`, `ProVerif`, `DY*`) vs. Computational
  (`EasyCrypt`, `CryptoVerif`, `Squirrel`):** `Tamarin` and `ProVerif` excel at
  finding intricate multi-session state-machine and key-compromise-impersonation
  (KCI) attacks automatically, but treat cryptographic primitives as black-box
  function symbols (ignoring length leaks, modular arithmetic malleability, or
  nonce-reuse probability bounds). `Squirrel` and `Owl` bridge symbolic
  ergonomics with computational soundness.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`Fiat-Crypto`, `SSProve`, `CertiCrypt`, `FCF`, `CryptHOL`:** Foundational
  kernel checking inside Coq or Isabelle/HOL.
- **`HACL*`, `EverCrypt`, `Vale`, `DY*`, `MLS*`, `Owl`:** Rely on the `F*` type
  checker (or `Owl` type checker), the `Z3` SMT solver without proof-certificate
  reconstruction, and the `KaRaMeL` / `OwlC` C/Rust extraction pipeline.
- **`SAW` and `CryptoLine`:** Rely on the unverified `SAWCore` symbolic
  simulator, `ABC` AIG equivalence checker, `Z3`/`Yices`/`Boolector`, and
  `Singular` Gröbner-basis engine (though `CryptoLine` supports optional Coq
  certificate checking for algebraic polynomial identities).

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.**

1. **`Language SemObs` & `Partial`:**
   - **Primitive Arithmetic (`Fiat-Crypto`, `HACL*`, `CryptoLine`, `SAW`):**
     Source `L_field` has `Prog := FieldSpec p`, `Query := Inputs (ZMod p)`,
     `Out := ZMod p`, `SemObs := ZMod p`. Target `L_mir` / `L_x86` has `Out :=
     LimbArray × LeakTrace`. `Partial.ub` (`defined = False`) captures **limb
     carry overflow**, **non-canonical Montgomery output**, or **secret-dependent
     timing leak**.
   - **Protocol Game-Hopping (`EasyCrypt`, `SSProve`, `Owl`, `Tamarin`):**
     Each game $G_i$ is a `Prog` in `L_game`. `Query` is an adversary oracle
     schedule and initial randomness tape $\rho \in \{0,1\}^\lambda$. `Out` is
     the full protocol state + randomness + transcript; `SemObs` (`obs`) is the
     adversary's view and authorized leakage trace $\langle \text{Transcript},
     \text{Leakage} \rangle$. `Partial.ub` (`defined = False`) models **bad
     cryptographic events** (AEAD nonce reuse, decrypting unauthenticated
     ciphertext, or signing-oracle forgery on a target message).
2. **`BehaviorCodec L₁ L₂`, `Compiles`, and `Abstracts`:**
   - **Multi-Limb Representation Refinement (`Fiat-Crypto` / `Libcrux`):**
     `BehaviorCodec` maps abstract field elements $x \in \mathbb{F}_p$ to
     canonical multi-limb vectors $\vec{u} \in (\text{UInt64})^k$. Crucially,
     `decodeOut : LimbVector → Option (ZMod p)` checks that the output limbs
     satisfy the canonical representation invariant (e.g., for Curve25519
     `fe_tobytes`, that $2^{255}-19 \le v < 2^{255}$ has been fully reduced so
     $\sum u_i 2^{w_i} < p$); any unreduced or overflowing limb vector decodes
     to `none`, causing `Compiles` to fail closed!
   - **Bijective Randomness Coupling in Game Hops (`EasyCrypt` / `SSProve`):**
     In an information-theoretic bridging hop $G_i \to G_{i+1}$ (such as
     one-time-pad masking $r \mapsto r \oplus m$ or lazy random-oracle
     permutation), `encodeOut` and `decodeOut` define the **randomness-tape
     bijection**. Anneal's partial bijection laws (`decodeOut_encodeOut` and
     `encodeOut_of_decodeOut`) structurally verify in the Lean kernel that the
     randomness coupling is injective and measure-preserving on uniform finite
     tapes, while `obs_decodeOut` guarantees that the adversary's observable
     view is identical across the hop!
   - **Algebraic + Range Splitting (`CryptoLine` / `SAW`):** `Abstracts L_polybv
     L_x86 codec v s` lifts machine instructions into polynomial ring +
     bitvector range constraints `v` discharged in `theory/`.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **`ProductiveOn` & `InhabitedPre`:** Prevents a protocol simulator `Sim` in
     UC (`SSProve`) from trivially preventing forgery by aborting/blocking all
     honest session transcripts (`val = ∅`).
   - **`StepResult.externalCall boundaryInv branches`:** Directly models
     **adversary oracle queries (`O_Sign`, `O_Dec`, `O_RO`, `O_Corrupt`)** in
     game-hopping and symbolic protocols: before yielding to the adversary,
     `boundaryInv` verifies state-separation invariants (e.g., ephemeral secret
     sponges are zeroized, nonce counters are strictly monotone, and challenge
     keys are isolated), and `branches` quantifies over all possible adversary
     return messages.
4. **`VerificationResult` and `TrustPolicy`:**
   - Information-theoretic hops and field-arithmetic carries are proved
     constructively (`ob.prop`), while **computational hardness assumptions**
     (such as `MLWE_768_Indistinguishable`, `DDH_Curve25519`,
     `SHA3_RandomOracleModel`) and **external solver certificates** (`SAW_ABC`,
     `Singular_Groebner`) are isolated as typed obligation IDs in `VerificationResult`
     governed by `TrustPolicy`. If a computational assumption is weakened, the
     audit report identifies the exact hops that rely on `ob.id ∈ waived`
     without risking `False.elim` across the pure arithmetic proofs.

---

### Category 6.3: Zero-knowledge proof systems (R1CS, Plonkish, AIR, and zkVMs)

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Zero-knowledge proof compilers
(`Circom`, `Halo2`, `Plonky2`/`Plonky3`, `Noir`, `Gnark`, `Cairo`, `Leo`,
`Arkworks`) and general-purpose RISC-V zkVMs (`RISC Zero`, `SP1`, `Jolt`,
`OpenVM`, `Valida`) split computation into two distinct artifacts: an
**off-circuit witness generator** $W(x, w_{\text{priv}}) \to \vec{z} \in
\mathbb{F}_p^m$ (written in imperative Rust, C++, or Wasm) and an **in-circuit
polynomial constraint system** $\mathcal{C}(\vec{z}) = 0$ over a prime field
$\mathbb{F}_p$ (R1CS rank-1 constraints $(A\vec{z}) \circ (B\vec{z}) = C\vec{z}$,
Plonkish custom gates + `Plookup`/`LogUp` lookup arguments, or STARK Algebraic
Intermediate Representations [AIR] over execution trace tables).

As documented in comprehensive ZK vulnerability studies (Chaliasos et al.,
*SoK: What don't we know? Understanding Security Vulnerabilities in SNARKs*,
USENIX Security 2024; Pailoor et al., PLDI 2023), **over 90% of critical circuit
vulnerabilities are under-constrained bugs** (where $W$ computes the intended
value via `<--`, but $\mathcal{C}$ omits an `===` constraint, bit-length range
check, or zero-divisor check, allowing a malicious prover to supply a bogus
witness $\vec{z}' \neq W(x, w_{\text{priv}})$ that satisfies $\mathcal{C}(\vec{z}')
= 0$ and forges a proof for a false public output). The dual vulnerability is
**over-constrained circuits** (completeness bugs), where $\mathcal{C}$ rejects
valid witnesses on edge-case inputs, causing honest rollup provers to deadlock.

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`Picus` (`Veridise/Picus`, formerly `QED^2`, Pailoor, Chen, Wang, Rodríguez,
  Geffen, Morton, Chu, Guarnieri, Pettai, Dillig; PLDI 2023):** An automated
  verifier built by Veridise and UT Austin that proves **weak uniqueness
  (circuit determinism)**—namely, that for any fixed public/private input vector
  $\vec{x}$, at most one output vector $\vec{y}$ can be extended to a satisfying
  wire assignment $\vec{z} \in \mathcal{C}$—by alternating lightweight static
  known-uniqueness propagation lemmas with SMT queries over finite fields (`cvc5`
  $\mathbb{F}_p$ solver / `Z3`).
- **`Ecne` (`0xPARC/Ecne`, Franklyn Wang; 2022):** The pioneering automated
  R1CS uniqueness checker that introduced iterative algebraic dependency
  propagation Rules (linear deduction, $a \cdot b = 0$ case splitting, and
  unique binary decomposition over $\mathbb{F}_p$) to detect under-constrained
  `Circom` signals without requiring a separate functional specification.
- **`Coda` (Chen, Pailoor, Wang, Rodríguez, Dillig, et al.; CAV 2024):** A
  statically typed ZK DSL and refinement-type checker built in **Coq** that
  embeds polynomial constraint predicates directly into refinement types over
  $\mathbb{F}_p$, discharging verification conditions via SMT and extracting
  certified `Circom`/R1CS circuits that are provably both sound
  (non-under-constrained) and complete (non-over-constrained).
- **`Garden` (`formal-land/garden`, Formal Land; 2024–2026):** A foundational
  verification framework in **Rocq (Coq)** for verifying **Plonky3** AIR chips
  (`SP1`/`OpenVM` RISC-V and precompile tables), `Circom`, and `LLZK` circuits,
  using a monadic shallow DSL (`M.t`) that separates deterministic functional
  specifications from non-deterministic relational constraint systems.
- **`Cairo` Lean Proofs (Avni, Bentov, Goldwasser, Chiesa, et al.; *A
  Formal Verification of the Cairo CPU*, CPP 2022):** A machine-checked proof in
  **Lean 3 / Lean 4** (StarkWare & CMU) that the polynomial AIR constraints of
  the Cairo Turing-complete STARK CPU soundly and completely enforce the
  fetch-decode-execute semantics of the Cairo instruction set over
  $\mathbb{F}_p$.
- **`Leo` ACL2 Verifier (Coglio, McCarthy, Smith, Chin, et al., Kestrel
  Institute & Aleo; FMCAD 2021):** A certifying compiler validation toolchain
  built in the **ACL2** theorem prover that parses `Leo` ASTs and generated R1CS
  files and generates machine-checked ACL2 theorems proving that each compiler
  pass and R1CS gadget refines the source language semantics.
- **`Circomspect` (`trailofbits/circomspect`, Trail of Bits; 2022–2026):** A
  fast static analyzer and SARIF linter for `Circom` integrated into CI that
  detects unconstrained outputs, `<--` simple assignments without `===`, unused
  sub-circuit outputs, and field aliasing hazards.
- **`ZKAP` (Wen, Stephens, Chen, Ferles, Pailoor, Dillig, Isiguzo; USENIX
  Security 2024):** A semantic static detector for `Circom` circuits based on
  circuit dependence graphs (CDGs) and abstract pattern predicates that catches
  missing sub-component constraints and arithmetic overflow bugs across large
  production circuits (`tornado-cash`, `maci`, `semaphore`, `zkEVM`).
- **`Korrect` (2023) and `Horus` (2024):** Automated symbolic and logic-programming
  (`Soufflé` Datalog + SMT) analyzers for R1CS and `Halo2` Plonkish constraint
  systems that check input-output functional dependency and range-check coverage.
- **`LAMPE` (`reilabs/lampe`, Reilabs & Aztec; 2024–2026):** A formal
  verification framework for **Noir** (Aztec's Rust-inspired ZK language) that
  extracts Noir ACIR/SSA programs into **Lean 4**, providing tactics and
  standard-library lemmas over prime fields to prove functional correctness,
  soundness, and completeness of Noir cryptographic libraries.
- **`RISC Zero` (`risc0/risc0`), `SP1` (`succinctlabs/sp1`), and `Jolt`
  (`a16z/jolt`) zkVM Verifiers:** Industrial RISC-V (`RV32IM` / `RV64IM`) zkVMs:
  `RISC Zero` and `SP1` use STARKs (`Plonky3` BabyBear/KoalaBear fields with
  `LogUp` cross-table lookups and Groth16/Plonk recursion wrappers), while
  `Jolt` uses `Lasso` sumcheck lookup arguments to decompose instruction
  execution into structured lookup tables. Ongoing community and vendor efforts
  (`Garden`, `zkLean`, `sail-riscv` to Lean/Rocq) verify the correspondence
  between the RISC-V ISA specification, precompile chips (`SHA-256`, `Keccak`,
  `Secp256k1`, `Ed25519`), and the receipt-binding verifier (`ReceiptClaim::ok`
  and `hashable_key` inspected in corpus package
  `zkvm-receipt-binding-and-verification-boundaries`).

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Specification-free uniqueness (`Picus`, `Ecne`) vs. Full Functional
  Specification (`Cairo` Lean, `Garden`, `LAMPE`, `Coda`, `Leo` ACL2):**
  Because writing a complete formal specification for a 100,000-constraint circuit
  is labor-intensive, `Picus` and `Ecne` verify a *relational 2-safety
  hyperproperty* on the constraint system $\mathcal{C}$ alone: $\forall \vec{x}
  \vec{z}_1 \vec{z}_2,\, \mathcal{C}(\vec{x}, \vec{z}_1) \land
  \mathcal{C}(\vec{x}, \vec{z}_2) \implies \vec{y}(\vec{z}_1) =
  \vec{y}(\vec{z}_2)$. Uniqueness catches missing constraints without a spec,
  but cannot detect if the unique function computed by $\mathcal{C}$ is the
  *wrong* mathematical function (e.g., wrong SHA-256 round constant). `Cairo`
  Lean, `Garden`, `LAMPE`, and `Coda` prove full functional refinement against a
  high-level spec.
- **SMT over $\mathbb{F}_p$ (`cvc5`, `Z3`) vs. Interactive Theorem Proving
  (`Lean 4`, `Rocq`, `ACL2`):** SMT solvers struggle with nonlinear finite-field
  polynomials of degree $\ge 3$ and variable-length loops (such as 64-round
  hashes or 256-bit multi-limb multiplication over a 31-bit BabyBear field),
  frequently timing out unless decomposed into small sub-circuits (`Picus`
  modularity). Interactive frameworks (`LAMPE` in Lean 4, `Garden` in Rocq,
  `Cairo` in Lean) verify arbitrary-scale circuits compositionally via ring
  tactics (`ring`, `omega`, `bv_decide`) with a tiny kernel TCB.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`Cairo` Lean, `Garden` (Rocq), `LAMPE` (Lean 4), `Leo` (ACL2):** Proof
  assistant kernel + circuit extractor/parser from R1CS/Plonky3/Noir AST.
- **`Picus` (`QED^2`), `Coda`, `Korrect`:** Unverified static propagation engine
  + `cvc5`/`Z3` finite-field theory solver.
- **zkVM Receipt Verifiers (`risc0`, `sp1`, `jolt`):** Rely on circuit-to-ISA
  soundness, Fiat-Shamir random oracle heuristics, FRI proximity-gap conjectures,
  and trusted verifier context configuration (disabling `FakeReceipt` / `mock`
  prover modes and discharging recursive `Assumption` lists).

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.** ZKP circuit and zkVM verification provides perhaps the
purest demonstration of why Anneal's four primitives belong together:

1. **`Language SemObs` & `Partial`:**
   - **High-Level Specification Language `L_spec`:** `Prog` is a pure functional
     or relational specification over bitvectors (`BitVec 32`, `BitVec 256`) or
     RISC-V architectural state; `Query` is `(pubIn, privIn)`; `Out` is `pubOut`;
     `SemObs` is `(pubIn, pubOut)`.
   - **Arithmetic Constraint Language `L_zk` (R1CS / Plonkish / AIR):**
     - `Prog` is a pair $\langle \mathcal{C}, W \rangle$ of a polynomial/lookup
       constraint system $\mathcal{C} \subseteq \mathbb{F}_p^m$ and a witness
       generator $W : \text{Query} \to \text{Option}(\mathbb{F}_p^m)$.
     - `Out` is the set of satisfying wire assignments $\vec{z} \in
       \mathbb{F}_p^m$ such that $\mathcal{C}(\vec{z}) = 0$.
     - `SemObs` (`obs : Out → SemObs`): Extracts the public input/output
       instance columns $(x(\vec{z}), y_{\text{pub}}(\vec{z}))$, erasing all
       internal advice and zero-knowledge blinding wires!
     - `defined` vs. `Partial.ub`: `(L_zk.sem ⟨C, W⟩ q).defined` holds iff (i)
       every wire assignment $\vec{z} \in \mathcal{C}$ matching public input
       $x(q)$ satisfies local gate/lookup well-formedness (no division by zero,
       no `LogUp` multiplicity wrap-around modulo $p$), and (ii) for fixed input,
       `obs z` is uniquely determined (`Picus`/`Ecne` determinism!).
2. **`BehaviorCodec L_spec L_zk`, `Compiles` (Soundness / No Under-Constraint),
   and `Abstracts`:**
   - **`decodeOut : F_p^m → Option L_spec.Out`:** Decodes the public output and
     limb wires of $\vec{z} \in \mathbb{F}_p^m$ into high-level bitvectors/integers
     *only if every limb wire satisfies its canonical range bound* (e.g.,
     $0 \le z_i < 2^{16}$), and returns `none` on any out-of-range field element
     (such as $p - 1$)!
   - **Why `Compiles L_spec L_zk codec s ⟨C, W⟩` = ZK Soundness:**
     `Compiles` states that for every satisfying wire assignment $\vec{z} \in
     \mathcal{C}$ accepted by the verifier, `codec.decodeOut z` must equal
     `some o₁` (never `none`!) where `o₁` satisfies `L_spec.sem s`. If the
     circuit is **under-constrained** (e.g., omits a 16-bit range lookup on a
     carry limb or allows a malicious witness $\vec{z}'$ with the wrong output),
     then $\vec{z}' \in \mathcal{C}$ either decodes to `none` (violating
     `Compiles`) or decodes to `some o₁'` that violates `s` (violating
     `Compiles`)!
   - **Notice how `obs_decodeOut` permits zero-knowledge blinding:** Because
     `obs` erases internal blinding factors $r \in \mathbb{F}_p$ while preserving
     public outputs, randomized witness assignments remain sound under
     `Compiles`.
3. **`ProductiveOn` & `InhabitedPre` (ZK Completeness / No Over-Constraint),
   `EventualBehaviorOf`, and `StepResult.externalCall`:**
   - **Why `ProductiveOn pre ⟨C, W⟩` = ZK Completeness:** Suppose a buggy or
     Goodharted circuit compiler emits the unsatisfiable constraint $1 = 0$.
     Then the set of satisfying wire assignments is empty (`val h = ∅`), so
     `Compiles` holds **vacuously**! Requiring `ProductiveOn pre ⟨C, W⟩` and
     `InhabitedPre pre` forces the witness generator $W$ to produce at least one
     valid assignment $\vec{z} \in \mathcal{C}$ for every valid input $q$
     satisfying `pre q`. Thus, **Anneal's `Compiles` + `ProductiveOn` is the
     exact mathematical definition of ZK Soundness + Completeness**!
   - **`EventualBehaviorOf`:** In zkVMs (`RISC Zero`, `SP1`, `Jolt`), a single
     RISC-V `ecall` to a `SHA-256` or `Keccak` precompile expands into 24–64
     trace rows in a secondary STARK table, while multi-segment continuations
     split execution across variable-length shards. `EventualBehaviorOf` aligns
     variable-row AIR traces with single-step ISA semantics without `Classical.choice`.
   - **`StepResult.externalCall boundaryInv branches`:** Models **Fiat-Shamir
     challenge sampling** (where `boundaryInv` asserts that all prior phase
     witness columns have been absorbed into the cryptographic sponge transcript
     before sampling lookup challenge $\beta, \gamma \in \mathbb{F}_p$) and
     **untrusted host-oracle hints** (where the prover queries an external
     nondeterministic hint oracle and `boundaryInv` enforces the in-circuit
     constraint check on the returned hint).
4. **`VerificationResult` and `TrustPolicy`:**
   - Separates machine-checked algebraic circuit equivalence (`ob.prop` proved
     in Lean) from cryptographic protocol and configuration assumptions
     (`FRIConjectureListDecoding`, `Poseidon2RandomOracle`,
     `Groth16TrustedSetup_BN254`, `Risc0DevModeDisabled`,
     `RecursiveAssumptionsEmpty`) tracked as explicit obligation IDs in
     `VerificationResult`.

---

### Category 6.4: Quantitative resource bounds, stack depth, and worst-case execution time (WCET)

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Safety-critical embedded
systems (DO-178C Level A avionics, ISO 26262 ASIL-D automotive brake/steering
controllers, IEC 61508 industrial PLCs, bare-metal Rust microcontrollers, and
smart-contract virtual machines) require **hard quantitative upper bounds** on
two non-functional resources that standard functional-correctness semantics
abstract away:

1. **Stack memory consumption (maximum stack-frame depth):** In standard C,
   Rust, and CompCert memory models, the call stack has infinite capacity. On
   real microcontrollers (ARM Cortex-M, RISC-V RV32E, Tricore) or kernel stacks,
   exceeding the fixed stack region silently overwrites adjacent `.bss`/heap
   memory or triggers a fatal double-fault reset.
2. **Worst-Case Execution Time (WCET) and algorithmic step/gas complexity:**
   Hard real-time tasks must provably complete before their scheduling deadline
   $D$ across all admissible inputs and initial pipeline/cache states; smart
   contracts and network packet handlers must resist algorithmic complexity
   Denial-of-Service (DoS) and out-of-gas traps.

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`AbsInt aiT` and `StackAnalyzer` (Wilhelm, Ferdinand, Heckmann et al.,
  AbsInt Angewandte Informatik; *The Worst-Case Execution-Time Problem—Overview
  of Methods and Survey of Tools*, ACM TECS 2008):** The industry gold-standard
  commercial static analyzers certified for DO-178B/C Level A (Airbus A380/A350
  fly-by-wire). `aiT` decodes binary executables, reconstructs control-flow
  graphs (CFGs), runs value/loop-bound abstract interpretation, models exact CPU
  instruction caches and out-of-order pipelines via abstract interpretation to
  bound basic-block cycle counts, and solves for the longest execution path via
  **Implicit Path Enumeration Technique (IPET)** using Integer Linear
  Programming (ILP). `StackAnalyzer` computes worst-case stack usage along the
  call graph.
- **`CompCertS` (Besson, Blazy, Wilke; POPL 2017) and Stack-Aware CompCert /
  `Stacking` (Wang, Wilke, Shao; POPL 2019; Carbonneaux, Hoffmann, Ramananandro,
  Shao; PLDI 2014):** Extensions of `CompCert` in Coq that replace the infinite
  block-based memory model with a **finite address-space memory model** (`2^{32}`
  or `2^{64}` bytes) and an explicit abstract stack frame list, propagating
  quantitative stack-consumption bounds through register allocation (`Linear`)
  and frame layout (`Stacking`) down to assembly so that source-level stack
  bounds guarantee freedom from stack overflow on hardware.
- **`CerCo` (*Certified Complexity*, Amadio, Ayache, Campbell, Mulligan,
  Piccolo, Pollack, Regis-Gianas, Sacerdoti Coen, Stark, Tranquilli; JAR 2014):**
  A Matita/Coq-verified C compiler targeting 8051 and ARM/Lustre that
  instruments source C basic blocks with **exact cycle-accurate cost
  annotations** induced by the backend assembly translation, allowing source-level
  Hoare logic proofs to certify exact machine-code execution time.
- **`RAML` (*Resource Aware ML*, Hoffmann, Aehlig, Hofmann; POPL 2012 / TOPLAS
  2017):** An automated resource-analysis system for OCaml/functional programs
  based on Tarjan's **potential method of amortized analysis** extended to
  multivariate resource polynomials, reducing worst-case heap, stack, and tick
  bound inference to Linear Programming (LP) over type derivations.
- **`TiML` (Wang, Wang, Chlipala; OOPSLA 2017):** A dependently typed ML-style
  language (mechanized in Coq) whose type system indexes function types by loop/
  data-structure sizes and big-$O$ / exact recurrence time bounds, discharging
  recurrence relations automatically via `Master Theorem` and SMT solvers.
- **`Iris` Time Credits and Space Credits (`CFML` / `Iris$`, Charguéraud and
  Pottier, JFP 2019; Mével, Jourdan, Pottier, ICFP 2019; Spies et al.):**
  Embeds quantitative amortized complexity and heap/stack space bounds into
  higher-order concurrent separation logic in Coq by treating each execution
  step as consuming one linear `$1` time credit (`$n ∗ ...`) and each allocation
  as consuming space credits.
- **`Bound-T` (Tidorum / Niklas Holsti):** Early aerospace WCET and stack
  analyzer (used on ESA space missions) based on Presburger arithmetic
  (`Omega` calculator) for loop-bound inference and IPET path analysis.
- **`OTAWA` (Ballabriga, Cassé, Rochange, Sainrat; Universite de Toulouse),
  `Chronos` (Li, Liang, Mitra, Roychoudhury; NUS), `Heptane` (Hardy, Puaut,
  Seznec; Inria Rennes), `SWEET` (Gustafsson et al., Mälardalen), and `Platin`
  (`t-crest/platin`, Hepp, Huber, Prokesch, Puschner; TU Wien):** Open-source
  static WCET toolchains combining binary CFG extraction, abstract-execution
  loop bound discovery (`SWEET`), cache/pipeline persistence analysis
  (`Heptane`, `OTAWA`, `Chronos`), and LLVM-to-machine-code flow-fact relation
  tracking (`Platin` PML format).
- **`RapiTime` (Rapita Systems):** Hybrid measurement-based and structural
  timing analysis tool used in avionics/automotive that combines hardware/on-target
  execution trace timestamps with structural CFG path aggregation.
- **`KoAT` (`aprove-developers/KoAT2-Releases`, Brockschmidt, Fabian, Giesl,
  et al.; TOPLAS 2016 / CAV), `Cofloco` (Flores-Montoya, Hähnle; SAS 2014), and
  `Loopus` (Sinn, Zuleger, Veith; CAV 2014):** Automated complexity and runtime
  bound analyzers for C/LLVM integer transition systems using multiphase linear
  ranking functions, size-change abstractions, and difference-bound reset chains.
- **`Gasol` and `Gastap` (Albert, Gordillo, Rubio, Sergey; CAV 2020):**
  Cost-equation and recurrence-solver tools built on `Cofloco` that infer symbolic
  upper bounds on EVM (Ethereum Virtual Machine) gas consumption and stack usage.
- **`cargo-call-stack` (`japaric/cargo-call-stack`, Jorge Aparicio / Rust
  Embedded Working Group):** Whole-program static stack usage analyzer for
  bare-metal Rust (`no_std`, ARM Cortex-M) that combines LLVM `-Z emit-stack-sizes`
  sections with call-graph analysis over ELF binaries to detect recursion,
  indirect calls, and maximum stack depth.

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Binary WCET (`aiT`, `OTAWA`, `Heptane`, `cargo-call-stack`) vs.
  Source-Level Cost Lifting (`CerCo`, `CompCertS`, `Platin`) vs. Type/Logic
  Bounds (`RAML`, `TiML`, `Iris` Credits):** Binary analyzers inspect actual
  machine instructions and linker-allocated stack frame sizes, which is
  mandatory for hardware cache/pipeline timing and register-spill stack accounting.
  However, compiler optimizations destroy loop structure and data-structure
  invariants needed to bound loop iterations (`Platin` must export flow-fact
  transformations across LLVM passes, which are unverified). `CerCo` and
  `CompCertS`/`Stacking` solve this inside Coq by proving that compiled machine
  code refines source code equipped with quantitative cost/stack budgets!
- **Amortized Potential (`RAML`, `Iris` `$n` credits) vs. Worst-Case Path ILP
  (`aiT`, `Heptane`):** ILP/IPET excels at flat embedded control loops with
  fixed iteration counts, but cannot express amortized data-structure bounds
  (e.g., splay trees or dynamic vector resizing where individual operations take
  $O(n)$ steps but any sequence of $m$ operations takes $O(m \log n)$). `RAML`
  and `Iris` time credits verify amortized bounds cleanly by storing potential
  functions inside data-structure invariants.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`CompCertS`, `Stacking`, `CerCo`, `TiML`, `Iris` (`CFML`):** Foundational
  Coq kernel proofs over operational semantics indexed by step counters and
  concrete byte-stack bounds.
- **`AbsInt aiT`, `OTAWA`, `Heptane`, `KoAT`, `RAML`, `cargo-call-stack`:**
  Unverified C++/OCaml/Rust analyzers relying on external LP/ILP/SMT solvers
  (`CPLEX`, `lp_solve`, `Z3`) and vendor-supplied microarchitectural pipeline
  timing models. Note a major soundness hazard in `cargo-call-stack` and
  static call-graph tools: any unresolved dynamic dispatch (`dyn Trait`),
  function pointer, or inline assembly without an explicit stack-size annotation
  can invalidate the whole-program stack bound if not fail-closed.

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.**

1. **`Language SemObs` & `Partial`:**
   - **Resource-Indexed Language `L_res` (Cycle & Stack Budgeted Semantics):**
     - `Query` carries the input state together with an explicit **initial
       stack capacity $S_{\max} \in \mathbb{N}$** and **cycle/gas budget
       $T_{\max} \in \mathbb{N}$**.
     - `Out` carries `(retVal, peakStackBytes, elapsedCycles)`.
     - `SemObs` (`obs`): Projects to `(retVal, peakStackBytes ≤ S_max,
       elapsedCycles ≤ T_max)`.
     - `defined` vs. `Partial.ub`: `(L_res.sem prog q).defined` is **false**
       (`Partial.ub`) whenever any execution path exceeds the hardware stack
       limit ($\text{sp} < \text{stack\_limit}$, i.e., `peakStackBytes > S_max`)
       or exceeds the hard real-time WCET deadline (`elapsedCycles > T_max`)!
2. **`BehaviorCodec L₁ L₂`, `Compiles`, and `Abstracts`:**
   - **Stack-Preserving & Cost-Lifting Compilation (`Stacking` / `CerCo`):**
     In `Compiles L_mir_res L_x86_res codec s t`, `codec.encodeQuery` translates
     the MIR stack/time budget into the target x86-64 byte stack budget
     (accounting for callee-saved register spills and 16-byte ABI alignment computed
     by the register allocator). If the x86-64 frame overflows $S_{\max}$ or
     misses the WCET bound $T_{\max}$, `decodeOut` returns `none` (or target is
     `Partial.ub`), falsifying `Compiles`.
   - **Amortized Potential & Ranking Abstraction (`RAML`, `KoAT`, `aiT` IPET):**
     `Abstracts L_potential L_mir_res codec v s` lifts concrete loop steps into
     a polynomial potential or lexicographic ranking transition system `v`.
     An untrusted LP/ILP solver (`RAML` / `aiT` / `KoAT`) computes dual Farkas
     multipliers or potential coefficients; Lean's kernel checks the linear
     inequality certificate in `O(n)` arithmetic steps to establish `Abstracts`!
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **Why `EventualBehaviorOf` + `ProductiveOn` Prevents Step-Budget Distortion:**
     As proved in Anneal corpus package
     `anneal-behavior-codec-and-progress-refinement-2026`, naive bounded-fuel
     semantics allow a degenerate morphism to map fuel $k \mapsto 0$, making an
     infinite loop appear "safe" because 0 steps cannot trigger UB!
     `EventualBehaviorOf` requires that every terminating source computation
     reaches a terminal target state in some finite number of concrete target
     steps $k'$, while `L_res` additionally bounds $k' \le T_{\max}$ inside
     `Out`.
   - **`StepResult.externalCall boundaryInv branches`:** Essential for
     **indirect calls and interrupt service routines (ISRs)** in
     `cargo-call-stack` and `Stacking`: before any external or indirect call,
     `boundaryInv` asserts that remaining stack headroom $\text{sp} -
     \text{stack\_base} \ge S_{\text{callee\_contract}}$ meets the callee's
     certified stack requirement, failing closed if an unannotated `dyn Trait`
     or ISR could overflow the stack.
4. **`VerificationResult` and `TrustPolicy`:**
   - Hardware WCET depends on microarchitectural assumptions outside the ISA
     (e.g., `NoInstructionCacheMiss_LockedSRAM`, `FlashWaitStates_Zero`,
     `InterruptPreemptionDepth_Max2`, `BusContentionBounded_DMA`). Tracking each
     hardware timing assumption as a positive obligation ID in
     `VerificationResult` (`ob.id ∈ waived ∨ ob.prop`) ensures that software
     loop-bound and stack-frame proofs remain 100% kernel-checked while the
     board-level hardware timing contract is audited explicitly in `TrustPolicy`.

---

### Category 6.5: Verified zero-copy parsers and binary wire formats

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Network protocol stacks (TLS,
QUIC, TCP/IP, DNS, SSH, Bluetooth, 5G), OS kernel IPC/virtio drivers, file-system
metadata readers, and cryptographic certificate parsers (X.509 ASN.1 DER, CBOR,
Protobuf) sit directly on the untrusted attack surface. In-place **zero-copy
parsers** and serializers must simultaneously prevent three classes of bugs:

1. **Spatial memory, alignment, and validity UB:** Out-of-bounds slice reads,
   integer overflow in length-field arithmetic (`offset + len` wrapping around
   `usize::MAX`), unaligned pointer dereferences, or transmuting arbitrary wire
   bytes into a Rust/C struct with invalid bit patterns (e.g., a `bool` byte
   $\notin \{0, 1\}$, an invalid `enum` discriminant, or uninitialized padding
   bytes read as initialized data).
2. **Parser malleability and format confusion (`Format-String / Ambiguity`
   attacks):** Two distinct high-level messages $m_1 \neq m_2$ serializing to
   the same byte slice (`Serializer(m₁) = Serializer(m₂)`), or two different
   byte slices $b_1 \neq b_2$ parsing to the same logical message $m$ in a
   context where cryptographic signatures cover the parsed AST rather than the
   canonical wire bytes (as in X.509 BER vs. DER signature-bypass vulnerabilities
   and Bitcoin transaction-malleability bugs).
3. **Parser starvation / rejection of valid inputs:** A buggy parser or
   overly restrictive zero-copy layout check that rejects compliant protocol
   frames, breaking interoperability.

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`EverParse` and `3d` (`project-everest/everparse`, Ramananandro, Delignat-
  Lavaud, Fournet, Swamy, Chajed, Kobeissi, Protzenko; USENIX Security 2019):**
  Project Everest's verified zero-copy parser generator in `F*`. Takes C-like
  data-format descriptions in the `3d` DSL (with dependent length constraints
  and field actions), synthesizes zero-allocation in-place validator functions
  in `Low*`/C (or Rust), and proves memory safety, arithmetic overflow freedom,
  and **non-malleability (bijective parser-serializer round-trip)** in `F*`.
  Deployed in the Microsoft Windows kernel (Hyper-V vSwitch network packet
  validators, USB/VMBus drivers) and Azure confidential computing firmware.
- **`Vest` (`secure-foundations/vest`, Cai, Wang, Bosamiya, Gancher, Parno;
  CMU Secure Foundations Lab, USENIX Security 2025):** A formally verified,
  high-performance zero-copy binary parsing and serialization framework for
  **Rust** verified in **Verus**. Provides a combinator library and RFC-style
  DSL that proves memory safety, absence of panics/overflows, and mutual inverse
  round-trip theorems (`parse(serialize(x)) == Ok(x)` and canonical
  non-malleability `serialize(parse(b)) == b`) on zero-copy Rust slices `&[u8]`.
- **`Narcissus` (Delaware, Suriyakarn, Pit-Claudel, Ye, Chlipala; MIT, ICFP
  2019):** A foundational Coq framework for synthesizing correct-by-construction
  binary encoders and decoders from relational format specifications using
  extensible combinators and automated tactic synthesis (` Fiat` refinement).
- **`Comparse` (`lthms/coq-comparse`, Wallez, Protzenko, Beurdouche, Bhargavan;
  CCS 2023):** A bit-precise parser combinator library in `F*` and `Coq`
  designed specifically for cryptographic protocol verification (`DY*` / `MLS*`),
  automatically proving that message concatenation grammars are **prefix-free
  and injective** so symbolic Dolev–Yao term equality coincides with concrete
  bitstring equality.
- **Google `zerocopy` (`google/zerocopy`, Liebow-Feeser et al.):** The flagship
  industrial Rust crate for safe zero-copy parsing and serialization via custom
  derive traits (`TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`,
  `KnownLayout`, `Immutable`, `Unaligned`). Replaces manual `unsafe {
  core::mem::transmute }` with compile-time layout, alignment, padding, and
  bit-validity obligation checks (analyzed extensively across the Anneal
  `reference` corpus packages `zerocopy-byte-domain-and-write-controls`
  and `zerocopy-validity-real-pass-certificate-alpha24`).
- **`RecordFlux` (`AdaCore/RecordFlux`, Componolit & AdaCore; 2020–2026):**
  Formal binary protocol specification language and code generator targeting
  **SPARK / Ada**, generating zero-copy message parsers and protocol state
  machines backed by `GNATprove` proofs of absence of runtime errors (AoRTE)
  and functional postconditions.
- **`DaeDaLus` (`GaloisInc/daedalus`, Diatchki et al., Galois; DARPA SafeDocs):**
  A monadic data-description language (DDL) for complex context-sensitive
  formats (such as PDF, ICC profiles, NITF, and UTF-8) that compiles format
  grammars into deterministic C++/Rust/Haskell parsers with formal semantics.
- **`Nail` (Bangert and Zeldovich; OSDI 2014) and `Hammer` (Patterson and
  Hirsch; LangSec):** Early influential LangSec parser generators; `Nail`
  introduced declarative grammar-to-struct bijections eliminating semantic
  actions, while `Hammer` provided bit-oriented packrat/GLR combinators in C.
- **`ASN1*` (Project Everest / Haonan et al.):** Formally verified zero-copy
  ASN.1 DER parser and serializer family in `F*`/`Low*` enforcing canonical
  shortest-length encoding to prevent X.509 certificate malleability.
- **`Kaitai Struct` (`kaitai-io/kaitai_struct`) and `Spicy` (`zeek/spicy`,
  Sommer et al., Corelight/Zeek):** Widely deployed industrial declarative
  binary format compilers (`Kaitai` YAML schemas; `Spicy` safe C++ streaming
  network parsers in Zeek IDS), emphasizing bounds-checked code generation
  without mechanized proof-assistant verification.

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Zero-Copy Transmute (`zerocopy`) vs. Zero-Copy Slice Validation (`EverParse`,
  `Vest`, `ASN1*`) vs. AST-Allocating Combinators (`Narcissus`, `DaeDaLus`):**
  Google `zerocopy` achieves **zero CPU instructions** for `FromBytes` types
  (pure pointer cast `&[u8] -> &T`) and minimal discriminant checks for
  `TryFromBytes` (`is_bit_valid`), whereas wire formats with variable-length
  fields (`TLV`, `TLS`, `QUIC`, `ASN.1 DER`) cannot be cast to a single
  fixed-layout C struct and instead require `EverParse` / `Vest` / `Comparse`
  offset-advancing slice validators.
- **Bijective Non-Malleability vs. Permissive Parsing:** Postel's Law ("be
  liberal in what you accept") is fatal in cryptographic protocols: if a parser
  accepts non-canonical encodings (e.g., leading zeros in an ASN.1 integer or
  trailing unparsed bytes), an attacker can mutate a signed packet's wire bytes
  (changing its hash/transcript) without changing the parsed struct! `EverParse`,
  `Vest`, `Comparse`, and `ASN1*` enforce **strict bijection** on canonical
  slices.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`Narcissus` and `coq-comparse`:** Foundational Coq kernel proofs of
  encoder-decoder inversion laws.
- **`EverParse` (`F*`/`Z3`) and `Vest` (`Verus`/`Z3`):** SMT-backed mechanized
  proofs of memory safety and parser-serializer round-trip bijections.
- **Google `zerocopy` (`cargo-anneal` / Anneal target):** In standard Rust,
  `#[derive(FromBytes, TryFromBytes, IntoBytes)]` relies on the proc-macro
  implementation and `unsafe` trait contracts; when verified with Anneal, those
  layout, padding, alignment, and bit-validity obligations are extracted from
  `rustc` MIR and proved inside the Lean 4 kernel (`Trusted.CrateTheorem`)!

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.** Look at the mathematical signature of `BehaviorCodec L₁ L₂`
in Anneal's `trusted/lean/`:

- `encodeOut : L₁.Out → L₂.Out`
- `decodeOut : L₂.Out → Option L₁.Out`
- `decodeOut_encodeOut : ∀ o₁, decodeOut (encodeOut o₁) = some o₁`
- `encodeOut_of_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`
- `obs_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁`

**Anneal's `BehaviorCodec` is literally the exact formalization of a Verified
Non-Malleable Parser and Serializer Pair (`EverParse` / `Vest` / `Narcissus` /
`Comparse` / `zerocopy`)!**

1. **`Language SemObs` & `Partial`:**
   - **Abstract Typed Value Language `L_typed`:** `Out` is the high-level Rust
     ADT / protocol message $v \in T$.
   - **Concrete Byte-Slice / Pointer Language `L_bytes` (`MirSemantics`):**
     `Out` is the raw memory byte slice `b : List Byte` (with provenance,
     initialization bits `InitMask`, and alignment). `Partial.ub` (`defined =
     False`) captures out-of-bounds slice indexing, unaligned pointer
     dereference, reading uninitialized padding bytes on `IntoBytes`, or
     constructing an invalid discriminant in `TryFromBytes::try_read_from_bytes`.
2. **`BehaviorCodec L_typed L_bytes`, `Compiles`, and `Abstracts`:**
   - **Parser Completeness (`decodeOut_encodeOut`):** Every serialized message
     `encodeOut v` parses back to `some v` (`parse(serialize(v)) == Some(v)`).
   - **Strict Non-Malleability / Canonical Representation (`encodeOut_of_decodeOut`):**
     Whenever `decodeOut b = some v`, `encodeOut v = b` (`serialize(parse(b)) == b`)!
     This single law in Anneal's `BehaviorCodec` automatically guarantees that
     no two distinct byte slices $b_1 \neq b_2$ can ever parse to the same typed
     value $v$ (ruling out BER/DER malleability, trailing garbage bytes, and
     format-confusion attacks!).
   - **Fail-Closed Invalid Bit-Pattern Rejection (`decodeOut b = none`):**
     For Google `zerocopy::TryFromBytes` or `EverParse` validators, any byte
     slice `b` containing an invalid enum tag, non-boolean byte $\notin \{0,1\}$,
     unaligned address, or truncated length maps to `decodeOut b = none`. Under
     `Compiles`, the target validator is forbidden from returning `Ok(&T)` on
     any input where `decodeOut b = none`!
3. **`ProductiveOn` & `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **`ProductiveOn` & `InhabitedPre`:** A trivial way to write a `TryFromBytes`
     or `EverParse` validator that never transmutes invalid bytes is to return
     `Err(())` on **every** byte slice! Pairing `Compiles` with `ProductiveOn
     ValidWirePre parser` proves that every valid wire encoding is actually
     accepted (`Ok`), preventing vacuous rejection.
   - **`StepResult.externalCall`:** Models streaming I/O buffer refills or
     `EverParse` field-action callbacks (`boundaryInv` asserts that the slice
     prefix up to `offset` has been validated before invoking the user callback).
4. **`VerificationResult` and `TrustPolicy`:**
   - Tracks target ABI layout assumptions (such as `TargetEndianness_Little`,
     `TargetPointerWidth_64`, or external RFC schema assumptions) as positive
     `TrustPolicy` obligation IDs while every `zerocopy` / `Vest` bit-validity
     and bounds check is discharged constructively in Lean.

---

### Category 6.6: Cross-language FFI, CHERI hardware capabilities, and secret zeroization

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Real-world Rust and C crates
do not execute in a closed single-language world: they link against C/assembly
libraries (`libc`, `BoringSSL`, `sqlite`, OS syscalls), run on hardware with
capability-enforced pointer provenance (`CHERI` / ARM `Morello`), and must
securely erase cryptographic keys from stack and heap memory before returning
(`zeroize`). Three catastrophic failure modes occur at these boundaries:

1. **Cross-Language FFI ABI, Representation, and Re-Entrancy Mismatches:**
   Passing a Rust reference or boxed closure across `extern "C"` into C or
   OCaml can violate aliasing invariants (`&mut T` aliased by a retained C
   pointer), corrupt garbage-collector / allocator headers, or trigger **open-
   world callback re-entrancy** (where an external C function calls back into
   the Rust module while the module's private ADT invariant is temporarily
   broken—the exact exploit mechanized in Anneal corpus package
   `anneal-structural-external-calls-and-tcb-mutation-testing-2026`).
2. **Pointer Provenance Forgery and Spatial/Temporal Capability Violations:**
   In integer-address architectures, casting an integer `usize` to a pointer or
   performing out-of-bounds pointer arithmetic (`p + offset`) can forge access
   to adjacent allocations. Hardware capability architectures (`CHERI`) attach
   unforgeable 128-bit bounds, permissions, and a 1-bit validity tag to every
   pointer register and memory word.
3. **Dead-Store Elimination (DSE) and Register-Spill Leakage of Secrets:**
   When a cryptographic routine zeroes a stack buffer `memset(secret_key, 0,
   32)` immediately before the variable goes out of scope, standard optimizing
   compilers (LLVM, GCC, `rustc`) delete the `memset` as a "dead store" because
   the buffer is never read again in the abstract machine (`What You See Is
   Not What You Execute`, D'Silva, Payer, Song; USENIX HotOS 2015). Even when
   `memset_s` or `write_volatile` zeroes the stack array, compiler register
   allocators silently leave copies of `secret_key` in callee-saved or scratch
   CPU registers, stack spill slots, or red-zone bytes!

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`DimSum` (Sammler, Spies, Song, D'Osualdo, Krebbers, Garg, Dreyer; MPI-SWS,
  POPL 2023):** A decentralized Coq/Iris framework for **multi-language
  semantics and compositional compiler/FFI verification**. Instead of baking a
  fixed global memory model into all languages, `DimSum` models each module (in
  high-level `Rec`, `Asm` assembly, or mathematical `Spec`) as an event-driven
  labeled transition system communicating via call/return events and uses
  combinators + `Simuliris`-style relational separation logic to verify
  cross-language linking, pointer-to-integer casts, and stack-switching
  coroutines.
- **`SepCompCert` (Kang, Kim, Hur, Dreyer, Viktor Vafeiadis; POPL 2016),
  `CompCertM` (Song, Cho, Kim, Hur; POPL 2020), and `CompCertO` (Koenig and
  Shao; Yale, POPL 2021):** Compositional extensions of `CompCert` in Coq.
  `SepCompCert` handles separate compilation of C modules; `CompCertM` supports
  mixed-language linking between C and hand-written assembly (`RSim` relational
  simulations); `CompCertO` introduces **open simulations Indexed by Kripke
  worlds and call/return language interfaces** so each pass composes both
  horizontally (linking) and vertically (compilation).
- **`VeriFFI` (Wang, Paraskevopoulou, Appel; Princeton, PLDI 2024):** A
  foundational Coq framework connecting `CertiCoq` (verified OCaml/Gallina) and
  `VST` (Verified Software Toolchain for CompCert C), using **foreign interface
  specifications** that relate functional Coq inductive types (`list`, `tree`)
  to heap-allocated C/GC graph representations while preserving garbage-collection
  roots across FFI calls.
- **`RLBox` (`PLSysSec/rlbox_sandboxing_api`, Narayan, Disselkoen, Garfinkel,
  Froyd, Rahm, Sorokin, Stefan, Shacham; USENIX Security 2020):** A C++ type-
  driven library sandboxing framework deployed in **Mozilla Firefox** (isolating
  `libgraphite`, `libogg`, `libexpat`, `hunspell`, `woff2` inside WebAssembly /
  process sandboxes) that tags all values and pointers crossing the FFI boundary
  as `tainted<T>` and enforces compile-time validation gates before untainted
  host code can branch on or dereference them.
- **`Sail-CHERI` and ARM `Morello` (`CTSRD-CHERI/sail-cheri-riscv` and
  `sail-morello`, Nienhuis, Joannou, Woodruff, French, Sewell, Watson,
  Neumann, Moore, Naylor, et al.; IEEE S&P 2020):** Authoritative instruction-set
  architecture specifications in the **Sail** language (compiled to `Isabelle/HOL`,
  `Coq`/`Rocq`, `Lean`, and C emulators) with machine-checked proofs in
  `Isabelle/HOL` of universal capability monotonicity (no execution sequence can
  ever escalate permissions or widen spatial bounds of held capabilities).
- **`Cerberus-CHERI` and `VIP-CHERI` (Memarian, Matthiesen, Lingard, Nienhuis,
  Chisnall, Watson, Sewell; ASPLOS 2019 / PLDI 2022):** Formal semantics of
  C and capability-C in Coq/Lem integrating the **PNVI-ae-udi** (Pointer-Numeric
  Value Integration) and **VIP** (Verified Integer-Pointer) provenance models
  with CHERI hardware capability tags.
- **`Secret-Erasure CompCert` (Besson, Blazy, Dumas, Laporte; *Towards a Formally
  Verified Secret-Erasing C Compiler*, and Barthe et al.):** Extends `CompCert`
  in Coq to preserve **secret erasure (`zeroize`)** down to machine code,
  instrumenting register allocation and stack-frame deallocation so that every
  register and stack spill slot tainted by a secret variable is explicitly
  scrubbed before function return.
- **`WYSIWYC` / `Zeroize-LLVM` (Simon, Chisnall, Anderson; *What You Get Is
  What You C: Controlling Side Effects in Mainstream C Compilers*, EuroS&P 2018;
  and Tuan, et al., *Clean-Up After Yourself: Compiler-Supported Secret
  Erasure*):** Compiler back-end extensions for Clang/LLVM that introduce
  `__attribute__((zero_call_used_regs))` (now in GCC 11+ / Clang 15+) and stack
  frame scrubbing to prevent register/spill remnant leaks.
- **Rust `zeroize` (`RustCrypto/utils/zeroize`, Tony Arcieri / RustCrypto):**
  The standard Rust cryptographic secret-erasure crate (`Zeroize`,
  `ZeroizeOnDrop`), combining `core::ptr::write_volatile` with
  `core::sync::atomic::compiler_fence(Ordering::SeqCst)` and architecture-specific
  inline assembly barriers so LLVM cannot elide the zeroing stores as dead
  writes.

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Decentralized Event Semantics (`DimSum`, `CompCertO`) vs. Shared-Memory
  Separation Logic (`VeriFFI`, `CompCertM`) vs. Tainted Sandboxing (`RLBox`):**
  `VeriFFI` and `CompCertM` verify trusted C and assembly modules that share a
  single flat address space with the caller, requiring explicit separation-logic
  ownership transfer of heap/stack footprints. `RLBox` assumes the foreign C
  library is **malicious or buggy** and isolates its memory inside a Wasm/CHERI
  sandbox, reducing FFI verification to checking the `tainted<T>` marshaling
  codec. `DimSum` unifies both by treating memory sharing and sandboxing as
  pluggable event-translation wrappers (`BehaviorCodec`!).
- **Library-Level `write_volatile` (`zeroize`) vs. Compiler-Integrated Secret
  Scrubbing (`Secret-Erasure CompCert`, `Jasmin`):** While Rust's `zeroize`
  prevents LLVM from deleting the explicit `write_volatile` loop over the User's
  struct in memory, it **cannot** erase secret values that LLVM's register
  allocator temporarily spilled to an anonymous stack slot during a complex
  calculation! Full secret erasure requires verifying the MIR-to-assembly
  register-allocation and stack-frame pass (`Stacking` / `Secret-Erasure
  CompCert`).

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`DimSum`, `CompCertO`, `CompCertM`, `SepCompCert`, `VeriFFI`,
  `Secret-Erasure CompCert`:** Foundational Coq kernel proofs.
- **`Sail-CHERI` / `Morello`:** Sail specification + Isabelle/HOL kernel proofs
  of capability monotonicity.
- **Rust `zeroize`:** Relies on `rustc`/LLVM honoring volatile store +
  `compiler_fence` semantics and does not cover compiler-generated stack spills.

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.**

1. **`Language SemObs` & `Partial`:**
   - **Multi-Language FFI & CHERI Capability Semantics (`DimSum`, `Sail-CHERI`,
     `Cerberus-CHERI`):**
     - `Out` in `L_cheri` / `L_mir` carries pointer values as capability tuples
       `(addr, base, length, perms, tag : Bool)` (matching Anneal's allocation-id
       provenance and bounds in `MirSemantics`). Any dereference with `tag =
       false`, `addr ∉ [base, base + length)`, or missing `Load`/`Store`
       permission transitions immediately to `Partial.ub` (`defined = False`).
   - **Post-Return Secret-Erasure Semantics (`Secret-Erasure CompCert`,
     `zeroize`):**
     - In `L_zeroize`, `Out` includes the post-return deallocated stack frame
       and caller-visible scratch registers `(retVal, postStackBytes,
       postScratchRegs)`.
     - `defined` requires that upon returning from any function holding a
       `ZeroizeOnDrop` secret, all bytes in `postStackBytes` (including compiler
       spill slots!) and `postScratchRegs` equal `0x00`.
2. **`BehaviorCodec L₁ L₂`, `Compiles`, and `Abstracts`:**
   - **FFI Marshaling & `RLBox` Taint Validation (`VeriFFI`, `RLBox`, `DimSum`):**
     `BehaviorCodec L_rust L_c_abi` defines the exact cross-language C ABI
     representation bijection (`#[repr(C)]` struct layout, pointer provenance,
     and ownership invariants). For `RLBox`-style sandboxed FFI, `decodeOut :
     TaintedCOut → Option ValidatedRustOut` runs the boundary validator and
     returns `none` on any out-of-bounds sandbox offset or invalid enum
     discriminant!
   - **Zeroization Verification via `decodeOut = none`:** In `Compiles
     L_idealZeroized L_x86 codec s t`, `codec.decodeOut` inspects the post-return
     x86-64 stack frame and scratch registers and **returns `none` if any secret-
     tainted spill slot or register is non-zero**! Consequently, if a backend
     dead-store-elimination pass deletes the zeroing store or leaves a secret
     limb in `%r11`, `decodeOut` yields `none`, and `Compiles` fails in the
     Lean kernel!
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **`StepResult.externalCall boundaryInv branches` (The Exact FFI & Callback
     Re-Entrancy Gate!):** As proved in Anneal corpus package
     `anneal-structural-external-calls-and-tcb-mutation-testing-2026`,
     `StepResult.externalCall boundaryInv branches` was specifically designed to
     solve the cross-language FFI and re-entrancy problem (`DimSum` / `CompCertO`
     / `VeriFFI`):
     - Before invoking an `extern "C"` function or dynamic callback, the
       interpreter checks `boundaryInv` (asserting that all private module/ADT
       invariants are restored, CHERI capabilities passed to the callee are
       bounds-restricted, and secret scratch buffers are scrubbed).
     - If `boundaryInv` fails, the step transitions to `Partial.ub` (`defined =
       False`).
     - If `boundaryInv` holds, `branches` demonically havoc-updates all memory
       reachable by the external callee while preserving caller-local frame
       isolation.
4. **`VerificationResult` and `TrustPolicy`:**
   - Foreign C/assembly functions that are not verified in Lean (e.g., an OS
     `getrandom` syscall or hardware cryptographic accelerator) are isolated as
     explicit external contract obligations (`ExternABIContract_libc_getrandom`)
     in `VerificationResult` governed by `TrustPolicy`.

---

### Comparative synthesis matrix across all six categories

| Category | Representative Tool Families | Primary Verification Target | Anneal `Language SemObs` & `Partial.ub` (`defined = False`) | Anneal `BehaviorCodec`, `Compiles` & `Abstracts` | Anneal `ProductiveOn`, `EventualBehaviorOf` & `StepResult.externalCall` | Anneal `VerificationResult` (`TrustPolicy` Waivers) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **6.1: 2-Safety, CT, SCT & IFC** | `CompCert-CT`, `Jasmin` (`-checkCT`/`-checkSCT`), `FaCT`, `ct-verif`, `Binsec/Rel` & `Haunted`, `Blade`, `Spectector`, `Pitchfork`, `CacheAudit`, `Constantine`, `CHL`/`Blazer`/`Themis`, `SecVerilog`/`Iodine`, `Jif`/`FlowCaml`/`LIO` | Architectural & speculative constant-time non-interference; cache leakage bounds | Paired 2-safety language `L_ct2`: `Partial.ub` on secret-dependent branch, cache address, variable-time opcode, or speculative transient leak | `obs_decodeOut` locks paired leakage traces across compilation; `Abstracts` lifts to security-type / taint / cache abstract domains | `ProductiveOn` prevents empty-domain CT transformations; `EventualBehaviorOf` aligns lockstep instruction expansion; `externalCall` checks `SLH` masks at calls | Hardware timing contracts (`X86Mul64ConstantLatency`, `SpectreWindow_250`, `CacheLine_64B`) |
| **6.2: Crypto Primitives & Protocol Game-Hopping** | `Fiat-Crypto`, `HACL*`/`EverCrypt`, `Vale`, `Libjade`, `Cryptol`/`SAW`, `CryptoLine`, `EasyCrypt`, `CryptoVerif`, `SSProve`/`FCF`/`CertiCrypt`, `CryptHOL`, `Owl`, `Tamarin`, `ProVerif`/`DeepSec`, `Squirrel`, `DY*`/`MLS*`, `Libcrux`/`hax` | Multi-limb $\mathbb{F}_p$ / NTT carry safety; computational game-hopping & Dolev–Yao protocol security | `Partial.ub` on limb carry overflow, non-canonical field output, AEAD nonce reuse, or signing-oracle forgery bad events | `decodeOut = none` rejects unreduced limbs; `decodeOut_encodeOut` + `encodeOut_of_decodeOut` certify bijective randomness-tape couplings across game hops | `ProductiveOn` ensures non-aborting UC simulators; `StepResult.externalCall` models adversary `O_Sign`/`O_Dec`/`O_RO` oracle queries with state-separation `boundaryInv` | Computational hardness assumptions (`MLWE_768`, `DDH_25519`, `ROM`) & external `SAW`/`Singular` certificates |
| **6.3: Zero-Knowledge Proofs & zkVMs** | `Picus` (`QED^2`), `Ecne`, `Coda`, `Garden`, `Cairo` Lean, `Leo` ACL2, `Circomspect`, `ZKAP`, `Korrect`/`Horus`, `LAMPE` (Noir/Lean 4), `RISC Zero`, `SP1`, `Jolt` | R1CS, Plonkish (`Halo2`/`Plonky3`), AIR & RISC-V zkVM circuit soundness + completeness | `SemObs` is public statement $(x, y_{\text{pub}})$ (erasing ZK blinding); `Partial.ub` on missing range check, witness ambiguity, or `LogUp` overflow | **`Compiles` = ZK Soundness** (`decodeOut = none` rejects out-of-range field limbs); `obs_decodeOut` preserves public instance columns | **`ProductiveOn` = ZK Completeness** (every valid input admits a satisfying witness $\vec{z} \in \mathcal{C}$); `EventualBehaviorOf` aligns zkVM precompile rows; `externalCall` gates Fiat-Shamir challenges | `FRIConjecture`, `KZG_BN254`, `Poseidon2_ROM`, `Risc0DevModeDisabled`, `RecursiveAssumptionsEmpty` |
| **6.4: Quantitative Resource Bounds & WCET** | `AbsInt aiT` & `StackAnalyzer`, `CompCertS`, `Stacking`, `CerCo`, `RAML`, `TiML`, `Iris` Time Credits (`CFML`), `Bound-T`, `OTAWA`/`Chronos`/`Heptane`/`SWEET`/`Platin`, `RapiTime`, `KoAT`/`Cofloco`/`Loopus`, `Gasol`, `cargo-call-stack` | Hard real-time WCET cycle bounds, maximum call-stack byte depth, amortized heap/gas complexity | `Query` carries $(S_{\max}, T_{\max})$; `Partial.ub` on stack overflow ($\text{sp} < \text{limit}$) or deadline overrun ($\text{cycles} > T_{\max}$) | `Compiles` propagates concrete stack spill sizes & cycle costs from MIR to x86-64; `Abstracts` checks LP/Farkas potential & ranking certificates | `EventualBehaviorOf` + `ProductiveOn` block step-zero fuel collapse while guaranteeing termination within $T_{\max}$; `externalCall` checks stack headroom at indirect calls/ISRs | Microarchitectural pipeline & cache tables (`LockedSRAM`, `FlashWaitStates_Zero`, `MaxISRDepth_2`) |
| **6.5: Verified Zero-Copy Parsers & Wire Formats** | `EverParse` (`3d`), `Vest`, `Narcissus`, `Comparse`, Google `zerocopy`, `RecordFlux`, `DaeDaLus`, `Nail`/`Hammer`, `ASN1*`, `Kaitai Struct`, `Spicy` | Spatial safety, bit-validity, alignment, and non-malleable parser-serializer bijections | `Partial.ub` on slice OOB, length-addition overflow, unaligned cast, uninitialized padding read, or invalid enum discriminant | **`BehaviorCodec` is a Non-Malleable Parser/Serializer Pair:** `decodeOut_encodeOut` = parse-serialize roundtrip; `encodeOut_of_decodeOut` = canonical non-malleability; `decodeOut = none` rejects invalid bit patterns | `ProductiveOn` guarantees parser completeness on valid wire messages (ruling out always-`Err` validators); `externalCall` gates streaming buffer callbacks | Target ABI layout parameters (`LittleEndian`, `PointerWidth_64`) & external RFC wire schema versions |
| **6.6: Cross-Language FFI, CHERI & Zeroization** | `DimSum`, `SepCompCert`/`CompCertM`/`CompCertO`, `VeriFFI`, `RLBox`, `Sail-CHERI`/`Morello`, `Cerberus-CHERI`/`VIP-CHERI`, `Secret-Erasure CompCert`, `WYSIWYC`/`Zeroize-LLVM`, Rust `zeroize` | Multi-language FFI linking, callback re-entrancy safety, CHERI capability monotonicity, and DSE-resistant secret erasure | `Partial.ub` on untagged/out-of-bounds CHERI capability dereference, FFI aliasing violation, or non-zero secret remnant in post-return stack/registers | `BehaviorCodec` checks `#[repr(C)]` FFI layout & `RLBox` taint validation; `decodeOut = none` rejects any non-zero post-return secret spill slot or scratch register | **`StepResult.externalCall` is the exact FFI & re-entrancy gate** (enforcing `boundaryInv` before external calls and demonically branching over returns) | Unverified foreign C/syscall specifications (`ExternContract_libc`, `HardwareRNG_Entropy`) |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **LLVM `__builtin_ct_select` (2024-2025), Coq SCT Jasmin Compiler (POPL 2025),
  `CT-Wasm` (POPL 2019), `SideTrail`, and `CTGREP` / `LIF`:** Compiler
  optimization barriers and Coq/Isabelle verifiers preserving Constant-Time and
  Speculative Constant-Time across lowering.
- **`LeaVe` (CCS 2023), `UPEC` (DAC 2019), `Revizor` (`microsoft/sca-fuzzer`),
  and `Hyper Hoare Logic (HHL)` / `AutoHyper` (PLDI 2024 / TACAS 2023):**
  2-safety relational RTL hardware-software leakage contract checkers and
  $\forall^*\exists^*$ hyperproperty verifiers.
- **Rupicola/Bedrock2 (`mit-plv/rupicola`), `s2n-bignum` (`awslabs/s2n-bignum`
  in HOL Light), `mlkem-native` (`CBMC` + `SLOTHY` + `s2n-bignum`), and
  `EasyUC`/`IPDL`:** Relational cryptographic synthesis, machine-code byte
  verification in HOL Light, and Universal Composability / MPC proof frameworks.
- **CertiPlonk (`NethermindEth/CertiPlonk`), Clean (`zksecurity/clean`), ArkLib
  (`Verified-zkEVM/ArkLib`), LLZK (`Veridise/llzk-lib`), and `acl2-jolt`
  (2024-2025):** Lean 4, MLIR, and ACL2 frameworks verifying Plonky3/AIR/Jolt ZK
  circuit soundness (`Compiles`) and witness completeness (`ProductiveOn`).
- **`C4B` (PLDI 2015), `RelCost` (POPL 2017), `LiquidATE` (POPL 2020), Menhir
  Coq-Verified LR(1) Parser (ESOP 2012), `Cogent` (ICFP 2016), `CHERIoT`, and
  `Iris-MSWasm` (POPL 2023):** Amortized C/relational cost logics, verified
  LR(1) grammar parsers, linear C FFI types, and microcontroller capability
  compartments.

---

### Part II — Historical Verification Failures, Root-Cause Postmortems, and Architectural Defenses

### 1. Compiler-Induced Constant-Time Violations and Microarchitectural Side-Channel Escapes

#### 1.1 How Optimizing Compilers Break Constant-Time Source Code (Simon, Chisnall, & Anderson EuroS&P 2018; Kaufmann et al. CANS 2016; Schneider et al. 2024)

Basis: documentation + source + derived.

Cryptographic implementations defend against timing and cache-timing attacks by
following the **constant-time programming discipline**: control-flow decisions
(branches, loop bounds), memory access addresses (array/table indices), and
variable-latency instruction operands must never depend on secret values.
Because C and Rust provide no source-level semantics for execution time or
register allocation, cryptographic engineers encode conditional assignments as
branchless bitwise arithmetic over all-ones (`0xFFFF...`) or all-zeros
(`0x0000...`) masks:

```rust
// Branchless constant-time selection in source Rust/C:
// mask is 0u64.wrapping_sub(cond as u64), i.e., 0xFFFF_FFFF_FFFF_FFFF or 0.
let selected = (a & mask) | (b & !mask);
```

Three landmark empirical studies and recent Rust CVEs demonstrate that
mainstream optimizing compilers systematically destroy these source-level
guarantees because their internal intermediate representations (LLVM IR, GIMPLE,
MSVC CIL) model only value-level input/output behavior:

1. **Kaufmann, Pelletier, Vaudenay, & Villegas (CANS 2016), *"When Constant-Time
   Source Yields Variable-Time Binary: Exploiting Curve25519-donna Built with
   MSVC 2015"*:**
   Adam Langley's 32-bit `Curve25519-donna` C implementation was meticulously
   written without secret-dependent branches or secret-indexed lookups, using a
   constant-time conditional swap (`cswap`) in the Montgomery ladder and 64-bit
   `uint64_t` shifts for radix-$2^{25.5}$ limb reduction. When compiled for
   32-bit x86 with Microsoft Visual C++ 2015 (`cl.exe /O2`), the compiler
   lowered 64-bit right shifts (`int64_t >> k`) to a runtime helper function
   `__allshr` and optimized the constant-time bitwise mask inside the ladder swap
   into a `test` + conditional jump (`je`) that skipped the swap when the secret
   scalar bit was `0`. Because the branch predictor and instruction cache traced
   every bit of the 255-bit secret scalar during X25519 key exchange, Kaufmann et
   al. recovered the full private key from local cache-timing observations.
2. **Simon, Chisnall, & Anderson (IEEE EuroS&P 2018), *"What You Get Is What You
   C: Controlling Side Effects in Mainstream C Compilers"*:**
   Auditing `Clang`/LLVM (versions 3.0 through 5.0) and `GCC` across x86-64,
   ARM, and MIPS on production constant-time primitives from OpenSSL, BoringSSL,
   and NaCl (`crypto_verify_16`, `constant_time_eq`, `constant_time_select`),
   Simon et al. showed that LLVM's `SimplifyCFG`, `InstCombine`, and backend
   `SelectionDAG` / `EarlyIfConversion` passes recognize bitwise selection
   idioms (`(x & m) | (y & ~m)` where `m = -(cond != 0)`), reconstruct the high-
   level ternary `cond ? x : y`, and then lower that ternary back into a
   conditional branch (`jne`) whenever the target CPU's branch-cost heuristic
   estimates a branch as cheaper than two ALU instructions plus a `cmov`. Worse,
   Simon et al. documented two additional compiler-induced side channels:
   - **Dead-store elimination of secret zeroization (`memset`):** Standard
     `memset(secret_buf, 0, len)` at the end of a stack frame is deleted by LLVM
     `DSE` (`DeadStoreElimination`) because reading a local buffer after
     function return is Undefined Behavior in C/Rust.
   - **Register-allocator secret spilling:** Even if source variables are
     zeroized, LLVM's greedy register allocator (`RAGreedy`) may spill
     intermediate secret values from architectural registers onto unnamed stack
     spill slots during high register pressure without ever zeroizing those
     stack slots before `ret`.
3. **Schneider, Lain, Puddu, Dutly, & Čapkun (2024 / CCS-era empirical compiler
   studies) and Rust `cmov` / `curve25519-dalek` (`CVE-2024-58262`):**
   Large-scale differential binary analysis across LLVM 14–19, GCC 11–14, and
   `rustc` demonstrated that LLVM's middle-end range analysis (`CorrelatedValuePropagation`
   and `InstCombine`) combined with backend instruction selection (`TargetLowering`
   on ARM Cortex-M0/M4, RISC-V, and x86-64) introduces secret-dependent branches
   into Rust crates that rely on portable bitwise masks rather than opaque
   inline assembly (`core::arch::asm!`) or `core::hint::black_box`. In
   `CVE-2024-58262`, the RustCrypto `cmov` crate (used by downstream
   cryptographic libraries) suffered an LLVM optimization on ARMv6-M (Cortex-M0)
   and other targets without hardware `cmov` instructions where LLVM recognized
   the bitmask conditional select and emitted a conditional branch (`bne`) over
   the secret condition bit.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Why value-only `Out` fails (`Trusted/Refinement.lean` &
  `Trusted/StepResult.lean`):** If `L_src` and `L_tgt` define `Out` solely by
  terminal return values (`TerminationKind Val`) with an empty observation trace
  (`Obs := Unit`), a compiler pass that rewrites branchless bitwise selection
  `let res = (a & mask) | (b & !mask)` into `if mask != 0 { a } else { b }`
  satisfies `Compiles L_src L_tgt C.π s t` (`L_tgt.sem t ≤ C.π (L_src.sem s)` at
  `Trusted/Refinement.lean:369-372`) because both programs compute the identical
  return value on every input!
- **Enforcing constant-time via `StepResult.step obs next` and
  `PartialBehaviorCodec`:** As established in `Trusted/StepResult.lean:70-74`
  and `reports/security-observations-and-relational-compiler-preservation`,
  `SmallStepMachine` records an explicit per-step observation `obs : Obs` in
  `ExecOut.trace : List Obs` (`Trusted/StepResult.lean:114-116`). When `Obs`
  records the program counter (`pc`), memory access address (`addr`), and
  stack-spill addresses at every step:
  1. A target pass `s ↦ t` that turns a branchless ALU sequence into a
     conditional jump emits distinct `pc` traces on secret-varying inputs and
     violates `obs_decodeOut` in `PartialBehaviorCodec`.
  2. Furthermore, because `rustc` delegates code generation to unverified LLVM
     passes, Anneal's `MIR-to-x86-64` architecture (`5fc1139f2208b3c9cfb513573c4a731cc32bb457`)—which compiles
     captured MIR directly to verified `X86Body` in Lean without passing through
     LLVM's middle-end `SimplifyCFG`/`InstCombine`—eliminates the unverified C/
     LLVM optimization gap entirely, provided `X86Body` is emitted from a single
     `.olean`-bound source (`SingleSourceCodegen.lean` in
     `anneal-rustc-obligation-inventory-and-single-source-codegen-2026`).

#### 1.2 Variable-Latency Integer Division in Post-Quantum Cryptography: `KyberSlash1` and `KyberSlash2` (Tamvada, Bhargavan, & Kiefer; Bernstein, Kannwischer, & Ravi Dec 2023)

Basis: documentation + source + derived.

In December 2023, two critical timing side-channel vulnerabilities—**`KyberSlash1`**
(discovered by Goutam Tamvada, Karthikeyan Bhargavan, and Franziskus Kiefer at
Cryspen) and **`KyberSlash2`** (discovered by Daniel J. Bernstein, Matthias J.
Kannwischer, and Prasanna Ravi)—were disclosed against the official C reference
implementation (`pq-crystals/kyber`) and over a dozen production libraries
(`PQClean`, `liboqs`, `circl`, `crystals-go`, `Botan`, `SYMCRYPT`) implementing
NIST's standardized post-quantum Key Encapsulation Mechanism **ML-KEM**
(CRYSTALS-Kyber, FIPS 203).

1. **Technical Root Cause (`idiv` / `udiv` on Secret Polynomial Coefficients):**
   - **`KyberSlash1` (`poly_tomsg`):** During Fujisaki-Okamoto (`FO`)
     decapsulation, after decrypting the noisy polynomial $v - s^T u \pmod q$
     (where $s$ is the secret key and $q = 3329$), `poly_tomsg` converts each
     polynomial coefficient $t \in \mathbb{Z}_q$ into a 1-bit message bit by
     computing:
     ```c
     t = (((t << 1) + KYBER_Q / 2) / KYBER_Q) & 1;
     ```
     Because `t` was a signed 16-bit integer (`int16_t`) rather than unsigned, or
     when compiled with `-Os` / size-optimization flags or on architectures
     where the compiler did not replace `/ 3329` with a Barrett/Montgomery
     multiply-shift sequence, `GCC` and `Clang` emitted a native hardware
     division instruction (`idiv` on x86, `sdiv`/`udiv` on ARMv7-A / ARMv8-M,
     `div` on RISC-V).
   - **`KyberSlash2` (`poly_compress` during re-encryption):** During the
     Fujisaki-Okamoto re-encryption check (which encrypts the decrypted candidate
     message $m'$ under a seed derived from $m'$ to verify that the resulting
     ciphertext matches the input ciphertext), `poly_compress` computed:
     ```c
     d0 <<= 4;
     d0 += 1665;
     d0 *= 80635;
     d0 >>= 28;
     ```
     in patched code, but in the unpatched reference implementation and several
     ports, compression divided secret-derived coefficients by `KYBER_Q` using
     `/` (`(((uint32_t)u[8*i+j] << 4) + KYBER_Q/2) / KYBER_Q`).
   - **Hardware Variable Latency:** On ARM Cortex-A7 (Raspberry Pi 2), Cortex-M4,
     Intel Skylake/Ice Lake, and RISC-V cores, hardware integer division is
     **not constant-time**: early-termination dividers take between 2 and 12+
     cycles depending on the number of leading zeros in the dividend and
     divisor. Using chosen ciphertexts, Bernstein et al. and Tamvada et al.
     demonstrated full ML-KEM private key recovery in **minutes** on ARM
     Cortex-A7 and Cortex-M4.
2. **Why Classic Constant-Time Static Analyzers Missed `KyberSlash`:**
   Early static constant-time verifiers defined the leakage observation trace
   solely as **control-flow (`PC`) + memory-access addresses (`Addr`)**. Under
   that restricted leakage model, `x / y` has no branches and touches no memory,
   so `((t << 1) + 1664) / 3329` verified as 100% "constant-time"! Only tools
   that include **variable-time instruction operands** in their leakage function
   $\lambda(\mathsf{instr}, \vec{v})$ (such as `ct-verif` Almeida et al. USENIX
   Security 2016, `Jasmin`'s constant-time checker, and the patched `Valgrind`
   `ctgrind` instruction-tainting rules released after `KyberSlash`) flag
   secret dividends/divisors in `idiv`/`udiv`/`sdiv`/`rem`.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Look at `Trusted/X86Semantics.lean` on the `MIR-to-x86-64` branch
  (`5fc1139f2208b3c9cfb513573c4a731cc32bb457`):** In `X86Semantics.lean`, `X86Machine` models `idiv`/`udiv`
  functional division and `#DE` traps (verified by `BoundaryCanarySuite` guards
  for division by zero and `INT64_MIN / -1` in
  `anneal-structural-external-calls-and-tcb-mutation-testing-2026`), but emits
  `Obs := Unit`.
- **Instruction-operand leakage in `StepResult.step obs next`:** To prevent a
  `KyberSlash`-class vulnerability when verifying constant-time Rust/x86-64 code
  in Anneal, `X86Machine`'s step observation `obs : X86LeakageObs` must record
  not only `.branch pc taken` and `.memAccess addr`, but also
  `.varLatencyOp opcode dividend divisor` for every architectural instruction
  whose hardware execution latency is data-dependent (`idiv`, `div`, variable-
  count shifts on legacy cores, and non-constant-time floating-point instructions).
  Under relational verification over `BehaviorOf`, two executions with
  differing secret inputs produce distinct `.varLatencyOp` traces unless both
  operands of `idiv`/`div` are proven public.

#### 1.3 Microarchitectural Prefetcher and Frequency Side-Channel Escapes: `Hertzbleed`, `Augury`, and `GoFetch` (2022–2024)

Basis: documentation + derived.

Even when a binary satisfies the strongest software constant-time contract—
identical `PC` traces, identical memory load/store addresses, and zero variable-
latency instructions—two classes of silicon microarchitectural optimizations
discovered between 2022 and 2024 break software constant-time isolation by
converting **data values** in registers or L1 cache into observable timing or
cache-state variations:

1. **`Hertzbleed` (Wang, Paccagnella, He, Shacham, Fletcher, & Kohlbrenner,
   USENIX Security 2022; `CVE-2022-23823` Intel, `CVE-2022-24436` AMD):**
   Modern x86-64 and ARM processors employ **Dynamic Voltage and Frequency
   Scaling (DVFS)** (Intel Turbo Boost, AMD Precision Boost) to keep power
   consumption within package thermal design power (TDP) limits. Because switching
   transistors from `0` to `1` (Hamming distance) and holding `1`s (Hamming
   weight) in 64-bit ALU/multiplier datapaths consumes data-dependent dynamic
   and leakage power ($\Delta P \propto \mathsf{HW}(x) + \mathsf{HD}(x, y)$),
   sustained arithmetic on low-Hamming-weight values consumes less power than on
   high-Hamming-weight values, allowing the CPU to stay at a higher Turbo Boost
   clock frequency (in MHz). Wang et al. exploited this power-to-frequency
   conversion to mount a **remote timing attack** against two formally audited,
   strictly constant-time implementations of SIKE (Supersingular Isogeny Key
   Encapsulation) in Cloudflare's `CIRCL` (Go) and Microsoft's `PQCrypto-SIDH`
   (C): by crafting ciphertexts where a target secret key bit caused internal
   Montgomery ladder values to collapse to `0x0000...0000` (low Hamming weight,
   higher clock frequency, faster wall-clock completion), the attacker extracted
   the full SIKE secret key over the network despite zero branches, zero
   secret-dependent memory accesses, and zero variable-cycle instructions.
2. **`Augury` (Vicarte et al., IEEE S&P 2022) and `GoFetch` (Chen, Wang,
   Paccagnella,izi, Kohlbrenner, Payer, Fletcher, & Morrison, USENIX Security
   2024) on Apple Silicon Data Memory-Dependent Prefetchers (DMP):**
   Apple A-14 and M1/M2/M3 processors include an undocumented hardware **Data
   Memory-Dependent Prefetcher (DMP)** attached to the L1/L2 cache hierarchy.
   Unlike classical stride or stream prefetchers (which inspect only the
   sequence of *load addresses*), a DMP inspects the **64-bit data values**
   loaded from memory into the cache/register file: whenever a loaded 64-bit
   word matches the bit-pattern heuristic of a valid virtual memory pointer
   within the process's address space, the DMP autonomously dereferences that
   value and prefetches the target cache line into L2—even if the program's
   instructions **never dereference, branch on, or index by that value**!
   While `Augury` (2022) initially believed DMP activation required specific
   array-of-pointers access patterns, `GoFetch` (March 2024) proved that standard
   loads of intermediate cryptographic state activate the DMP whenever a 64-bit
   secret-dependent intermediate value happens to collide with a valid pointer
   prefix. Using chosen inputs to steer intermediate values into pointer-shaped
   bit patterns and measuring L2 cache evictions (`Prime+Probe`) from an
   unprivileged co-located thread, `GoFetch` extracted complete secret keys from
   **constant-time** implementations of:
   - OpenSSL 3.x Diffie-Hellman key exchange,
   - Go's standard library `crypto/rsa` (2048-bit CRT decryption),
   - `CRYSTALS-Kyber` (`ML-KEM`), and
   - `CRYSTALS-Dilithium` (`ML-DSA`).
   On Apple M1 and M2 chips, the DMP cannot be disabled by software; mitigation
   requires either algorithmic operand blinding or setting the `DIT` (Data
   Independent Timing) / hardware chicken bit on Apple M3+ (`MSR DIT, #1`).

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Hardware-contract boundaries in `TrustPolicy` and `ScopedVerificationResult`
  (`Trusted/Refinement.lean:418-456` and
  `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`):**
  Software-level constant-time verification proves an architectural property of
  the ISA trace (`pc`, `addr`, `varLatencyOp`), **not** a physical silicon
  electromagnetic/DVFS or DMP prefetcher guarantee. If a verification framework
  conflates ISA trace noninterference with physical side-channel immunity, users
  are misled into deploying unblinded constant-time code on M1/M2 silicon where
  `GoFetch` extracts keys in under an hour.
- In Anneal's `ScopedVerificationResult` and `TrustPolicy`, any theorem that
  maps ISA-level trace equivalence (`ExecOut.trace`) to microarchitectural timing
  noninterference must carry an explicit, target-scoped `TrustedAssumption`—such
  as `.hardwareDataIndependentTiming_ARMv8_4_DIT` (requiring the `DIT` state bit
  to be set on entry in `ExecQuery.init` and hardware compliance with `DIT`
  semantics disabling DMP) and `.noDvfsPowerSideChannel`—audited by
  `TrustPolicy.isAllowed`. On M1/M2 targets where `DIT` does not disable the
  DMP, `policy.isAllowed .hardwareDataIndependentTiming_ARMv8_4_DIT` is `False`,
  forcing the cryptographic library to prove **value-blinding / pointer-prefix
  masking** in `theory/` so loaded 64-bit limbs never match virtual-address top
  bits.

### 2. Cryptographic Multi-Limb Arithmetic, Carry-Propagation, and Protocol State-Machine Failures

#### 2.1 Multi-Limb Carry-Propagation and Modular Reduction Bugs in OpenSSL, BoringSSL, `libgcrypt`, and `dalek`

Basis: documentation + source + derived.

High-performance public-key cryptography (RSA, Diffie-Hellman, X25519/Ed25519,
ECDSA over P-256/secp256k1) represents elements of large prime fields
$\mathbb{F}_p$ ($255$ to $4096$ bits) as arrays of 32-bit or 64-bit machine
words ("limbs"), using either saturated radixes ($2^{64}$) with hardware carry
flags (`CF` / `OF` via `adc`, `adcx`, `adox`, `mulx`) or unsaturated radixes
($2^{51}$ in 64-bit limbs or $2^{25.5}$ in 32-bit limbs) with delayed carry
propagation and conditional modular reduction. Because a carry out of an upper
limb occurs only when an intermediate limb equals $2^{64}-1$ (or $2^{51}-1$) and
receives an incoming carry—an event of probability $2^{-64}$ or $2^{-32}$ on
uniform random inputs—**random testing and differential fuzzing with uniform
inputs almost never exercise multi-limb carry-propagation bugs**:

1. **OpenSSL `bn_sqr8x_internal` Carry Overwrite (`CVE-2014-3570`):**
   In OpenSSL's hand-written x86-64 assembly squaring routine
   `bn_sqr8x_internal` (`crypto/bn/asm/x86_64-mont5.pl`), used whenever
   `BN_sqr` squared a multi-precision integer whose word length was divisible by
   8, a register spill/carry bug overwrote the carry flag (`CF`) before adding
   it into the next higher limb when a cross-product accumulation overflowed
   simultaneously with a diagonal square addition. The bug triggered with
   probability $\approx 2^{-64}$ per squaring operation, went undetected for
   years under millions of standard test vectors, and allowed an attacker to
   mount active fault/invalid-curve attacks against Diffie-Hellman and ECDH key
   exchanges to recover private key bits.
2. **OpenSSL `x86_64-mont5.pl` Montgomery Squaring Carry Bug (`CVE-2015-3193`):**
   Less than a year after `CVE-2014-3570`, differential fuzzing between OpenSSL
   1.0.2 and `libgcrypt` by Hanno Böck uncovered a second carry-propagation bug
   in `crypto/bn/asm/x86_64-mont5.pl` (`bn_sqr8x_mont` / `bn_mul4x_mont`) used
   by `BN_mod_exp` on Intel Broadwell/Haswell (`ADX`/`BMI2`) and standard
   x86-64 paths. During the final reduction step of 5-bit windowed Montgomery
   exponentiation, an unpropagated carry out of the most significant limb
   produced a corrupted modular power mod $N$. Because RSA with Chinese
   Remainder Theorem (`RSA-CRT`) computes $m_p = c^{d_p} \bmod p$ and
   $m_q = c^{d_q} \bmod q$ and combines them via Garner's formula, a single
   corrupted reduction in $m_p$ while $m_q$ is correct yields a signature $s'$
   satisfying $\gcd((s')^e - c, N) = q$—the classic **Bellcore (`Boneh-DeMillo-
   Lipton` 1997) single-fault RSA key recovery attack**, allowing a remote
   attacker who submits a crafted ciphertext/challenge triggering the $2^{-64}$
   carry edge case to factor the server's RSA modulus $N = p \cdot q$ in one
   query!
3. **`libgcrypt` Sliding-Window and Carry/Reduction Vulnerabilities
   (`CVE-2017-7526` & Differential Arithmetic Bugs):**
   In `libgcrypt` (used by GnuPG), Bernstein et al. (`CVE-2017-7526`) showed
   that the sliding-window modular exponentiation routine (`_gcry_mpi_powm`)
   leaked the complete sequence of squarings and multiplications—and sufficient
   information about the window multipliers—to recover 1024-bit and 2048-bit RSA
   secret keys via L1 cache bank conflict timing, while differential campaigns
   by Guido Vranken (`Cryptofuzz`) uncovered carry/reduction discrepancies across
   `libgcrypt`, OpenSSL, BoringSSL, and `mbedTLS` bignum routines.
4. **`curve25519-dalek` / `ed25519-dalek` Canonical Reduction, Scalar Bounds,
   and Double Public-Key Oracle Issues:**
   In pure-Rust cryptography, `curve25519-dalek` represents field elements
   modulo $p = 2^{255}-19$ in radix-$2^{51}$ (`FieldElement51([u64; 5])`) with
   explicit limb-bound invariants ($\forall i,\; l_i < 2^{51} + \epsilon$). Two
   classes of real-world vulnerabilities struck the `dalek` ecosystem:
   - **Limb-bound and constant-time compilation hazards:** Every field addition
     (`&a + &b`) adds limbs pointwise without carry propagation, increasing the
     limb bound from $2^{51}$ toward $2^{54}$. If a function omits an explicit
     `reduce()` call before a multiplication or serialization step whose
     tightness proof assumes 52-bit limbs, high bits overflow 128-bit
     intermediate accumulators (`u128`). This exact verification challenge
     motivated the formal verification of `curve25519-dalek`'s radix-$2^{51}$
     arithmetic using **Aeneas** (`Ho & Protzenko ICFP 2022`) and **Verus**.
   - **`ed25519-dalek` (< `v2.0.0`) Double Public-Key Signing Oracle:** In
     earlier versions of `ed25519-dalek`, the signing API accepted a caller-
     supplied public key $A$ alongside the secret key $s$ without re-deriving
     $A = [s]B$ or binding $s$ to $A$ in type invariants during deterministic
     nonce generation $r = H(\text{prefix} \parallel M)$ and challenge hashing
     $k = H(R \parallel A \parallel M)$: if a caller invoked `sign` twice on the
     same message $M$ with the same secret key $s$ but two different public key
     parameters $A_1 \neq A_2$, the deterministic nonce $r$ was identical ($R_1
     = R_2$) while the challenges $k_1 \neq k_2$ differed, giving the attacker
     two linear equations $S_1 = r + k_1 a \pmod \ell$ and
     $S_2 = r + k_2 a \pmod \ell$ and immediately solving for the secret scalar
     $a = (S_1 - S_2)(k_1 - k_2)^{-1} \bmod \ell$!
5. **How `Fiat-Crypto` (Erbsen et al., IEEE S&P 2019) and `CryptoLine` (Polyakov
   et al., CAV 2018) Solved Arithmetic Carry Bugs:**
   - **`Fiat-Crypto`** synthesizes saturated and unsaturated multi-limb C/Rust/
     Go/assembly routines from high-level prime-field specifications inside Coq
     using abstract interpretation over limb range intervals $[0, B_i]$,
     statically proving that no intermediate limb addition or multiplication can
     ever overflow machine word bounds.
   - **`CryptoLine`** verifies hand-written assembly (`x86_64-mont5.pl`,
     BoringSSL `fiat_curve25519`, NTT polynomial rings) by splitting each
     proof into an **algebraic polynomial ideal membership obligation**
     (checked via Singular/Gröbner bases over $\mathbb{Z}$) and a **bitvector
     range/carry no-overflow obligation** (checked via `Boolector`/`Bitwuzla`
     SMT solvers).

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Universal query coverage (`WellFormedOn pre` + `Compiles`) vs. $2^{-64}$
  carry bugs:** In Anneal (`Trusted/Refinement.lean:347-372`), `L.sem s ≤
  L.SpecOn pre post` quantifies universally (`∀ q : L.Query`) over the entire
  input bitvector space. A $2^{-64}$ carry-propagation edge case is simply a
  specific `q₀ : L.Query` where the implementation produces a wrong value or
  overflows a limb bound.
- **Limb-bound invariants as `PartialBehaviorCodec.decodeOut`:** When verifying
  unsaturated radix-$2^{51}$ field arithmetic (`FieldElement51([u64; 5])`)
  against the mathematical prime field $\mathbb{F}_{2^{255}-19}$, `PartialBehaviorCodec`
  defines:
  - `decodeOut (limbs : [u64; 5]) : Option (ZMod (2^255 - 19))` to return
    `some (∑ i, limbs[i] * 2^(51*i) mod p)` **if and only if** every limb
    satisfies its declared headroom bound `limbs[i] < B_i` (and for canonical
    serialization outputs, `∑ i, limbs[i] * 2^(51*i) < 2^255 - 19`), and `none`
    otherwise!
  - If a routine omits a carry reduction and allows `limbs[i] ≥ B_i` on a
    $2^{-64}$ input `q₀`, `decodeOut` returns `none`, which falsifies
    `Compiles L_field L_mir codec.toMorphism spec_op mir_op` at `q₀`!
- **Enforcing `ed25519-dalek` key-pair coupling via `AdtInv` and
  `StepResult.externalCall`:** The `ed25519-dalek` double public-key bug is a
  classic **broken ADT invariant** where `Keypair { secret, public }` failed to
  enforce the coupling `public == derive_public(secret)` at the API boundary. In
  Anneal, attaching `AdtInv` (`public == derive_public(secret)`) to `Keypair` in
  `MirSemantics.lean` and checking `boundaryInv` at `StepResult.externalCall`
  prevents any safe caller or FFI boundary from constructing an uncoupled
  `(secret, public)` pair.

#### 2.2 Symbolic Protocol State-Machine and Timing Gaps: Needham-Schroeder (Lowe 1995), TLS `3SHAKE` (2014), WPA2 `KRACK` (2017), and TLS `Raccoon` (2020)

Basis: documentation + derived.

Even when underlying arithmetic primitives are 100% bug-free, cryptographic
protocols fail when their verification model makes an implicit closed-world or
idealized state-machine assumption that the real network environment violates:

1. **Needham-Schroeder Public-Key Protocol (1978) & Gavin Lowe's Man-in-the-
   Middle Attack (1995):**
   Needham and Schroeder's 3-message mutual authentication protocol:
   $$\begin{aligned}
   1.\quad A \to B &: \{N_A, A\}_{pk(B)} \\
   2.\quad B \to A &: \{N_A, N_B\}_{pk(A)} \\
   3.\quad A \to B &: \{N_B\}_{pk(B)}
   \end{aligned}$$
   was considered secure for **17 years** and was proved "correct" in Burrows-
   Abadi-Needham (**BAN**) logic (1989). In 1995, Gavin Lowe modeled the
   protocol in the CSP model checker **FDR** allowing an honest initiator $A$ to
   intentionally initiate a session with a compromised/malicious participant $I$
   while $I$ simultaneously impersonates $A$ to honest responder $B$:
   - $A \to I : \{N_A, A\}_{pk(I)}$
   - $I(A) \to B : \{N_A, A\}_{pk(B)}$ (re-encrypting $N_A, A$ under $B$'s key)
   - $B \to I(A) : \{N_A, N_B\}_{pk(A)}$
   - $I \to A : \{N_A, N_B\}_{pk(A)}$ ($A$ decrypts this, sees her own $N_A$,
     and returns $N_B$ encrypted under $I$'s key!)
   - $A \to I : \{N_B\}_{pk(I)}$
   - $I(A) \to B : \{N_B\}_{pk(B)}$ ($B$ concludes he is talking privately to
     $A$ with shared nonces $N_A, N_B$, which $I$ knows in full!).
   BAN logic missed the attack because its idealization rules assumed honest
   principals only ever initiate sessions with uncompromised principals (a
   **closed-world 2-party assumption**), and Message 2 $\{N_A, N_B\}_{pk(A)}$
   omitted the responder's identity $B$ (`Needham-Schroeder-Lowe` fixes Message
   2 to $\{N_A, N_B, B\}_{pk(A)}$).
2. **TLS `3SHAKE` Triple Handshake Attack (Bhargavan, Delignat-Lavaud, Fournet,
   Pironti, & Strub, IEEE S&P 2014):**
   Individual proofs of TLS 1.2 full handshakes, abbreviated session-resumption
   handshakes, and secure renegotiation (RFC 5746) held in isolation. However,
   by composing three handshakes across a client $C$, man-in-the-middle $M$, and
   honest server $S$, Bhargavan et al. showed that because the TLS 1.2 master
   secret `master_secret = PRF(pre_master_secret, "master secret", ClientRandom || ServerRandom)`
   depended only on the two nonces and **not on the full handshake transcript
   (specifically omitting the server's X.509 certificate)**, $M$ could forward
   `ClientRandom` and the abbreviated session-resumption ticket between $C \leftrightarrow M$
   and $M \leftrightarrow S$ so both sessions shared the **exact same `master_secret`
   and `Finished` verify data** while bound to different certificates, hijacking
   client-authenticated TLS renegotations. Fixing `3SHAKE` required RFC 7627
   (**Extended Master Secret**, binding the full session transcript hash into
   key derivation) and TLS 1.3's transcript-hashed key schedule.
3. **WPA2 `KRACK` Key Reinstallation Attack (Vanhoef & Piessens, ACM CCS 2017;
   `CVE-2017-13077`):**
   The IEEE 802.11i (WPA2) 4-way handshake was mathematically proved secure in
   the Bellare-Rogaway symbolic/computational model as an idealized 4-step
   exchange. In real networks, Wi-Fi frames can be lost, so the IEEE 802.11
   state machine specifies that if the Access Point (AP) does not receive
   **Message 4** from the client, the AP **retransmits Message 3**. Furthermore,
   to maintain layer separation, the 802.11 state machine tells the handshake
   module to install the Pairwise Transient Key (`PTK`) into the lower-layer
   `AES-CCMP` / `TKIP` data-confidentiality module via the `MLME-SETKEYS.request`
   primitive upon receiving Message 3. When a man-in-the-middle attacker blocked
   Message 4 from reaching the AP, the AP retransmitted Message 3; the client
   accepted the retransmitted Message 3 and called `MLME-SETKEYS.request` a
   **second time** with the same `PTK`. In Linux (`wpa_supplicant`), Android,
   iOS, Windows, and OpenBSD, reinstalling the `PTK` **reset the transmit
   packet number (nonce counter) and replay counter back to `1`**! Because the
   client had already transmitted data frames encrypted under `PTK` with nonces
   $1, 2, \dots, k$ after the first Message 3, resetting the nonce counter to
   `1` forced immediate **`AES-CCMP` / `GCM` nonce reuse** ($C_1 \oplus C_1' =
   P_1 \oplus P_1'$), completely breaking WPA2 encryption!
4. **TLS 1.2 `Raccoon` Timing Attack (Merget, Brinkmann, Aviram, Somorovsky,
   Mittmann, & Schwenk, USENIX Security 2020; `CVE-2020-1968`):**
   TLS 1.2 specification (RFC 5246 §8.1.2) mandated that in finite-field Diffie-
   Hellman (`DH` / `DHE`) key exchange, the negotiated shared secret $Z = g^{xy}
   \bmod p$ must have **all leading `0x00` bytes stripped** before being passed
   as the `pre_master_secret` into the HMAC-SHA256/SHA384 key derivation
   function (`PRF`). Because HMAC processes inputs in 64-byte (SHA-256) or
   128-byte (SHA-384) compression blocks, when stripping $k$ leading zero bytes
   shortened the total PRF input across a 64-byte/128-byte SHA block boundary,
   HMAC executed **one fewer SHA compression function call**! When a server
   reused an ephemeral or static DH key $g^y \bmod p$, an attacker could send
   chosen client shares $g^{x_i} \bmod p$, measure the server's response timing
   to detect when $g^{x_i y} \bmod p$ started with leading zero bytes (i.e.,
   $0 \le g^{x_i y} \bmod p < 2^{\text{bitlen}(p) - 8k}$), and solve the
   resulting **Hidden Number Problem (HNP)** via lattice reduction (`LLL`/`BKZ`)
   to recover the server's private key $y$ and decrypt the target TLS session.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Why `StepResult.externalCall boundaryInv next` (`Trusted/StepResult.lean` +
  `anneal-structural-external-calls-and-tcb-mutation-testing-2026`) is essential
  for protocol state machines:**
  Needham-Schroeder (Lowe 1995), `3SHAKE`, and `KRACK` are all **re-entrancy and
  cross-layer state-reset bugs**:
  - In `KRACK`, the 802.11 handshake state machine made an external call
    (`MLME-SETKEYS.request`) to the data-plane cipher module without enforcing a
    monotone key-epoch / non-reinstallation invariant, and the network input
    loop accepted re-entrant retransmissions of Message 3 in the `PTK-INIT-DONE`
    state.
  - In Anneal's operational semantics (`StepResult.externalCall boundaryInv next`),
    sending a network packet or invoking the crypto driver (`MLME-SETKEYS`) is
    an explicit `externalCall` step. Encoding the one-time nonce-monotonicity
    and key-installation latch (`¬ keyAlreadyInstalled(sessionId)`) inside
    `boundaryInv : Bool` and marking duplicate nonce reuse as `.failed .ub`
    (`defined = False`) causes `ReachesPrefix` to step immediately to `.failed`
    when a retransmitted Message 3 triggers a second `MLME-SETKEYS` call!
  - Similarly, for Needham-Schroeder and `3SHAKE`, `StepResult.externalCall`
    models the Dolev-Yao network adversary as an arbitrary open-world environment
    that can interleave, replay, and re-enter any public protocol endpoint with
    corrupted principals—the exact same open-world adversary quantified over by
    `open_world_callback_composition_sound` in
    `StructuralExternalCallAndCanaries.lean`!
- **Why `Raccoon`'s specification flaw highlights `PartialBehaviorCodec` +
  constant-time `Obs`:** RFC 5246's leading-zero stripping rule violated fixed-
  width representation invariance: a 256-byte field element $Z \in \mathbb{F}_p$
  was encoded into a variable-length byte slice whose length leaked the top bits
  of $Z$ into the SHA block-count observation trace `Obs`. In Anneal, fixed-
  length big-endian serialization (as adopted in TLS 1.3 RFC 8446 §7.4.1, which
  preserves all leading zero bytes) is a fixed-width bijection in
  `PartialBehaviorCodec` whose `Obs` trace length is constant across all
  $Z \in \mathbb{F}_p$.

### 3. Zero-Knowledge Proof (R1CS, Plonkish, AIR, and zkVM) Under-Constrained, Over-Constrained, and Transcript Vulnerabilities

#### 3.1 The Soundness–Completeness Anatomy of SNARK Bugs (Chaliasos et al. USENIX Security 2024 SoK)

Basis: documentation + source + derived.

In *"SoK: What Don't We Know? Understanding Security Vulnerabilities in SNARKs"*
(33rd USENIX Security Symposium, 2024, pp. 3855–3872), Chaliasos, Ernstberger,
Theodore, Wong, Jahanara, and Livshits analyzed **141 real-world vulnerability
reports** collected from 2018 to 2024 across the SNARK software stack (circuit
DSLs such as `Circom`, `Halo2`, `Noir`, `Cairo`, and `Arkworks`; zkEVMs; and
proof-system backends). Their central finding is that **over 90% of circuit-
layer vulnerabilities are under-constrained or over-constrained bugs caused by
the split between imperative witness generation and declarative polynomial
constraints**:

- In a SNARK DSL (such as `Circom`) or a zkVM (`RISC Zero`, `SP1`), a program is
  compiled into two distinct artifacts over a prime field $\mathbb{F}_p$:
  1. **The Witness Calculator ($W : \text{Input} \to \text{Option}(\mathbb{F}_p^m)$):**
     Imperative code (written in Circom `<--`, Rust, or C++) that computes values
     for the $m$ circuit wires given public and private inputs.
  2. **The Constraint System ($\mathcal{C} \subseteq \mathbb{F}_p^m$):** A set
     of R1CS (`(A·z) * (B·z) = (C·z)`), Plonkish custom-gate/lookup, or AIR
     polynomial equations (`===`) checked by the cryptographic verifier.
- A malicious prover **throws away the honest witness calculator $W$** and
  directly chooses any wire vector $\vec{z} \in \mathbb{F}_p^m$ that satisfies
  $\mathcal{C}$! Consequently:
  - **Under-Constrained Bug (Soundness Failure):** $W$ computes the intended
    wire assignment $\vec{z} \in \mathcal{C}$ on honest inputs, so all unit
    tests pass (`ProductiveOn` holds!), but $\mathcal{C}$ omits a polynomial
    equation or range check, allowing a malicious prover to supply a bogus wire
    assignment $\vec{z}' \in \mathcal{C}$ that projects to a false public
    statement (`Compiles` fails!).
  - **Over-Constrained Bug (Completeness / Liveness Failure):** $\mathcal{C}$
    includes an overly restrictive polynomial equation (e.g., requiring an
    intermediate difference to be non-zero when legitimate edge-case inputs make
    it zero), so for valid inputs $q$ satisfying `pre q`, **no** wire assignment
    $\vec{z} \in \mathcal{C}$ exists ($\mathcal{C}(q) = \emptyset$, violating
    `ProductiveOn` and permanently freezing user funds in a rollup bridge!).

#### 3.2 `Circomlib`, Tornado Cash, Semaphore, and Aztec 2.0 Under-Constrained & Alias Bugs

Basis: documentation + source + derived.

Concrete historical postmortems from `Circomlib`, Tornado Cash, Semaphore, and
Aztec 2.0 illustrate how subtle algebraic omissions in $\mathbb{F}_p$ turn into
total soundness breaks:

1. **`Circomlib` `Edwards2Montgomery` / `Montgomery2Edwards` Missing Division-by-
   Zero Constraint (`BabyJubJub`):**
   To speed up elliptic-curve point additions inside SNARK circuits,
   `Circomlib` converted points on the twisted Edwards curve `BabyJubJub`
   ($ax^2 + y^2 = 1 + dx^2y^2$ over the `BN254` scalar field $p \approx 2^{254}$)
   to its birationally equivalent Montgomery curve via the rational map:
   $$u = \frac{1 + y}{1 - y}, \qquad v = \frac{1 + y}{(1 - y) x}$$
   In `Circom`, division cannot be written directly inside a degree-2 R1CS
   constraint `===`, so `Edwards2Montgomery` computed the witness via `<--` and
   constrained it by multiplication:
   ```circom
   out[0] <-- (1 + in[1]) / (1 - in[1]);
   out[0] * (1 - in[1]) === 1 + in[1];
   out[1] <-- out[0] / in[0];
   out[1] * in[0] === out[0];
   ```
   Look at `out[1] * in[0] === out[0]`: when the input Edwards point has
   $x = \text{in}[0] = 0$ and $y = \text{in}[1] = -1 \pmod p$ (the point of
   order 2 on `BabyJubJub`), `1 + in[1] = 0`, so `out[0] = 0`. Then the second
   constraint becomes:
   $$\text{out}[1] \cdot 0 = 0$$
   which holds for **every** $\text{out}[1] \in \mathbb{F}_p$! A malicious
   prover could supply `in = (0, -1)` and set `out[1]` to **any arbitrary field
   element**, forging point additions and signatures.
2. **`Circomlib` `Num2Bits(254)` / `LessThan` Field-Aliasing Bug (`AliasCheck`)
   & Tornado Cash / Semaphore Nullifier Collisions:**
   On the `BN254` scalar field, the prime modulus $p$ is a 254-bit prime:
   $$p = 21888242871839275222246405745257275088548364400416034343698204186575808495617 < 2^{254} - 1$$
   When a circuit decomposes a field element $x \in \mathbb{F}_p$ into 254
   binary wires $b_0, \dots, b_{253} \in \{0, 1\}$ using `Num2Bits(254)`:
   $$x \equiv \sum_{i=0}^{253} b_i 2^i \pmod p$$
   every field element $x \in [0, 2^{254} - 1 - p]$ has **two distinct 254-bit
   binary representations** in $\mathbb{F}_p$: its canonical bit vector
   representing $x$, and its "aliased" bit vector representing $x + p < 2^{254}$!
   In early versions of `Circomlib` and downstream protocols (Tornado Cash note
   commitments/nullifiers and Semaphore identity commitments that hashed bit
   arrays via Pedersen hashes while exposing the field element $x$ as a public
   nullifier), omitting `AliasCheck` (which constrains $\sum_{i=0}^{253} b_i 2^i
   < p$) allowed an attacker to deposit **one** note with secret $x < 2^{254}-p$
   and withdraw **twice**—once using the bit decomposition of $x$ and once using
   the bit decomposition of $x + p$, yielding two distinct nullifiers from the
   same note!
3. **Tornado Cash `MiMC` Sponge & Governance / Circuit Postmortems:**
   In Tornado Cash and early `Circomlib` `MiMCSponge` usages, circuits that
   computed `MiMC` rounds or Merkle-tree path selectors without constraining
   intermediate state wires or selector bits ($s \cdot (s - 1) = 0$) allowed
   non-binary path indices ($s \notin \{0, 1\}$) to linearly interpolate left and
   right Merkle children:
   $$L' = (1 - s) \cdot L + s \cdot R$$
   enabling a prover to forge Merkle inclusion proofs for arbitrary un-deposited
   leaves unless $s \in \{0, 1\}$ was explicitly constrained.
4. **Aztec 2.0 Missing Range Check in Rollup Note Value Summation (2021/2022):**
   In Aztec 2.0's Plonkish rollup circuits, join-split notes represented token
   amounts as integers embedded in the `BN254` scalar field $\mathbb{F}_p$. While
   individual input/output notes had range checks in isolation, an inner/outer
   circuit path omitted a tight bit-length range check on a fee/value wire,
   allowing a prover to supply a negative value modulo $p$ ($p - v$) that wrapped
   around $\pmod p$ during note balance conservation ($v_{\text{in},1} +
   v_{\text{in},2} \equiv v_{\text{out},1} + v_{\text{out},2} \pmod p$),
   inflating token balances out of thin air before the bug was disclosed and
   patched via Plookup range tables.

#### 3.3 zkEVM and RISC-V zkVM Constraint & Bridge Vulnerabilities: Polygon zkEVM, Scroll, `RISC Zero`, and `SP1`

Basis: source + documentation + derived.

As zero-knowledge systems scaled from application-specific `Circom` circuits to
full Ethereum Virtual Machines (**Polygon zkEVM**, **Scroll**) and RISC-V Zero-
Knowledge Virtual Machines (**`RISC Zero`**, **`SP1`**), under-constrained and
boundary-binding bugs shifted to **CPU instruction decoding, memory-alignment
hints, cross-table `LogUp`/`Plookup` arguments, and receipt-verification APIs**:

1. **Polygon zkEVM & Scroll Plonkish/AIR Cross-Table & Limb-Range Bugs:**
   In zkEVMs, 256-bit EVM words (`U256`) are split into 8-bit, 16-bit, or 32-bit
   limbs across dedicated execution tables (Main State Machine, Binary SM,
   Arithmetic SM, Keccak SM, Storage SM) connected via permutation and lookup
   arguments (`Plookup` / `LogUp`). Audits and bug bounties in Polygon zkEVM and
   Scroll uncovered critical vulnerabilities where:
   - An arithmetic carry or byte-decomposition column in a secondary state
     machine calculated the limb split in the witness generator (`executor`)
     without adding the corresponding range-lookup inclusion constraint on the
     highest limb, allowing a forged carry to corrupt `ADDMOD`/`MULMOD` or
     `CALLDATA` byte-slicing; or
   - Selector polynomials guarding conditional lookup queries were not
     multiplied into both sides of the lookup identity, allowing an active row
     in the CPU table to match a disabled ("padding") zero row in the secondary
     precompile table.
2. **`RISC Zero` Under-Constrained 3-Byte Aligned Memory / `sys_div` Host-Oracle
   Hint Vulnerabilities & Receipt Binding Boundaries:**
   - **Host-Oracle / Unconstrained Witness Hints:** In `RISC Zero`'s RV32IM
     circuit, complex operations (such as division/remainder `divu`/`remu` or
     sub-word unaligned memory loads) obtain non-deterministic witness hints from
     the host emulator and check them inside the AIR constraints (for instance,
     checking $a = b \cdot q + r$ and $0 \le r < b$ for unsigned division). In a
     disclosed 2024 `RISC Zero` circuit vulnerability, an instruction/memory
     addressing path failed to fully constrain a low-bit alignment/remainder
     condition on witness advice columns, allowing a modified prover to supply a
     forged witness value that satisfied the AIR polynomial identities while
     diverging from true RV32IM instruction semantics.
   - **Receipt API Verification Boundaries (`reports/zkvm-receipt-binding-and-verification-boundaries`):**
     As documented directly in the reference corpus at
     `risc0/risc0@3bbcd44d6459b9ef6ac0df3846dc9215514934e8`
     (`risc0/zkvm/src/receipt.rs:152-206`), calling
     `verify_integrity_with_context` alone checks only cryptographic proof
     integrity and **does not constrain the guest `ImageID` or `Halted(0)` exit
     status** (`ReceiptClaim::ok` at `claim/receipt.rs:75-94`), nor does it
     discharge non-empty recursive verification assumptions (`claim/receipt.rs:426`).
     Moreover, `FakeReceipt::verify_integrity_with_context` (`receipt.rs:589-599`)
     returns `Ok` without cryptographic proof verification whenever `dev-mode` is
     enabled in `VerifierContext`.
3. **`SP1` (`succinctlabs/sp1`) Precompile Bridge, Verifying-Key Binding, and
   Mock Verifier Boundaries:**
   In `SP1` (`succinctlabs/sp1@02fa30185ecd658174b211d56128b14867ab8e81`),
   RISC-V `ecall` instructions delegate heavy cryptographic operations
   (`sha256_compress`, `keccak256`, `secp256k1_decompress`, `uint256_mul`) from
   the main CPU Stark chip to specialized precompile chips over a multi-table
   `LogUp` memory bus. Soundness requires that:
   - Every memory read/write timestamp and register value on the precompile bus
     matches the CPU table's state transition (`PartialBehaviorCodec` +
     `StepResult.externalCall`),
   - The `LogUp` sumcheck denominators $\sum_i \frac{m_i}{\alpha - t_i}$ cannot
     wrap around modulo the BabyBear/KoalaBear prime $p \approx 2^{31}$ when
     trace lengths approach $p$, and
   - On the SDK boundary (`crates/sdk/src/mock/mod.rs:88-109`), mock Plonk/
     Groth16 verification (`verify_mock_public_inputs` at `proof.rs:22-47`)
     ignores the requested `StatusCode` and accepts empty proof bytes whenever
     public hashes match.

#### 3.4 Fiat-Shamir Transcript Omissions: Trail of Bits **Frozen Heart** (2022)

Basis: documentation + derived.

Interactive zero-knowledge protocols (Σ-protocols, Bulletproofs, PlonK, STARKs)
are converted into non-interactive proofs (NIZKs / SNARKs) using the **Fiat-
Shamir heuristic** (Fiat & Shamir, CRYPTO 1986): instead of waiting for a live
verifier to sample a random challenge $e \xleftarrow{\$} \mathbb{F}_p$, the
prover computes $e = H(\text{Transcript})$ using a cryptographic hash function
or sponge (`Poseidon`, `Rescue`, `SHA-256`, `Merlin`/`Blake3`).

In April 2022, Trail of Bits (Jim Miller, Least Authority / Trail of Bits crypto
team) disclosed **Frozen Heart** ("The Most Dangerous Code in the World of Zero-
Knowledge"), a vulnerability class across numerous production PlonK,
Bulletproofs, and Schnorr/Girault proof implementations (including early versions
of Dusk Network's `plonk`, `bulletproofs` forks, and custom MPC threshold
wallets):

- **Technical Root Cause:** For the Fiat-Shamir transformation to be sound
  (preventing adaptive statement/witness manipulation in the Random Oracle Model),
  the hash transcript **must absorb all public inputs, public keys, circuit
  verification keys, and all round-1..$k$ prover polynomial commitments** before
  squeezing round-$k$ challenge scalar $\beta, \gamma, \alpha, \zeta \in
  \mathbb{F}_p$. In affected implementations, the prover hashed only the round
  commitments $H(A, B, C)$ and **omitted the public inputs $(x_1, \dots, x_\ell)$**
  (or omitted the commitment $R$ in Schnorr-style proofs) from the transcript!
- **Exploit:** Because the challenge scalar $\zeta$ did not depend on the public
  input $x$, a malicious prover could first generate a dummy commitment, compute
  the fixed challenge $\zeta = H(\text{commitments})$, and then algebraically
  solve the PlonK quotient polynomial identity *backward* for whatever false
  public input $x_{\text{forged}}$ balanced the equation at evaluation point
  $\zeta$—forging valid zero-knowledge proofs for arbitrary false statements in
  milliseconds without knowing any witness!

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

Anneal's four primitives provide a direct, mathematically airtight solution to
every ZKP failure class in §§3.1–3.4:

1. **Simultaneous Soundness (`Compiles`) + Completeness (`ProductiveOn`)
   (`Trusted/Refinement.lean` + `anneal-behavior-codec-and-progress-refinement-2026`):**
   Let `L_spec` be the high-level functional relation over fixed-width types
   (`BitVec 64`, `Point`), and let `L_circuit` be the constraint-system language
   whose programs are pairs $\langle \mathcal{C}, W \rangle$ and whose outcomes
   at input $q$ are wire assignments $\vec{z} \in \mathbb{F}_p^m$ satisfying
   $\mathcal{C}(q, \vec{z})$.
   - **`Compiles L_spec L_circuit codec.toMorphism spec ⟨C, W⟩` proves ZK
     Soundness (No Under-Constrained Bugs):** By definition of `Compiles`
     (`L_circuit.sem ⟨C, W⟩ ≤ codec.toMorphism (L_spec.sem spec)`), **every**
     satisfying wire vector $\vec{z} \in \mathcal{C}(q)$—even one crafted by a
     malicious prover bypassing $W$—must decode via `codec.decodeOut z` to
     `some o₁` satisfying `L_spec.sem spec q`!
   - **`ProductiveOn pre ⟨C, W⟩` & `InhabitedPre pre` prove ZK Completeness (No
     Over-Constrained Bugs):** If a circuit were over-constrained ($\mathcal{C}(q)
     = \emptyset$), `(L_circuit.sem ⟨C, W⟩ q).val h` would be the empty set
     `fun _ => False`, which refines every specification vacuously (`False →
     post q o`). Requiring `ProductiveOn pre ⟨C, W⟩` ($\forall q,\; \mathsf{pre}\;
     q \implies \exists h\;z,\; W(q) = \mathsf{some}\;z \land \mathcal{C}(q, z)$)
     forces the honest witness calculator $W$ to produce a valid satisfying
     assignment on every input in `pre`!
2. **Blocking `AliasCheck` and Missing Range Checks via `PartialBehaviorCodec`:**
   In `PartialBehaviorCodec`, `decodeOut : F_p^m → Option SpecOut` checks that
   every bit wire $b_i \in \{0, 1\}$, every $w$-bit limb wire is $< 2^w$, and
   every 254-bit bit-decomposition wire array satisfies $\sum_{i=0}^{253} b_i 2^i
   < p$. If a circuit omits `AliasCheck` or an Aztec-style note range check, a
   wire assignment $\vec{z} \in \mathcal{C}$ exists with $\sum b_i 2^i \ge p$,
   for which `decodeOut z = none`. Under `PartialBehaviorCodec.toMorphism`,
   `decodeOut z = none` maps to `False`, immediately refuting `Compiles`!
3. **Blocking `Frozen Heart` and Unconstrained Host Hints via
   `StepResult.externalCall boundaryInv next`:**
   In multi-phase Plonkish/STARK protocols and zkVMs (`RISC Zero`, `SP1`),
   sampling a Fiat-Shamir challenge from the transcript sponge or receiving an
   untrusted host-oracle hint (`sys_div`) is modeled as `StepResult.externalCall
   boundaryInv next`:
   - For Fiat-Shamir challenges, `boundaryInv : Bool` checks that the transcript
     state's absorbed message list equals the canonical prefix of `vk ||
     public_inputs || phase_1..k_commitments`. Any implementation that squeezes
     a challenge before absorbing `public_inputs` has `boundaryInv = false` and
     steps immediately to `.failed` (`Partial.ub`), catching **Frozen Heart** at
     compile/verification time!
   - For zkVM receipt and assumption tracking (`RISC Zero` `FakeReceipt` /
     unresolved recursive assumptions; `SP1` mock verifiers), `ScopedVerificationResult`
     and `TrustPolicy` (`Trusted/Refinement.lean:418-456`) ensure that any mock
     receipt or undischarged recursive assumption must appear as an explicit
     `TrustedAssumption` rejected by production `TrustPolicy`.

### 4. Quantitative Resource Bounds (WCET Timing Anomalies, Stack Overflows) and Wire-Format Parser Malleability

#### 4.1 Out-of-Order CPU Timing Anomalies (Lundqvist & Stenström RTSS 1999)

Basis: documentation + derived.

In hard real-time avionics, automotive braking/steering, and spacecraft control
software, verifying functional correctness is insufficient: the verifier must
establish a sound upper bound on **Worst-Case Execution Time (WCET)**. Classic
static WCET analyzers decompose a program into its control-flow graph (CFG) of
basic blocks, compute the worst-case cycle latency $T_{\max}(B_i)$ of each basic
block $B_i$ by assuming every ambiguous cache access is a **cache miss** (local
worst case), and solve an Implicit Path Enumeration Technique (`IPET`) integer
linear program to sum $\sum_i c_i T_{\max}(B_i)$ along the longest path.

In their landmark paper *"Timing Anomalies in Dynamically Scheduled
Microprocessors"* (20th IEEE Real-Time Systems Symposium, RTSS 1999, pp.
12–21), Thomas Lundqvist and Per Stenström proved that on out-of-order,
dynamically scheduled superscalar CPUs (such as PowerPC, modern Cortex-A/R, and
x86-64), **local worst-case latency does NOT imply global worst-case execution
time ($\Delta t_{\text{local}} < 0 \implies \Delta T_{\text{global}} > 0$)**:

1. **Concrete Counterexample (Cache Hit Causing Longer Total Execution Time):**
   Consider an out-of-order CPU with an L1 data cache (1-cycle hit, 10-cycle
   miss), a fast integer ALU (1 cycle), and a non-pipelined multi-cycle integer
   multiplier (`MUL`, 6 cycles, prioritized oldest-ready-first):
   - Instruction $I_1$: `LD r1, [addr]` (feeds $I_2$)
   - Instruction $I_2$: `MUL r2, r1, r3` (non-critical path; independent of loop
     exit)
   - Instruction $I_3$: `ADD r4, r5, r6` (delays $I_4$ by 2 cycles)
   - Instruction $I_4$: `MUL r7, r4, r8` (**critical path** feeding a long
     dependency chain $I_5 \to \dots \to I_k$)
   Compare the two executions:
   - **Case A ($I_1$ L1 Cache Miss — Local Slow Case, +9 cycles on $I_1$):**
     Because $I_1$ stalls for 10 cycles waiting for memory, $I_2$ is not ready at
     cycle 2. Instead, $I_3$ finishes at cycle 2 and critical-path instruction
     $I_4$ claims the non-pipelined multiplier at cycle 3, completing at cycle
     9 and allowing the critical path $I_5 \dots I_k$ to finish at **cycle 20**.
     Meanwhile, $I_2$ runs later in the shadow of the critical path.
   - **Case B ($I_1$ L1 Cache Hit — Local Fast Case, -9 cycles on $I_1$):**
     Because $I_1$ hits in cache at cycle 1, $I_2$ becomes ready at cycle 2—
     **one cycle before $I_4$**! Because $I_2$ is older and ready, the out-of-
     order scheduler dispatches non-critical $I_2$ to the non-pipelined
     multiplier at cycle 2, locking out critical-path instruction $I_4$ until
     cycle 8! The entire critical path shifts later, finishing at **cycle 25**
     (+5 cycles longer globally than the cache miss!).
2. **Domino Effects (Unbounded Amplification):**
   Lundqvist and Stenström further exhibited **domino timing anomalies** where a
   1-cycle local difference at loop entry alters hardware prefetcher or
   branch-predictor/pipeline phase alignment so that every subsequent loop
   iteration suffers an extra stall, making the global timing penalty
   proportional to the loop trip count $O(N)$.
3. **Why Compositional Basic-Block WCET Addition Fails:**
   Because the latency function $T(B_1 ; B_2)$ is **not monotone** in the local
   step latency of $B_1$ when microarchitectural pipeline/cache/reservation-
   station state $\mu$ is erased, any WCET verifier that abstracts a basic block
   to a single scalar cycle bound $[t_{\min}, t_{\max}] \in \mathbb{N}$ is
   **unsound** on out-of-order hardware! Sound static WCET tools (`aiT` by
   AbsInt) must instead propagate abstract microarchitectural states
   $\hat{\mu} \in \mathcal{P}(\text{CacheState} \times \text{PipelineState})$
   across every instruction step, retaining both the hit state and miss state at
   join points whenever they are incomparable.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Look at `ExecQuery` and `EventualBehaviorOf` (`Trusted/StepResult.lean:105-109`
  and `anneal-behavior-codec-and-progress-refinement-2026`):**
  In Anneal, `ExecQuery State` pairs `init : State` with `steps : Nat`, while
  `EventualBehaviorOf` abstracts away intermediate architectural instruction
  counts (`steps : Nat`) for functional partial/total correctness.
- **How to model sound WCET in Anneal:**
  1. Never equate architectural instruction step count `steps : Nat` in
     `ExecQuery` with wall-clock CPU cycles on an out-of-order core (`X86Semantics`),
     because deleting a `.nop` or turning a cache miss into a hit in
     `Peephole.lean` reduces `steps : Nat` while potentially *increasing*
     out-of-order cycle count due to a Lundqvist-Stenström timing anomaly!
  2. To verify hard real-time WCET in Anneal, either:
     - Target an **in-order, timing-compositional core** (such as ARM Cortex-M0+/
       M4 or an in-order RISC-V core without timing anomalies, recorded as an
       explicit `TrustedAssumption` in `TrustPolicy`) where per-instruction
       cycle bounds compose monotonically via a quantitative `Obs := Nat` cycle
       trace in `StepResult.step cycles next`; or
     - For out-of-order cores, include the abstract pipeline/cache state
       $\mu \in \text{MicroArchState}$ inside `SmallStepMachine.State` and use
       `StepResult.choice .demonic branches` (`Trusted/StepResult.lean:84`) to
       branch demonically over **both** the cache-hit successor state and the
       cache-miss successor state whenever cache residency is uncertain! Because
       `BehaviorOf` (`Trusted/StepResult.lean:172-183`) requires `defined` and
       `SpecOn` postconditions to hold across **all** reachable demonic branches
       (`∀ tr out, ReachesPrefix ... → post`), demonic branching over `{hit,
       miss}` automatically explores both Case A and Case B of the Lundqvist-
       Stenström anomaly without unsoundly dropping the cache-hit branch!

#### 4.2 Embedded Stack Overflow Disasters: Toyota ETCS-i Unintended Acceleration and `cargo-call-stack` Indirect/Interrupt Gaps

Basis: documentation + source + derived.

Unlike desktop/server operating systems that place unmapped virtual-memory guard
pages below thread stacks, bare-metal and RTOS-based embedded microcontrollers
(automotive ECUs, medical devices, flight controllers) run in a flat physical
address space without an MMU (or with an MPU disabled/misconfigured). When the
hardware stack pointer (`sp`) overflows its allocated RAM region, pushes and
local frame writes silently overwrite adjacent `.bss`/`.data` global variables
or RTOS kernel data structures:

1. **Toyota Electronic Throttle Control System (`ETCS-i`) Unintended
   Acceleration Postmortem (`Bookout v. Toyota` 2013; Michael Barr & Philip
   Koopman 2014):**
   During the 2013 litigation over unintended acceleration in the 2005 Toyota
   Camry (`89661-06C20` main CPU running the OSEK-compliant `vrtx`/NEC V850E1
   RTOS), embedded systems experts Michael Barr (Barr Group) and Prof. Philip
   Koopman (CMU) inspected the production ECM source code and testified to severe
   stack-safety failures:
   - Toyota's own internal stack-sizing link map calculated worst-case stack
     usage as **788 bytes out of 4,096 bytes (19%)**, but omitted **136 functions**
     (including recursive call chains and system calls) and underestimated task
     context-switch frames; actual static stack depth exceeded **94% of the
     allocated stack** before accounting for nested hardware interrupts (ISRs)
     and recursion!
   - Worse, the memory layout placed the **RTOS kernel's critical task-control
     and system tables directly adjacent to the bottom of the stack** with zero
     MPU guard region: when nested interrupts or recursive error handlers pushed
     `sp` past the 4,096-byte boundary, the stack overwrite corrupted the RTOS
     scheduler structures, killing the 8 ms / 65 ms throttle-angle control task
     while leaving the hardware PWM H-bridge driving the throttle motor open,
     and failing to trigger the watchdog timer because the timer-tick ISR
     continued servicing the hardware watchdog in interrupt context!
2. **Static Stack Analysis Blind Spots in Embedded Rust (`cargo-call-stack`):**
   In the embedded Rust ecosystem, tools such as `cargo-call-stack` compute
   worst-case stack usage by combining LLVM's `-Z emit-stack-sizes` section
   (`.stack_sizes`, which records each function's local stack frame size in
   bytes) with a static call-graph extracted from LLVM IR / ELF relocations.
   However, static call-graph extraction fails closed or silently under-
   approximates stack usage in three pervasive Rust patterns:
   - **Indirect Calls via Function Pointers and Trait Objects (`&dyn Trait` /
     `core::fmt`):** Formatting macros (`write!`, `panic!`) dispatch through
     `core::fmt::Arguments` function-pointer tables (`vtable`). Because LLVM IR
     represents the call as an indirect `call %fn_ptr`, `cargo-call-stack`
     cannot determine the concrete target from relocations alone and emits an
      unresolved `Dynamic` / unknown-cycle edge unless whole-program type-based
     call-graph refinement is provided.
   - **Compiler Intrinsic / `libcore` Formatting Cycles:** Panic handlers and
     integer/float formatting routines in precompiled `libcore` often contain
     apparent call-graph cycles (`fmt` $\to$ `pad` $\to$ `fmt`), making naive
     DAG longest-path stack summation return $\infty$ (unbounded) unless loop/
     recursion bounds are proved semantically.
   - **Asynchronous Interrupt Service Routine (ISR) Preemption:** On ARM
     Cortex-M (`NVIC`) and RISC-V (`CLIC`), up to $K$ priority levels of
     hardware interrupts can preempt the main thread at the exact instruction
     where the main thread's stack pointer is at its deepest peak, pushing $K$
     additional hardware exception frames (`8` or `26` words each, plus lazy
     FPU context stacking) plus all ISR call trees onto the same Main Stack
     Pointer (`MSP`).

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Bounded stack frames in `Trusted/X86Semantics.lean` (`5fc1139f2208b3c9cfb513573c4a731cc32bb457`) and
  `BoundaryCanarySuite`:**
  In Anneal's `X86Semantics.lean` (hardened by `fixedX86Model` in
  `anneal-structural-external-calls-and-tcb-mutation-testing-2026`), every
  stack slot read/write checks `slot < maxFrameSlots` and every `call` checks
  stack-pointer alignment and remaining stack capacity (`sp ≥ frameBytes`); any
  stack overflow steps immediately to `.failed .ub` (`defined = False`).
- **Frame isolation and stack budgets across `StepResult.externalCall`:**
  When a function invokes an external or indirect callee via
  `StepResult.externalCall boundaryInv next`, `boundaryInv : Bool` can encode not
  only ADT invariants (`AdtInv`), but also the **remaining stack-budget
  precondition** `currentStackUsed + calleeMaxStack + isrReserve ≤ TotalStackSize`.
  If a callee's stack bound is not proved in Lean (for example, an external C
  function or an unverified ISR preemption reserve), that bound must be declared
  as an explicit, parameterized `TrustedAssumption` (`.externalStackBound "foo"
  256`) audited by `TrustPolicy` inside `ScopedVerificationResult`, making
  Toyota-style "136 omitted functions" impossible to hide inside a verified
  crate!

#### 4.3 Wire-Format Parser Malleability and Differential Bugs: Bitcoin DER (BIP-62/66), X.509 Null-Prefix (`CVE-2009-2408`), Android Master Key ZIP (`CVE-2013-4787`), and Android `Parcel` (`CVE-2014-7911`)

Basis: normative specification + documentation + source + derived.

Across network protocols, cryptographic ledgers, package managers, and OS IPC
boundaries (FFI/JNI), a **parser** decodes raw wire bytes $b \in \text{Bytes}$
into a structured domain value $v \in \text{Val}$, and a **serializer** encodes
$v$ back into bytes. When the decoding relation `decode : Bytes → Option Val` is
**non-injective** ($\exists b_1 \neq b_2,\; \mathsf{decode}(b_1) =
\mathsf{decode}(b_2) = \mathsf{some}\;v$) or when two subsystems use slightly
different decoders $\mathsf{decode}_A \neq \mathsf{decode}_B$ (**parser
differential**), catastrophic authentication and privilege-escalation exploits
follow:

1. **Bitcoin ASN.1 BER/DER Signature Malleability (Mt. Gox 2014; BIP-62 &
   BIP-66):**
   Prior to BIP-66 (activated July 2015), Bitcoin Core delegated ECDSA signature
   verification to OpenSSL's `d2i_ECDSA_SIG` ASN.1 parser. Instead of enforcing
   strict **Distinguished Encoding Rules (DER)**, OpenSSL accepted relaxed
   **Basic Encoding Rules (BER)** for the `(r, s)` signature tuple:
   - Arbitrary leading zero bytes (`0x00`) or negative-zero padding could be
     prepended to `r` or `s`;
   - Length fields could be encoded in multi-byte long form (`0x81 0x44` instead
     of `0x44`); and
   - Independently at the elliptic-curve layer (BIP-62), for every valid
     secp256k1 signature $(r, s)$, the pair $(r, n - s \pmod n)$ is also a
     mathematically valid ECDSA signature for the same message and public key!
   Because Bitcoin computed a transaction's unique identifier `txid =
   SHA256(SHA256(raw_tx_bytes))` over the **serialized wire bytes including the
   signature (`scriptSig`)**, any third party relay node on the peer-to-peer
   network could intercept an unconfirmed withdrawal transaction, pad the BER
   length/integer bytes or flip $s \mapsto n - s$, and broadcast the mutated
   transaction. The mutated transaction passed `ECDSA_verify` (same logical
   meaning!) and moved the coins to the same recipient, but had a **completely
   different `txid` hash**—causing exchange accounting databases that tracked
   withdrawals by `txid` to believe the withdrawal had failed and re-send the
   funds repeatedly (before SegWit BIP-141 moved witness data out of `txid` and
   BIP-66 enforced strict canonical DER).
2. **X.509 ASN.1 Null-Prefix Certificate Spoofing (`CVE-2009-2408` /
   `CVE-2009-2409`, Marlinspike & Kaminsky Black Hat 2009):**
   In ASN.1 DER (used by X.509 TLS certificates), string fields such as the
   Subject Common Name (`CN`) or Subject Alternative Name (`SAN`) are encoded as
   `(tag, length, bytes)` triples (`IA5String`, `UTF8String`, `PrintableString`),
   which may legally contain an embedded ASCII NUL byte (`0x00`) inside the
   explicit byte length. When an attacker requested a certificate from a
   commercial Certificate Authority (CA) for the domain string:
   $$\texttt{"www.bank.com\textbackslash 0.attacker.com"}\quad (\text{length} = 25)$$
   the CA's Pascal/Java/ASN.1 length-aware validation parser read the full
   25-byte string ending in `.attacker.com`, verified that the applicant owned
   `attacker.com`, and signed the X.509 certificate! When the attacker presented
   that signed certificate to a victim's web browser or SSL client (NSS, GnuTLS,
   OpenSSL, Windows CryptoAPI), the C client extracted the `CN` bytes into a
   `char *` buffer and called `strcmp` or `fnmatch` against the target hostname:
   because C strings are **NUL-terminated**, the client's hostname verifier
   stopped reading at `\0` and saw **`"www.bank.com"`**—accepting the
   certificate as valid for any bank or root domain on the Internet!
3. **Android "Master Key" ZIP Parser Differentials (`CVE-2013-4787` Bluebox
   Security, `CVE-2013-8619` Saurik):**
   Android application packages (`.apk`) are ZIP archives verified by a Java
   cryptographic signature verifier (`java.util.zip.ZipFile` in `PackageParser`)
   and then unpacked and installed by a privileged C++ daemon (`system/core/libziparchive`
   / `installd`). The ZIP file format places a **Central Directory (CD)** at the
   end of the file pointing to **Local File Headers (LFH)** scattered throughout
   the archive:
   - **Bug 1 (`CVE-2013-4787` Duplicate Central Directory Entries):** When an
     APK contained **two** Central Directory entries with the exact same
     filename `"classes.dex"`, Java's `ZipFile` stored entries in a
     `LinkedHashMap` (where the second entry overwrote the first, so the
     signature verifier checked the **second** benign `"classes.dex"`), whereas
     C++'s `ZipArchive` iterated linearly and extracted the **first** malicious
     `"classes.dex"`!
   - **Bug 2 (`CVE-2013-8619` Signed/Unsigned 16-Bit Field Length Overflow):**
     In the Local File Header, Java parsed the `extra field length` as a signed
     16-bit integer extended or handled differently from C++'s unsigned
     `uint16_t` offset calculation, allowing an attacker to make the Java
     signature verifier and C++ extractor read `"classes.dex"` from two
     completely different byte offsets within the same file!
4. **Android `Binder` `Parcel` Deserialization Mismatch (`CVE-2014-7911`,
    Jann Horn / Pangu Team):**
   In Android `< 5.0`, inter-process communication (`Binder` IPC) serializes
   `Bundle` / `ArrayMap` objects into a `Parcel` byte stream crossed between
   unprivileged app processes and the privileged `system_server` (`uid 1000`).
   When `ObjectInputStream` / `Parcel.readValue` deserialized a `Serializable`
   object inside `system_server`, it failed to verify that the class resolved by
   the receiver's classloader still satisfied `Serializable` invariants and matched
   the exact byte length consumed by the sender: by crafting a `Parcel` whose
   deserialized type confused `android.os.BinderProxy` fields with controlled
   64-bit pointers, an unprivileged app corrupted `BinderProxy.mObject` and
   achieved arbitrary native code execution inside `system_server` when the
   garbage collector ran `BinderProxy.finalize()`.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

Notice how **every single parser malleability and parser differential bug in
§4.3 is directly ruled out by Anneal's `PartialBehaviorCodec` (`anneal-behavior-codec-and-progress-refinement-2026`)**:

1. **Injectivity (`encodeOut_of_decodeOut`) Prohibits Signature & Transaction
   Malleability (BIP-62/66):**
   In `PartialBehaviorCodec`, the partial-bijection law:
   ```lean
   encode_of_decode_some : ∀ {o₁ : L₁.Out} {o₂ : L₂.Out},
     decodeOut o₂ = some o₁ → encodeOut o₁ = o₂
   ```
   states that if a wire byte sequence `o₂` is accepted by the parser
   (`decodeOut o₂ = some o₁`), then `o₂` **must equal the unique canonical
   serialization `encodeOut o₁`**!
   - Suppose two distinct byte strings $b_1 \neq b_2$ (such as a canonical DER
     signature and a BER leading-zero-padded signature, or $(r, s)$ and
     $(r, n - s)$) both decoded to `some sig`. Then by `encode_of_decode_some`,
     $b_1 = \mathsf{encodeOut}(\mathsf{sig}) = b_2$, contradicting $b_1 \neq
     b_2$!
   - Thus, **it is mathematically impossible to construct a `PartialBehaviorCodec`
     for a non-canonical or malleable parser**! Any non-canonical wire encoding
     (extra leading zeros, long-form lengths, high-$S$ signatures, duplicate ZIP
     central directory entries, or trailing unconsumed bytes) **must** map to
     `decodeOut b = none`.
2. **Round-Trip Identity (`decode_encode_out`) and Common Spine (`obs_decodeOut`)
   Prohibit Parser Differentials (`CVE-2009-2408`, `CVE-2013-4787`,
   `CVE-2014-7911`):**
   - In `CVE-2009-2408` (X.509 NUL prefix), the ASN.1 string `"bank.com\0.bad.com"`
     cannot round-trip through a C NUL-terminated string type `CStr`: either
     `CStr` forbids interior `\0` bytes (so `decodeOut` returns `none` on any
     ASN.1 string containing `0x00`), or `encode_of_decode_some` fails because
     truncating at `\0` loses `.bad.com`.
   - When two subsystems (such as a signature verifier $V$ and an installer $I$
     in Android Master Key, or a Rust caller and C++ FFI callee across a `Parcel`
     boundary) communicate over a wire format $L_{\text{wire}}$, requiring both
     $V$ and $I$ to refine the **same** `PartialBehaviorCodec L_domain L_wire`
     forces both parsers to agree on the exact `some`/`none` domain and the
     exact decoded value `o₁` for every byte sequence $b \in \text{Bytes}^*$,
     eliminating parser differentials by transitivity.

#### 4.4 Cross-Domain Synthesis Matrix: Mapping Historical Failures to Anneal's 4 Trusted Primitives

| Historical Failure / CVE / Paper | Domain | Technical Root Cause | Violated Formal Property | Anneal `trusted/` Primitive That Blocks or Isolates It |
| :--- | :--- | :--- | :--- | :--- |
| **Compiler CT Violations** (Kaufmann CANS 2016; Simon EuroS&P 2018; `CVE-2024-58262`) | Crypto / Compilers | `MSVC`/`LLVM`/`GCC` rewrite bitwise masks `(a & m) \| (b & ~m)` into branches & delete `memset` | Value-only refinement (`Obs = Unit`) ignores `PC` and stack-spill traces | `StepResult.step obs next` (`Obs` tracks `pc` + `addr`) + single-source `.olean`-bound x86 codegen |
| **`KyberSlash1` & `KyberSlash2`** (Bernstein et al.; Tamvada et al. Dec 2023) | Post-Quantum Crypto (`ML-KEM`) | Secret polynomial coefficients divided by $q=3329$ via variable-latency `idiv`/`udiv` | Leakage model `Obs` tracked only `PC`/`Addr`, omitting instruction operand latency $\lambda$ | `X86LeakageObs.varLatencyOp` in `StepResult` + relational trace equivalence |
| **`Hertzbleed` (`CVE-2022-23823`) & `GoFetch` (USENIX Sec 2024)** | Microarchitectural Side Channels | DVFS power throttling (SIKE) & Apple M1–M3 DMP dereferencing pointer-shaped secret data | Silicon violates ISA constant-time assumption without `DIT` / operand blinding | `TrustPolicy` / `ScopedVerificationResult` explicit `.hardwareDIT` assumption + blinding in `theory/` |
| **OpenSSL Carry Bugs** (`CVE-2014-3570`, `CVE-2015-3193`) & `dalek` Limb Bounds | Multi-Limb Arithmetic | $2^{-64}$ carry-flag overwrite in `bn_sqr8x_internal` / `x86_64-mont5.pl` enabling Bellcore RSA fault attack | Testing missed $2^{-64}$ inputs; unverified carry/headroom invariant across limbs | Universal query coverage (`WellFormedOn`) + `PartialBehaviorCodec.decodeOut` checking limb bounds |
| **Needham-Schroeder (Lowe 1995), `3SHAKE` (2014), `KRACK` (`CVE-2017-13077`), `Raccoon`** | Crypto Protocols (TLS, WPA2) | Closed-world 2-party model, missing transcript hash, Message 3 retransmission resetting nonces, DH zero-stripping | Unguarded re-entrant callbacks & variable-length secret encoding | `StepResult.externalCall boundaryInv` (enforcing monotone nonce latch) + fixed-width `PartialBehaviorCodec` |
| **SNARK Under-Constrained & Alias Bugs** (`Circomlib`, Tornado Cash, Aztec 2.0, Chaliasos SoK 2024) | Zero-Knowledge Proofs (R1CS / Plonkish) | `<--` witness generator works (`ProductiveOn`), but `===` omits $x \neq 0$, `AliasCheck` ($< p$), or limb range check | Target constraint set $\mathcal{C}$ is wider than source spec (`¬ Compiles`) | `Compiles` (soundness) + `ProductiveOn` (completeness) + `PartialBehaviorCodec` (`decodeOut = none` on $\ge p$) |
| **zkVM Host-Hint & Receipt Bugs** (`RISC Zero`, `SP1`, Polygon zkEVM, Scroll) | RISC-V zkVMs & zkEVMs | Under-constrained host division/alignment hints; `verify_integrity` omitting `ImageID`; `FakeReceipt` dev mode | Unchecked oracle return & unverified receipt configuration assumptions | `StepResult.externalCall` post-hint constraints + `ScopedVerificationResult` rejecting mock/dev assumptions |
| **Trail of Bits `Frozen Heart` (2022)** | Fiat-Shamir NIZKs / PlonK / Bulletproofs | Public inputs omitted from Fiat-Shamir hash transcript before squeezing challenge $\zeta$ | Challenge sampled before public statement & commitments bound to sponge | `StepResult.externalCall boundaryInv` requiring full transcript absorption before challenge squeeze |
| **Out-of-Order WCET Timing Anomalies** (Lundqvist & Stenström RTSS 1999) | Hard Real-Time WCET | Local L1 cache *hit* lets non-critical `MUL` seize functional unit, delaying critical path (+5 cycles vs. miss) | Local cycle latency is non-monotone when pipeline/cache state $\mu$ is erased | `StepResult.choice .demonic` branching over `{hit, miss}` microarchitectural states; `EventualBehaviorOf` separation |
| **Toyota ETCS-i Stack Overflow (2013) & `cargo-call-stack` Unknowns** | Embedded RTOS & Static Stack Bounds | 136 functions omitted from link map; nested ISRs + recursion overflow stack into RTOS globals; indirect vtable calls | Unbounded/unverified stack depth across indirect calls and interrupts | `X86Semantics.lean` bounded stack-frame checks + `StepResult.externalCall` stack-budget invariants |
| **Bitcoin DER (BIP-62/66), X.509 `\0` (`CVE-2009-2408`), Android Master Key (`CVE-2013-4787`), `Parcel` (`CVE-2014-7911`)** | Wire Formats, Parsers & FFI/IPC | Non-canonical BER padding/high-$S$ mutates `txid`; ASN.1 `\0` vs. C `strcmp`; duplicate ZIP CD entries; JNI `Parcel` mismatch | Parser `decode` is non-injective (`¬ encodeOut_of_decodeOut`) or differs across languages | `PartialBehaviorCodec` injectivity (`encode_of_decode_some`) + fail-closed `decodeOut = none` on non-canonical bytes |

## Boundaries

### Part I Boundaries — Real-World Verification Tools

- **Not examined — standalone execution of third-party external verifiers:**
  This report synthesizes the architecture, formal semantics, TCB boundaries,
  and exact mathematical embeddings of the 75 tools across Categories 6.1–6.6
  from primary literature, upstream repositories, and existing Anneal
  `reference` corpus packages (`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` and
  `zkvm-receipt-binding-and-verification-boundaries`). Commercial binaries
  (such as `AbsInt aiT`, `StackAnalyzer`, `RapiTime`, and `Bound-T`) and
  external solver pipelines (`EasyCrypt`, `Tamarin`, `Picus`, `EverParse`) were
  not executed locally during this synthesis.
- **Known not to apply — unverified SMT/CAS solver Equivalence to Lean Kernel
  Proofs:** Tools relying on unverified SMT (`Z3`, `cvc5`, `Bitwuzla`), SAT/AIG
  (`ABC`), or CAS (`Singular`) backends (`ct-verif`, `Binsec/Rel`, `HACL*`,
  `Owl`, `Picus`, `Vest`, `CryptoLine` without Coq certificates) do not satisfy
  Anneal's `trusted/` kernel-only soundness boundary unless their outputs are
  exported as checkable proof certificates (such as `LRAT`, Farkas LP duals,
  Gröbner-basis Nullstellensatz cofactors, or explicit `BehaviorCodec` witnesses)
  and re-checked inside the Lean 4 kernel (`theory/`).
- **Known not to apply — source-only `zeroize` or `ct-verif` as a machine-code
  guarantee:** Verifying constant-time (`ct-verif`, `Pitchfork`) or secret
  erasure (`RustCrypto/zeroize`) purely at the source or high-level IR layer
  does not prevent downstream unverified compiler passes (such as LLVM
  `SimplifyCFG` or register spilling) from re-introducing secret-dependent
  branches or un-zeroed stack spills unless paired with a verified backend
  (`CompCert-CT`, `Jasmin`, `Secret-Erasure CompCert`, or Anneal's verified
  `MIR-to-x86-64` compilation pipeline).

### Part II Boundaries — Historical Verification Failures

To prevent future agents from over-generalizing the findings in this report, the
following boundaries distinguish what is established from what remains outside
scope:

- **Not examined (Physical EM / Power Analysis and Fault-Injection Physics):**
  While this report covers software-visible microarchitectural side channels
  (`KyberSlash` instruction timing, `Hertzbleed` DVFS frequency throttling, and
  `GoFetch` DMP cache prefetching), it does **not** examine physical
  oscilloscope Differential Power Analysis (DPA), Electromagnetic (EM) probe
  side channels, or laser/voltage-glitch hardware fault injection (beyond the
  software-triggered Bellcore RSA-CRT carry bug in `CVE-2015-3193`).
- **Known not to apply (ISA Constant-Time $\neq$ Apple M1/M2 DMP Immunity):**
  Proving that a compiled binary has secret-independent `PC`, memory addresses,
  and instruction-operand latencies in Anneal's `SmallStepMachine` is **known
  not to apply** as a guarantee against Data Memory-Dependent Prefetcher (DMP)
  key extraction on Apple M1 and M2 processors (`GoFetch`), because the M1/M2
  DMP inspects 64-bit register/cache *values* loaded from memory and cannot be
  disabled via architectural state bits. Mitigating `GoFetch` on M1/M2 requires
  algorithmic blinding or pointer-prefix masking in the program's data
  representation.
- **Known not to apply (Architectural Step Count $\neq$ Out-of-Order WCET):**
  By Lundqvist and Stenström's theorem (RTSS 1999), reducing the architectural
  instruction step count `steps : Nat` in `ExecQuery` (or via `DilationCodec` in
  `Peephole.lean`) is **known not to apply** as a proof of reduced worst-case
  wall-clock cycle latency on out-of-order superscalar processors with shared
  non-pipelined functional units or speculative cache effects.
- **Unsupported in current `Trusted/X86Semantics.lean` (`5fc1139f2208b3c9cfb513573c4a731cc32bb457`):**
  The current `X86Semantics.lean` on `MIR-to-x86-64` sets `Obs := Unit` and models
  architectural registers and bounded stack slots without microarchitectural
  cache/pipeline state, hardware interrupt preemption frames, or a built-in
  `.varLatencyOp` observation constructor. Extending `X86Semantics.lean` to emit
  constant-time leakage observations or cycle-accurate in-order WCET traces
  requires instantiating the parameterized `Obs` type in `SmallStepMachine`.

## Evidence

### Part I Evidence — Real-World Verification Tools

- **Anneal `trusted/lean/` primitives and mechanized proofs (acquired
  2026-10-31):** Repository `joshlf/anneal`, branch `reference`, commit
  `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`:
  - `reports/anneal-behavior-codec-and-progress-refinement-2026/REPORT.md` and
    `support/MorphismAdmissibility.lean`,
    `support/BehaviorCodecExpressiveness.lean`,
    `support/AntiDegeneracyAndCallbackFraming.lean` (`Language`, `Partial`,
    `BehaviorCodec`, `PartialBehaviorCodec`, `Compiles`, `Abstracts`,
    `ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`).
  - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/REPORT.md`
    and `support/ProofGatedCompilationAndTrustPolicy.lean` (`VerificationResult`,
    `TrustPolicy`, `Obligation`, relational cut elimination, positive waiver
    scoping).
  - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/REPORT.md`
    and `support/StructuralExternalCallAndCanaries.lean`
    (`StepResult.externalCall`, callback re-entrancy protection, and 48-mutant
    TCB audit).
  - `reports/zkvm-receipt-binding-and-verification-boundaries/REPORT.md` (pinned
    source analysis of `risc0/risc0@3bbcd44d6459b9ef6ac0df3846dc9215514934e8`
    and `succinctlabs/sp1@02fa30185ecd658174b211d56128b14867ab8e81`).
  - `reports/zerocopy-byte-domain-and-write-controls/REPORT.md` and
    `reports/zerocopy-validity-real-pass-certificate-alpha24/REPORT.md` (Google
    `zerocopy` byte validity and layout verification).
- **Primary upstream repositories and specifications (observed 2026-10-31):**
  - Category 6.1: `jasmin-lang/jasmin`, `knothed/CompCert-ct`, `PLSysSec/FaCT`,
    `imdea-software/verifying-constant-time`, `binsec/Rel`,
    `PLSysSec/haybale-pitchfork`, `spectector/spectector`,
    `cacheaudit/cacheaudit`, `crocs-muni/ct-tools`.
  - Category 6.2: `mit-plv/fiat-crypto`, `project-everest/hacl-star`,
    `formosa-crypto/libjade`, `GaloisInc/cryptol`, `GaloisInc/saw-script`,
    `fmlab-iis/cryptoline`, `easycrypt/easycrypt`, `SSProve/ssprove`,
    `secure-foundations/owl`, `tamarin-prover/tamarin-prover`,
    `squirrel-prover/squirrel-prover`, `cryspen/libcrux`, `hacspec/hax`.
  - Category 6.3: `Veridise/Picus`, `0xPARC/Ecne`, `formal-land/garden`,
    `reilabs/lampe`, `trailofbits/circomspect`, `risc0/risc0`,
    `succinctlabs/sp1`, `a16z/jolt`.
  - Category 6.4: `aprove-developers/KoAT2-Releases`, `t-crest/platin`,
    `japaric/cargo-call-stack`.
  - Category 6.5: `project-everest/everparse`, `secure-foundations/vest`,
    `lthms/coq-comparse`, `google/zerocopy`, `AdaCore/RecordFlux`,
    `GaloisInc/daedalus`, `kaitai-io/kaitai_struct`, `zeek/spicy`.
  - Category 6.6: `CTSRD-CHERI/sail-cheri-riscv`,
    `PLSysSec/rlbox_sandboxing_api`, `RustCrypto/utils`.

### Part II Evidence — Historical Verification Failures

### 1. Anneal Repository Coordinates (`joshlf/anneal`)

- **Core Refinement, Partial Behaviors, and Trust Policy (`trusted/lean` at
  `24367bd1a8c784f2578535954f9915e24894a56f`):**
  - `trusted/lean/Trusted/Refinement.lean` (blob
    `7a81836536870398a6d0846474b08ceadf8402c3`, lines 208–472): `Preorder`,
    `Partial` (`defined`, `val`, `Partial.ub`), `Behavior`, `Language`,
    `SpecOn`, `WellFormedOn`, `Compiles` (`L369–372`), `Abstracts` (`L381–384`),
    `Compiler.SoundOn`, `Compiler.Verified`, `TrustedAssumption`, `TrustPolicy`,
    and `VerificationResultOn` (`L444–456`).
  - `trusted/lean/Trusted/StepResult.lean` (blob
    `4805cf0c30910890eb5914957776d7a26c52ef0c`, lines 58–199):
    `TerminationKind`, `StepResult`, `PrefixOutcome`, `ExecQuery`, `ExecOut`,
    `SmallStepMachine`, `ReachesPrefix` (`.emptyChoice`, `.noStep` transitioning
    to `.stuck`), and `BehaviorOf`.
- **MIR-to-x86-64 Target Semantics (`MIR-to-x86-64` at
  `5fc1139f2208b3c9cfb513573c4a731cc32bb457`):**
  - `trusted/lean/Trusted/X86Semantics.lean` (lines 24–343, 650–896): `X86Val`,
    `X86State`, `X86Instr` (`idiv`/`udiv`, ALU ops), `X86Machine`, and
    `EnsuresRetLibInv`.
  - `theory/Anneal/Compiler/NaiveCodegen.lean` & `Peephole.lean`: 2-stage
    lowering and peephole optimization passes.
- **Reference Corpus Hardening Packages (`zerocopy/reference` at
  `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`):**
  - `reports/anneal-behavior-codec-and-progress-refinement-2026/`:
    `PartialBehaviorCodec` (`decodeOut : L₂.Out → Option L₁.Out`,
    `decode_encode_out`, `encode_of_decode_some`), `EventualBehaviorOf`,
    `ProductiveOn`, and `CertifiedOptimizationPass`.
  - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/`:
    `StepResult.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)`
    (`support/StructuralExternalCallAndCanaries.lean:148-236`) and
    `BoundaryCanarySuite` (`L2570-2655`).
  - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/`:
    `TCBModel`, `refTCBModel`, `BoundaryCodec`, and `ScopedVerificationResult`
    (`support/ProofGatedCompilationAndTrustPolicy.lean`).
  - `reports/security-observations-and-relational-compiler-preservation/` &
    `reports/zkvm-receipt-binding-and-verification-boundaries/`:
    `ct-verif` (Almeida et al. USENIX Security 2016), `Jasmin`
    (`34f15840f10625bbc2cbf59b3d877e94c75bfbd9`), `risc0/risc0`
    (`3bbcd44d6459b9ef6ac0df3846dc9215514934e8`), and `succinctlabs/sp1`
    (`02fa30185ecd658174b211d56128b14867ab8e81`).

### 2. Primary Literature, CVEs, and Postmortem Sources

- **Compiler Constant-Time & Microarchitectural Side Channels:**
  - Thierry Kaufmann, Hervé Pelletier, Serge Vaudenay, & Karine Villegas, *"When
    Constant-Time Source Yields Variable-Time Binary: Exploiting
    Curve25519-donna Built with MSVC 2015"*, CANS 2016, LNCS 10052, pp. 573–582.
  - Laurent Simon, David Chisnall, & Ross J. Anderson, *"What You Get Is What
    You C: Controlling Side Effects in Mainstream C Compilers"*, IEEE EuroS&P
    2018, pp. 1–15.
  - Moritz Schneider, Daniele Lain, Ivan Puddu, Nicolas Dutly, & Srdjan Čapkun,
    *"Breaking Bad: How Compilers Break Constant-Time Implementations"*, 2024;
    `CVE-2024-58262` (Rust `cmov` / LLVM backend branch optimization).
  - Daniel J. Bernstein, Karthikeyan Bhargavan, Shivam Bhasin, Anupam Chattopadhyay,
    et al., *"KyberSlash: Exploiting Secret-Dependent Division Timings in Kyber
    Implementations"* (`https://kyberslash.cr.yp.to/`, Dec 2023 / 2024).
  - Yingchen Wang, Riccardo Paccagnella, Elizabeth Tang He, Hovav Shacham,
    Christopher W. Fletcher, & David Kohlbrenner, *"Hertzbleed: Turning Power
    Side-Channel Attacks Into Remote Timing Attacks on x86"*, USENIX Security
    2022, pp. 679–697 (`CVE-2022-23823`, `CVE-2022-24436`).
  - Jose Rodrigo Sanchez Vicarte et al., *"Augury: Using Data Memory-Dependent
    Prefetchers to Leak Data at Rest"*, IEEE S&P 2022, pp. 1491–1505.
  - Boru Chen, Yingchen Wang, Pradyumna Shome, Christopher W. Fletcher, David
    Kohlbrenner, Riccardo Paccagnella, & Daniel Genkin, *"GoFetch: Breaking
    Constant-Time Cryptographic Implementations Using Data Memory-Dependent
    Prefetchers"*, USENIX Security 2024 (`https://gofetch.fail/`).
- **Cryptographic Arithmetic & Protocol Postmortems:**
  - OpenSSL Security Advisories `CVE-2014-3570` (`bn_sqr8x_internal`) and
    `CVE-2015-3193` (`crypto/bn/asm/x86_64-mont5.pl`); `libgcrypt`
    `CVE-2017-7526`.
  - Andres Erbsen, Jade Philipoom, Jason Gross, Robert Sloan, & Adam Chlipala,
    *"Simple High-Level Code For Cryptographic Arithmetic — With Proofs, Without
    Compromises"* (`Fiat-Crypto`), IEEE S&P 2019, pp. 1202–1219.
  - Yu-Fu Fu, Jiaxiang Liu, Xiaomu Shi, Ming-Hsien Tsai, Bow-Yaw Wang, & Bo-Yin
    Yang, *"Signed Cryptographic Program Verification with Typed CryptoLine"*,
    ACM CCS 2019 / CAV 2018.
  - Gavin Lowe, *"An Attack on the Needham-Schroeder Public-Key Authentication
    Protocol"*, Information Processing Letters 56(3):131–133, 1995.
  - Karthikeyan Bhargavan, Antoine Delignat-Lavaud, Cédric Fournet, Alfredo
    Pironti, & Pierre-Yves Strub, *"Triple Handshakes and Cookie Cutters:
    Breaking and Fixing Authentication over TLS"* (`3SHAKE`), IEEE S&P 2014,
    pp. 98–113; IETF RFC 7627.
  - Mathy Vanhoef & Frank Piessens, *"Key Reinstallation Attacks: Forcing Nonce
    Reuse in WPA2"* (`KRACK`), ACM CCS 2017, pp. 1313–1328 (`CVE-2017-13077`).
  - Robert Merget et al., *"Raccoon Attack: Finding and Exploiting
    Most-Significant-Bit-Oracles in TLS-DH(E)"*, USENIX Security 2020
    (`CVE-2020-1968`).
- **Zero-Knowledge Proof Vulnerabilities:**
  - Stefanos Chaliasos, Jens Ernstberger, David Theodore, David Wong, Mohammad
    Jahanara, & Benjamin Livshits, *"SoK: What Don't We Know? Understanding
    Security Vulnerabilities in SNARKs"*, USENIX Security 2024, pp. 3855–3872.
  - Trail of Bits (Jim Miller et al.), *"Coordinated Disclosure of the Frozen
    Heart Vulnerability in Girault, PlonK, and Bulletproofs"*, April 2022.
- **WCET, Stack Analysis, and Parser Malleability:**
  - Thomas Lundqvist & Per Stenström, *"Timing Anomalies in Dynamically
    Scheduled Microprocessors"*, 20th IEEE RTSS 1999, pp. 12–21.
  - Michael Barr, *"Bookout v. Toyota Motor Corp. Trial Testimony and Expert
    Report on Camry ETCS-i Software"*, Oct 2013; Philip Koopman, *"A Case Study
    of Toyota Unintended Acceleration and Software Safety"*, Sept 2014.
  - Bitcoin Improvement Proposals BIP-62 (*"Dealing with Malleability"*) and
    BIP-66 (*"Strict DER Signatures"*); X.509 Null-Prefix `CVE-2009-2408`;
    Android Master Key `CVE-2013-4787` & `CVE-2013-8619`; Android `Parcel`
    `CVE-2014-7911`.

## Revalidation

### Part I Revalidation — Real-World Verification Tools

To revalidate the structural mappings onto Anneal's four `trusted/lean/`
primitives after any change to Anneal's kernel interface, inspect and re-check
the Lean 4 mechanizations in:

```console
lean reports/anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey/support/MorphismAdmissibility.lean
lean reports/anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey/support/ProofGatedCompilationAndTrustPolicy.lean
lean reports/anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey/support/StructuralExternalCallAndCanaries.lean
```

Verify that:
1. `BehaviorCodec` retains `decodeQuery_encodeQuery`, `decodeOut_encodeOut`,
   `encodeOut_of_decodeOut`, and `obs_decodeOut` with `Option`-valued `decodeOut`
   (required for non-malleable parsers in Category 6.5, ZK range checks in
   Category 6.3, randomness couplings in Category 6.2, and post-return secret
   erasure in Category 6.6);
2. `Compiles` and `ProductiveOn` remain paired with `InhabitedPre` (required for
   ZK soundness + completeness in Category 6.3 and non-vacuous CT/parser/WCET
   synthesis in Categories 6.1, 6.4, and 6.5);
3. `EventualBehaviorOf` and `StepResult.externalCall` preserve fuel-independent
   step dilation and pre-call `boundaryInv` enforcement (required for oracle
   queries in Category 6.2, zkVM precompiles in Category 6.3, and FFI/callback
   isolation in Category 6.6); and
4. `VerificationResult` continues to enforce positive per-obligation waiver
   disjunction (`ob.id ∈ waived ∨ ob.prop`).

*Authored by an AI agent acting on joshlf's behalf.*

### Part II Revalidation — Historical Verification Failures

To revalidate the architectural guarantees linking these historical failure modes
to Anneal's codebase when `trusted/lean/` or `theory/` evolves:

1. **Codec Injectivity & Non-Malleability Check (`PartialBehaviorCodec`):**
   Verify that any `PartialBehaviorCodec` used for wire formats, multi-limb
   field arithmetic, or ZKP witness decoding retains `encode_of_decode_some`
   (injectivity on `some`) and `decode_encode_out` by running the Lean 4 kernel
   over `reports/anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey/support/BehaviorCodecExpressiveness.lean`:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey/support/BehaviorCodecExpressiveness.lean
   ```
2. **Re-Entrant External Call & Target Guard Canary Check
   (`StepResult.externalCall` & `BoundaryCanarySuite`):**
   Verify that mid-call invariant violations (`KRACK`/`ed25519-dalek`/`Frozen
   Heart` pattern) and target x86-64 division/stack-overflow guards remain
   refuted by running:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey/support/StructuralExternalCallAndCanaries.lean
   ```
3. **Scoped Assumption Isolation Check (`ScopedVerificationResult`):**
   Verify that waiving a hardware side-channel or cryptographic hardness
   assumption (`GoFetch` DMP, `Hertzbleed` DVFS, or LWE/KZG) cannot explode
   unwaived obligations via `False.elim`:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey/support/ProofGatedCompilationAndTrustPolicy.lean
   ```
