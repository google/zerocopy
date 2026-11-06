# Real-World Verification Tools and Historical Failure Postmortems Across Databases, Storage, Distributed Systems, Networking, Cloud Infrastructure, Authorization, Build Systems, and Tensor Compilers

## Summary

### Part I — Real-World Verification, Synthesis, and Compilation Tool Landscape

Anneal's trusted refinement core (`trusted/lean/Trusted/Refinement.lean` and
`trusted/lean/Trusted/StepResult.lean` at
`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`, together with the
hardened boundary extensions mechanized in
`joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`) isolates four
orthogonal verification primitives:

1. **Defined-vs.-UB Partial Behavior Spine (`Language`, `Partial`, `SemObs`):**
   `Partial B` constructively lifts outcome predicates `Out → Prop` with
   `defined : Prop` and `val : defined → B` (`Partial.ub` as the top element
   $\top$ where `defined = False`), paired with an observational spine
   `obs : Out → SemObs` that separates semantic outcomes from concrete
   representation details.
2. **Bidirectional Representation Coupling and Pass Polarity
   (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, `Abstracts`):**
   `Compiles L_src L_tgt π_c s t` (`L_tgt.sem t ≤ π_c (L_src.sem s)`) shrinks
   nondeterminism and preserves definedness forward, while
   `Abstracts L_v L_src π_v v s` (`L_src.sem s ≤ π_v (L_v.sem v)`) reflects
   UB-freedom backward from an abstract verifier model `v` to a concrete
   artifact `s`. `PartialBehaviorCodec` enforces query retraction
   (`decodeQuery_encodeQuery`), partial outcome bijection (`decode_encode_out`,
   `encode_of_decode_some`), and spine preservation (`obs_decodeOut`), rejecting
   degenerate morphisms (`π_top`, `π_chaosPure`, `π_stepZero`).
3. **Anti-Vacuity, Variable-Step Progress, and Pre-Call Boundary Framing
   (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`,
   `StepResult.externalCall`):**
   `InhabitedPre` and `ProductiveOn` rule out vacuous preconditions and
   synthetic abort/drop/reject cheats; `EventualBehaviorOf` collapses variable
   $1 \to k$ operational steps without `Classical.choice` or coinduction while
   enforcing all-prefix intermediate safety (`ReachesPrefix`); and
   `StepResult.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)`
   enforces decidable call-site invariants before yielding to demonic
   environmental nondeterminism.
4. **Scoped, Non-Exploding TCB Waiver Envelopes (`VerificationResultOn`,
   `ScopedVerificationResult`, `TrustPolicy`):**
   Positive per-obligation waiver masking (`ob.id ∈ waived ∨ ob.prop`) combined
   with universal `TCBModel` quantification prevents a single unverified rule,
   external solver axiom, or boundary bug in a work-in-progress component from
   exploding into a vacuous proof (`False.elim`) of sibling obligations.

Across **86+ real-world formal verification, synthesis, and certifying
compilation tools** spanning **10 non-ISA systems domains**—(1) SQL/Datalog
query equivalence and incremental view maintenance, (2) crash-consistent storage
engines, (3) distributed consensus and transactions, (4) SDN/P4 data planes and
BGP routing, (5) cloud Infrastructure-as-Code and Kubernetes reconciliation
controllers, (6) authorization engines (`Cedar`, `Zanzibar`, `OPA`) and
differential privacy, (7) hermetic build systems and incremental computation,
(8) ML/tensor/polyhedral compilers and GPU kernel verifiers, (9) streaming
watermarks and verified lexer/regex/parser compilers, and (10) binary wire
schemas, bi-directional lenses, and durable execution workflows—every domain
independently rediscovered domain-specific fragments of these four primitives.
Where real-world tools rely on unverified SMT encodings, whole-system Coq/Dafny
monoliths, or partial-correctness checks vulnerable to degenerate "abort-all /
drop-all / deny-all / hold-watermark-forever" implementations, instantiating
Anneal's four primitives provides a uniform, kernel-checked foundation that
accepts untrusted external solvers and LLM-synthesized certificates in
`theory/` while keeping the domain TCB minimal.

### Part II — Historical Verification, Compiler, and Operational Failure Postmortems

Across eight non-traditional systems domains—relational query optimizers and
incremental view maintenance (SQL/DBSP), crash-consistent storage engines,
distributed consensus and transaction protocols, Kubernetes reconciliation
controllers, programmable network data/control planes (P4/BGP), cloud
authorization and differential privacy engines (`Cedar`/`OpenDP`), hermetic and
incremental build systems (`Bazel`/`Ninja`/`Salsa`), and deep-learning tensor
compilers (`XLA`/`TVM`/`Triton`/`Halide`)—historical postmortems, differential
fuzzing campaigns, and formal verification errata reveal that severe bugs
rarely arise from isolated arithmetic mistakes inside already-verified pure
kernels. Instead, historical failures cluster around four structural seams at
the boundary between specification, lowering, environment interaction, and
partial verification:

1. **Silent semantic drift across three-valued partiality, multiset
   multiplicity, and representation decoding (`Language SemObs`, `Partial`, and
   `BehaviorCodec`):**
   - In relational databases (`PostgreSQL`, `MySQL`, `CockroachDB`, `SQLite`,
     `TiDB`, `Apache Calcite`, `Spark SQL`), `SQLancer`'s Ternary Logic
     Partitioning (`TLP`, OOPSLA 2020) and Non-Optimizing Reference Engine
     Construction (`NoREC`, ESEC/FSE 2020) uncovered hundreds of silent
     wrong-result bugs where query rewrite passes conflated Kleene three-valued
     `UNKNOWN` (`NULL`) with boolean `FALSE`, dropped duplicate rows under bag
     semantics, or pushed unguarded division/cast expressions below filters.
     Similarly, early SQL equivalence provers (`Cosette`, CIDR/PLDI 2017; `UDP`,
     VLDB 2018) hit expressiveness boundaries on `NULL` three-valued semantics,
     outer joins, and window functions while exposing classic `COUNT(*)`
     empty-group aggregation bugs (such as the Kim 1982 nested-query rewrite
     bug).
   - In programmable networks, `Gauntlet` (OSDI 2020) and `Petr4` (POPL 2021)
     uncovered 96 distinct bugs (62 crashes and 34 silent miscompilations) in
     `p4c`, `BMv2`, and the Barefoot Tofino compiler, driven by out-of-order
     side-effect hoisting in match-action table keys and unvalidated header
     validity bits (`isValid()`).
   - In tensor compilers, `Tzer` (ISSTA 2022), `NNSmith` (ASPLOS 2023), and
     production `XLA GSPMD` / `Triton` bug trackers document silent numerical
     corruptions caused by omitted `AllReduce` collectives across sharded device
     meshes, out-of-bounds polyhedral halo loads in `Halide`/`TVM`, and
     shared-memory (`smem`) race conditions under asynchronous GPU barriers
     (`mbarrier`).
   - **Architectural lesson for Anneal:** Separating `defined : Prop` from
     `Partial.ub` (`Trusted/Refinement.lean`) and anchoring `BehaviorCodec` with
     `Option`-valued outcome decoding (`decodeOut : L₂.Out → Option L₁.Out`) and
     semantic spine preservation (`obs_decodeOut : L₂.obs o₂ = L₁.obs o₁`)
     prevents optimizers from introducing new traps on dead paths, erasing
     multiset multiplicities, reading invalid P4 header bits, or leaving TPU/GPU
     mesh shards unreduced (`decodeOut = none`).

2. **Degenerate "vacuous safety" implementations and non-terminating control
   loops (`ProductiveOn`, `InhabitedPre`, and `EventualBehaviorOf`):**
   - A transaction manager that aborts 100% of transactions trivially satisfies
     Strict Serializability; a firewall compiler that emits `DROP ALL` trivially
     satisfies tenant isolation; an authorization residual filter that returns
     `Deny` on every row trivially prevents data leaks; a streaming engine
     (`Apache Flink`) that holds watermarks at $-\infty$ forever never emits
     wrong window aggregates; and a Kubernetes operator that returns
     `RequeueAfter(∞)` never performs an unsafe state transition.
   - Conversely, systems that perform variable-step ($1 \to k$) convergence can
     diverge into permanent oscillation or exponential backtracking: BGP route
     reflection combined with Multi-Exit Discriminator (`MED`) attributes forms
     Griffin-Shepherd-Wilf *Dispute Wheels* that oscillate forever (`RFC 3345`);
     competing Kubernetes operators enter infinite reconciliation livelocks
     (`Sieve`, OSDI 2022; `Anvil`, OSDI 2024); `Salsa` incremental query engines
     in `rust-analyzer` panic on dynamically formed dependency cycles; and
     backtracking NFA regex engines caused global production outages at
     `Stack Overflow` (July 20, 2016; 34 minutes) and `Cloudflare` (July 2,
     2019; 27 minutes, 82% global traffic drop) via $O(2^N)$ catastrophic
     backtracking (`ReDoS`).
   - **Architectural lesson for Anneal:** Pairing `InhabitedPre` and
     `ProductiveOn` with fuel-internalized `EventualBehaviorOf`
     (`anneal-behavior-codec-and-progress-refinement-2026`) forces positive
     progress on valid inputs, verifies both all-prefix intermediate safety
     (`∀ n <= k, isSafe`) and finite-step convergence (`.terminated`), and
     refutes non-terminating BGP Dispute Wheels, Kubernetes livelocks, and
     unbounded backtracking without requiring coinduction or `Classical.choice`.

3. **Unchecked environment boundaries, stale caches, and hardware reorderings
   (`StepResult.externalCall`):**
   - Verified storage systems (`FSCQ`, SOSP 2015; `Yggdrasil`, OSDI 2016)
     experienced real bugs in their unverified FUSE/C shims and relied on disk
     barrier models where omitting a Force Unit Access (`FUA`) or `fsync`
     barrier before overwriting metadata causes power-loss corruption; in LSM
     storage engines (`RocksDB` `DeleteRange` issues `#4747`, `#4760`, `#5616`,
     `#7703`), compacting and dropping a range tombstone above an active
     snapshot or lower SSTable level resurrects deleted keys.
   - In Kubernetes controllers, reading from a lagging local informer cache
     creates time-of-check-to-time-of-use (`TOCTOU`) races (`Sieve` OSDI 2022;
     `Anvil` OSDI 2024) where a controller overwrites newer `etcd` state or
     leaks orphan cloud resources after partial API failures.
   - In differential privacy libraries (`OpenDP`, `Diffprivlib`, `Chorus`),
     implementing real-valued Laplace/Gaussian noise and sum aggregations in
     IEEE-754 floating-point arithmetic without boundary rounding/sensitivity
     guards enabled Mironov's least-significant-bit (`LSB`) reconstruction
     attack (CCS 2012) and Casacuberta et al.'s widespread sensitivity
     underestimation attacks (CCS 2022).
   - In build systems (`Bazel`, `Ninja`), spawning a compiler subprocess whose
     sandbox mounts header files or environment variables omitted from the
     content-addressed `ActionKey` digest causes persistent remote cache
     poisoning.
   - **Architectural lesson for Anneal:** Modeling every I/O, RPC, cache read,
     CSPRNG sample, and subprocess spawn via `StepResult.externalCall
     (boundaryInv : Bool) (branches : State → Obs → Prop)`
     (`anneal-structural-external-calls-and-tcb-mutation-testing-2026`) checks
     caller-side boundary invariants (`flushedLSN >= pageLSN`,
     `tombstone.seq <= earliest_snapshot`, `resourceVersion` preconditions,
     `sandboxMounts ⊆ hashedInputs`, and discrete DP budget/sensitivity bounds)
     before exposing execution to demonic environment nondeterminism.

4. **Pointwise contradiction and partial-waiver contamination
   (`VerificationResult`, `ScopedVerificationResult`, and `TrustPolicy`):**
   - When a complex system (such as a 150-rule SQL optimizer, a multi-pass ML
     compiler waiving IEEE-754 reassociation in `AllReduce`, or an incremental
     build system waiving SHA-256 collision resistance) waives an unproven rule
     by placing a concrete assumption on the left-hand side of an implication
     (`→`), any edge-case bug in the waived rule makes the antecedent `False`
     and discharges every other obligation in the system by `False.elim`.
   - **Architectural lesson for Anneal:** Positive per-obligation consequent
     masking (`ob.id ∈ waived ∨ ob.prop` in `ScopedVerificationResult`, combined
     with universal `TCBModel` quantification in
     `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`)
     isolates waived rules, hardware assumptions, and external solver steps so a
     bug in an unverified rule can never silently certify an adjacent pass.

## Applicability

### Part I — Real-World Verification and Compilation Tools Applicability

This report applies to the subjects recorded in `REPORT.json`:

1. **Anneal trusted core and MIR-to-x86-64 compiler branches:**
   - `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` (`trusted-refinement-core`:
     `trusted/lean/Trusted/Refinement.lean`,
     `trusted/lean/Trusted/StepResult.lean`,
     `theory/Anneal/Refinement.lean`, and `theory/Anneal/StepResult.lean`),
   - `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457` (`x86-backend-pipeline`:
     `trusted/lean/Trusted/X86Semantics.lean`,
     `theory/Anneal/Compiler/NaiveCodegen.lean`, and
     `theory/Anneal/Compiler/Peephole.lean`).
2. **Anneal trusted-boundary hardening corpus:**
   - `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` (`reference`:
     `support/BehaviorCodecExpressiveness.lean`,
     `support/StructuralExternalCallAndCanaries.lean`,
     and
     `support/ProofGatedCompilationAndTrustPolicy.lean`).
3. **Eighty-six external tools, specification languages, and industrial engines
   across ten domains**, evaluated as architectural comparison targets and
   candidate instantiations of Anneal's `trusted/` primitives. The relationship
   among these subjects is comparative and constructive: Anneal's Lean 4
   refinement primitives are interpreted as a unifying meta-framework for the
   specifications, intermediate representations, solver certificates, and TCB
   boundaries of the examined domain tools.

### Part II — Historical Verification and Operational Failures Applicability

This report synthesizes primary-source evidence from the eight subject groups in
`REPORT.json` and maps their failure modes onto Anneal's trusted verification
primitives:

| Subject Group | Primary Sources & Coordinates | Examined Scope |
| :--- | :--- | :--- |
| **Anneal Trusted Core & Extensions** | `joshlf/anneal` at `24367bd1a8c784f2578535954f9915e24894a56f` (`trusted-refinement-core`) and `5fc1139f2208b3c9cfb513573c4a731cc32bb457` (`x86-backend-pipeline`), plus companion 2026 reference reports | `Language`, `Partial`, `BehaviorCodec`, `PartialBehaviorCodec`, `Compiles`, `Abstracts`, `ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, `StepResult.externalCall`, `VerificationResult`, `ScopedVerificationResult`, `TrustPolicy` |
| **SQL Optimizers & `SQLancer`** | Rigger & Su: `NoREC` (`10.1145/3368089.3409710`, ESEC/FSE 2020), `TLP` (`10.1145/3428279`, OOPSLA 2020), `PQS` (OSDI 2020); `sqlancer/sqlancer` | Silent wrong-result bugs in `PostgreSQL`, `MySQL`, `CockroachDB`, `SQLite`, and `TiDB` involving Kleene 3VL `NULL`, joins, predicates, and aggregates |
| **SQL Equivalence & IVM (`Cosette`, `UDP`, `WeTune`, `DBSP`)** | Chu et al. `Cosette` (CIDR/PLDI 2017) & `UDP` (`10.14778/3192965.3192971`, VLDB 2018); Wang et al. `WeTune` (`10.1145/3514221.3526125`, SIGMOD 2022); Budiu et al. `DBSP` (`10.14778/3587136.3587137`, VLDB 2023) | Automated SQL rewrite verification boundaries, `COUNT` / bag-vs-set bugs, correlated subquery unnesting, and streaming $\mathbb{Z}$-set / watermark retractions in `Materialize` and `Apache Flink` |
| **Storage & Consensus (`FSCQ`, `Yggdrasil`, `RocksDB`, `Jepsen`/`Elle`)** | Chen et al. `FSCQ` (`10.1145/2815400.2815402`, SOSP 2015); Sigurbjarnarson et al. `Yggdrasil` (OSDI 2016); `facebook/rocksdb` `DeleteRange`; Kingsbury & Alvaro `Elle` (`10.14778/3457390.3457396`, VLDB 2020); Ongaro `Raft` (ATC 2014 / PhD 2014) | Unverified C/FUSE shims, disk barrier reorderings, LSM range-tombstone compaction drops, Raft Figure 8 & membership-change bugs, and distributed isolation anomalies in `CockroachDB`, `TiKV`, and `MongoDB` |
| **Kubernetes Controllers (`Sieve`, `Anvil`)** | Sun et al. `Sieve` (OSDI 2022); Sun et al. `Anvil` (OSDI 2024) | Stale informer-cache TOCTOU races, non-idempotent API retries, orphan resource leaks, and reconciliation livelocks in Kubernetes operators |
| **Networking (`Gauntlet`, `Petr4`, `BGP RFC 3345`)** | Ruffy et al. `Gauntlet` (`arXiv:2006.01074`, OSDI 2020); Doenges et al. `Petr4` (`10.1145/3434304`, POPL 2021); Griffin, Shepherd & Wilf (ICNP/SIGCOMM 1999); McPherson et al. `RFC 3345` (2002) | 96 compiler/semantic bugs in `p4c`, `BMv2`, and Barefoot Tofino; P4-16 specification undefined behaviors; BGP route-reflection / MED Dispute Wheel oscillations |
| **Cloud IAM & Differential Privacy (`Cedar`, `Mironov`, `Casacuberta`)** | Cutler et al. `Cedar` (`arXiv:2403.04651`, OOPSLA 2024); Mironov (`10.1145/2382196.2382264`, CCS 2012); Casacuberta et al. (`10.1145/3548606.3560708`, CCS 2022) | Pre-release validator and evaluator bugs caught by Lean 4 proofs and DRT in AWS `Cedar`; IEEE-754 LSB and sensitivity-underestimation attacks in `OpenDP`, `Diffprivlib`, and `Chorus` |
| **Build Systems, Tensor Compilers & `ReDoS`** | Erdweg et al. `Pluto` (`10.1145/2814270.2814316`, OOPSLA 2015); Mokhov et al. `Build Systems à la Carte` (`10.1145/3236774`, ICFP 2018); Liu et al. `Tzer` (`10.1145/3533767.3534388`, ISSTA 2022) & `NNSmith` (`10.1145/3575693.3575707`, ASPLOS 2023); `Cloudflare` (2019) & `Stack Overflow` (2016) postmortems | Dynamic dependency and remote-cache poisoning in `Bazel`/`Ninja`/`Salsa`; miscompilations in `XLA GSPMD`, `Triton`, `TVM`, and `Halide`; catastrophic regex backtracking outages |

The architectural mappings in this report apply whenever Anneal's `trusted/lean/`
primitives are used to verify domain-specific compilers, query optimizers,
storage engines, distributed controllers, policy evaluators, or incremental
build systems, as well as to Anneal's own Rust/Lean compilation and caching
infrastructure.

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

### 0. Structural Cross-Walk of Anneal's Four Trusted Primitives

`Basis: source + execution + derived`

In `trusted/lean/Trusted/Refinement.lean` (lines 241–471 at
`24367bd1a8c784f2578535954f9915e24894a56f`) and `trusted/lean/Trusted/StepResult.lean`
(lines 58–198), coupled with the mechanized hardening modules in
`joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`, every verification
or compilation pipeline is governed by four orthogonal mechanisms:

- **Primitive 1 (`Language`, `Partial`, `SemObs`):**
  `Behavior Query Out := Query → Partial (Out → Prop)` separates whether an
  execution is well-defined (`defined : Prop`, where `defined = False` is
  `Partial.ub`) from what outcomes it may produce (`val : defined → Out → Prop`).
  Equipping `Language` with an observational projection `obs : Out → SemObs`
  ensures that concrete target states are compared along a canonical semantic
  spine.
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`,
  `Abstracts`):**
  `Compiles L_src L_tgt π_c s t` (`L_tgt.sem t ≤ π_c (L_src.sem s)`) and
  `Abstracts L_v L_src π_v v s` (`L_src.sem s ≤ π_v (L_v.sem v)`) compose
  transitively via `Preorder.le_trans` (`pass_trans`, `Compiles.comp`,
  `Abstracts.comp` in `theory/Anneal/Refinement.lean:185-223`). Constraining
  `π` to be induced by a `PartialBehaviorCodec L₁ L₂` (`encodeQuery`,
  `decodeQuery`, `encodeOut`, `decodeOut : L₂.Out → Option L₁.Out`, with
  `decodeQuery_encodeQuery`, `decode_encode_out`, `encode_of_decode_some`, and
  `obs_decodeOut`) prevents morphism degeneracy while rejecting invalid target
  encodings (`decodeOut o₂ = none`).
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`,
  `StepResult.externalCall`):**
  `InhabitedPre pre` (`∃ q, pre q`) prevents vacuous domain constraints;
  `ProductiveOn pre p` forces at least one valid outcome (`decodeOut o₂ = some o₁`)
  on every query in `pre`; `EventualBehaviorOf` (`support/BehaviorCodecExpressiveness.lean`
  at `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`) existentially quantifies finite step budgets `steps : Nat`
  inside `Out` while preserving all-prefix safety
  (`eventual_wellFormed_iff_prefix_wellFormed`); and
  `StepResult.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)`
  (`support/StructuralExternalCallAndCanaries.lean:148-236`) steps immediately
  to `.failed` if `boundaryInv = false` before branching demonically over
  `next`.
- **Primitive 4 (`VerificationResultOn`, `ScopedVerificationResult`,
  `TrustPolicy`):**
  `ScopedVerificationResult` (`support/ProofGatedCompilationAndTrustPolicy.lean`
  at `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`) checks `AllHold (waived.map policy.isAllowed)` and
  evaluates each obligation `ob` positively as `ob.id ∈ waived ∨ ob.prop` under
  universal `TCBModel` quantification, preventing antecedent `False.elim`
  explosion.

---

### 1. Domain 1: Relational, Graph, and Datalog Query Equivalence and Incremental View Maintenance (SQL / Substrait / DBSP)

`Basis: documentation + source + derived`

#### 1.1 Domain Problem Space and Tool Families

Relational, graph, and Datalog query engines transform declarative queries
through hundreds of algebraic rewrite rules, subquery decorrelation passes
(Neumann-Kemper unnesting), predicate pushdowns, join reorderings, and
incremental view maintenance (IVM) differentiation passes. Three semantic
hazards dominate industrial query optimizers:

1. **Three-valued Kleene `NULL` logic (`TRUE`, `FALSE`, `UNKNOWN`):** Pushing a
   filter past an `OUTER JOIN` or rewriting `x NOT IN (SELECT y ...)` into an
   anti-join alters results whenever `y` contains `NULL`.
2. **Bag (multiset) vs. set multiplicity:** Pushing `DISTINCT`, commuting
   projections with joins, or applying magic-set rewrites without tracking
   tuple multiplicities ($\text{Tuple} \to \mathbb{N}$ or $\mathbb{Z}$-sets)
   duplicates or drops rows.
3. **Evaluation-order traps and non-monotone IVM drift:** Pushing an arithmetic
   expression `100 / x > 5` or `CAST(s AS INT)` below a guard `WHERE x <> 0`
   triggers runtime division-by-zero traps on dead tuples; in streaming IVM,
   incorrectly differentiating non-monotone operators (`EXCEPT`, `GROUP BY`
   having empty groups, recursive Datalog negation) causes incremental state to
   drift from $Q(I + \Delta I)$.

#### 1.2 Exhaustive Tool Deep-Dives (15 Core Tools + Adjacent Systems)

1. **`Cosette` (`uwdb/Cosette`, Chu et al., CIDR / SIGMOD 2017, DOI
   `10.1145/3035918.3056447`) and `HoTTSQL` (`uwdb/HoTTSQL`, POPL 2017, DOI
   `10.1145/3009837.3009848`):**
   - *(1) Goals & Users:* Automated prover and bounded counterexample finder for
     SQL query equivalence used by database researchers and compiler writers.
   - *(2) History & Lineage:* Developed at the University of Washington by
     Shumo Chu, Konstantin Weitz, Alvin Cheung, and Dan Suciu.
   - *(3) Design Philosophy & Tradeoffs:* Dual-engine architecture combining bounded
     symbolic execution in Rosette/Z3 (for fast counterexample generation over
     small relation bounds) with mechanized $K$-relation semiring proofs in Coq
     (`HoTTSQL`, using Homotopy Type Theory univalence to identify isomorphic
     tuple schemas).
   - *(4) Ecosystem Comparison:* Unlike SMT-only tools (`EQUITAS`, `SPES`, `Qex`),
     `HoTTSQL`/`Cosette` produces unbounded machine-checked proofs in Coq for
     conjunctive queries and unions, but struggles to automate correlated
     three-valued `NULL` semantics and complex aggregations without manual
     tactics.
   - *(5) Formal Theory & TCB:* Semiring $K$-relations ($R : \text{Tuple} \to K$,
     where $K = \mathbb{N}$ models bag semantics and $K = \mathbb{B}$ models set
     semantics). The proof track trusts the Coq kernel plus the unverified SQL
     parser translating SQL strings into Coq ASTs; the Rosette track trusts
     Racket, Rosette, and Z3 up to a finite tuple bound.

2. **`UDP` (Unified Decision Procedure / U-Expressions, Chu et al., VLDB 2018,
   DOI `10.14778/3236187.3236200`):**
   - *(1) Goals & Users:* Decide equivalence of SQL queries mixing set and bag
     semantics, integrity constraints (primary/foreign keys), and materialized
     views.
   - *(2) History & Lineage:* Direct successor to `HoTTSQL` at UW, extending
     $K$-relations with explicit summation $\sum_{t} e(t)$ and squash `‖e‖`
     (set-projection) operators called **U-expressions**.
   - *(3) Design Philosophy & Tradeoffs:* Normalizes two queries into canonical
     U-expressions and checks isomorphism of bound tuple variables via SMT
     (Lean 3 / Coq / Z3).
   - *(4) Ecosystem Comparison:* Strictly generalizes `Cosette` to integrity
     constraints and mixed set/bag queries; adopted as the theoretical core of
     `WeTune`.
   - *(5) Formal Theory & TCB:* Commutative semiring with idempotent squash
     operator; mechanized core metatheory in Coq/Lean 3, with an SMT solver in
     the decision loop for variable-bijection search.

3. **`EQUITAS` (`georgia-tech-db/equitas`, Zhou et al., SIGMOD 2019, DOI
   `10.1145/3299869.3319869`) and `SPES` (`georgia-tech-db/spes`, Zhou et al.,
   ICDE 2022, DOI `10.1109/ICDE53745.2022.00201`):**
   - *(1) Goals & Users:* Symbolic push-button SQL equivalence verifiers built
     at Georgia Tech (Qi Zhou, Joy Arulraj, Shamkant Navathe, William Harris)
     for auditing industrial query optimizers (Apache Calcite, PostgreSQL,
     MySQL).
   - *(2) History & Lineage:* `EQUITAS` (2019) modeled SQL under set semantics
     with 3-valued `NULL`s via first-order SMT constraints; `SPES` (2022)
     extended symbolic representation to **bag semantics** by encoding
     algebraic queries into canonical Symbolic Query Pair (`SQP`) normal forms
     and checking the existence of a bijective identity mapping between output
     tuple multisets in Z3.
   - *(3) Design Philosophy & Tradeoffs:* Trades foundational proof-assistant
     certificates for 100% push-button Z3 automation over 3-valued `NULL`s,
     outer joins, and aggregations.
   - *(4) Ecosystem Comparison:* Faster and broader on `NULL`/outer-join corner
     cases than `Cosette`, but unverified: a bug in `SPES`'s Java normalization
     rules or Z3 encoding silently yields false positives.
   - *(5) Formal Theory & TCB:* Entire Java symbolic normalizer, Calcite SQL
     parser, and Z3 SMT solver sit inside the TCB.

4. **`Qex` (Symbolic SQL Query Explorer, Veanes et al., LPAR 2010, DOI
   `10.1007/978-3-642-17511-4_24`):**
   - *(1) Goals & Users:* Microsoft Research tool for symbolic execution and
     test-input generation of parameterized `.NET`/T-SQL queries.
   - *(2) History & Lineage:* Built by Margus Veanes, Nikolaj Bjørner, and
     Nikolai Tillmann using the Z3 theory of lists, bags, and bitvectors.
   - *(3) Design Philosophy & Tradeoffs:* Bounded symbolic table instantiation
     for finding concrete database instances $D$ where $Q_1(D) \ne Q_2(D)$ or
     where $Q(D)$ satisfies coverage targets.
   - *(4) Ecosystem Comparison:* Predecessor to `Cosette`'s Rosette backend;
     bounded falsifier rather than an unbounded equivalence prover.
   - *(5) Formal Theory & TCB:* Z3 SMT solver and `.NET` T-SQL translator.

5. **`WeTune` (`we-tune/WeTune`, Wang et al., SIGMOD 2022, DOI
   `10.1145/3514221.3526125`) and `SlabCity` (Dong et al., SIGMOD 2023, DOI
   `10.1145/3589297`):**
   - *(1) Goals & Users:* Automated rule synthesis (`WeTune`) and rule-free
     whole-query dataflow synthesis (`SlabCity`) for discovering missing
     optimizations in PostgreSQL, SQL Server, MySQL, and Calcite.
   - *(2) History & Lineage:* Developed at SJTU / Alibaba / UMich (`WeTune`)
     and CUHK (`SlabCity`). `WeTune` enumerates algebraic plan templates up to a
     small size bound and invokes a `UDP`-based U-expression SMT prover to
     discover 200+ verified rewrite rules; `SlabCity` bypasses local rewrite
     rules entirely by synthesizing equivalent whole-query dataflows via
     bounded counterexample-guided inductive synthesis (CEGIS) and verifying
     candidates with an SMT solver.
   - *(3) Design Philosophy & Tradeoffs:* Shifts human effort from authoring
     optimizer rules to specifying semantics; however, both rely on uncertified
     SMT encodings for rule admission.
   - *(4) Ecosystem Comparison:* Directly addresses the "rule coverage gap" in
     hand-written optimizers (`CockroachDB optgen`, `Apache Calcite`).
   - *(5) Formal Theory & TCB:* U-expression / FOL SMT encoding + Z3 solver.

6. **`DataCert` (`datacert/datacert`, Benzaken, Contejean, Stefanesco, ESOP
   2014 / CPP 2017) and `QCert` (`querycert/qcert`, Auerbach et al., SIGMOD
   2017, DOI `10.1145/3035918.3056101`):**
   - *(1) Goals & Users:* Foundational Coq-verified relational database engines
     (`DataCert`) and nested-relational / JSON / OQL / SQL query compilers
     (`QCert`, IBM Research & INRIA).
   - *(2) History & Lineage:* `DataCert` mechanized relational algebra, bag
     semantics, `NULL`s, and SQL-to-algebra compilation in Coq; `QCert` built a
     20-tier verified compiler pipeline (NRA$^e$, NNRC, Cloudant MapReduce,
     Spark RDDs) in Coq extracted to OCaml.
   - *(3) Design Philosophy & Tradeoffs:* Full CompCert-style verified
     compilation (`∀ D, eval_target (compile Q) D = eval_source Q D`) inside
     Coq. High assurance, but writing new optimization passes requires manual
     Coq proofs over the compiler implementation rather than external e-graph
     certificate checking.
   - *(4) Ecosystem Comparison:* Gold standard for foundational TCB minimization
     in query compilation prior to Lean 4 certificate checking.
   - *(5) Formal Theory & TCB:* Nested Relational Calculus (NRC) and
     Nested Relational Algebra with Environments (NRA$^e$); TCB is the Coq
     kernel and OCaml extraction.

7. **`DBSP` and `Feldera` (`feldera/feldera`, Budiu et al., PVLDB 16(6) 2023,
   DOI `10.14778/3587136.3587140`) and `Materialize` (`MaterializeInc/materialize`):**
   - *(1) Goals & Users:* Real-time Incremental View Maintenance (IVM) engines
     that compile arbitrary SQL (including recursive CTEs, outer joins, nested
     aggregations, and window functions) into streaming incremental dataflow
     circuits.
   - *(2) History & Lineage:* `Materialize` (founded by Frank McSherry and Arjun
     Narayan) pioneered commercial SQL IVM over `Differential Dataflow`; `DBSP`
     (created by Mihai Budiu, Frank McSherry, Leonid Ryzhyk, and Val Tannen at
     VMware Research / Feldera) distilled IVM into a clean algebraic calculus
     over streams of $\mathbb{Z}$-sets (abelian groups of tuples with integer
     weights $w \in \mathbb{Z}$, where $w > 0$ represents insertions and $w < 0$
     represents deletions) with delay operator $z^{-1}$, differentiation
     $\mathcal{D}(s)[t] = s[t] - s[t-1]$, integration
     $\mathcal{I}(s)[t] = \sum_{i \le t} s[i]$, and incrementalization
     $Q^\Delta = \mathcal{D} \circ Q \circ \mathcal{I}$.
   - *(3) Design Philosophy & Tradeoffs:* Every relational operator is reduced to
     primitive bilinear, linear, and stateful stream operators over commutative
     groups. Feldera uses `Apache Calcite` to parse/optimize SQL and compiles it
     to a Rust `dbsp` circuit.
   - *(4) Ecosystem Comparison:* Unlike ad-hoc IVM triggers, `DBSP` has a
     complete compositional mathematical theory (mechanized in Lean 4 /
     Isabelle prototypes by the DBSP authors), though Feldera's production
     Calcite-to-Rust compiler is not proof-carrying per query.
   - *(5) Formal Theory & TCB:* Commutative $\mathbb{Z}$-modules, stream derivative/integral
     bijection ($\mathcal{D}(\mathcal{I}(s)) = s$), and bilinearity of joins
     ($(a \bowtie b)^\Delta = a^\Delta \bowtie b^\Delta + z^{-1}(a) \bowtie b^\Delta + a^\Delta \bowtie z^{-1}(b)$).

8. **Industrial & Educational Optimizer Infrastructures: `CockroachDB optgen`
   (`cockroachdb/cockroach`, Taft et al., SIGMOD 2020), `Apache Calcite`
   (`apache/calcite`, Begoli et al., SIGMOD 2018), `RisingLight`
   (`risinglightdb/risinglight`, e-graph `egg` optimizer), `Soufflé`
   (`souffle-lang/souffle`, Jordan et al., CAV 2016), plus `Spark Catalyst` and
   `DuckDB`:**
   - *(1) Goals & Users:* Production query planning, cost-based Volcano/Cascades
     search, equality saturation (`RisingLight` with `egg`), and Datalog-to-C++
     semi-naive compilation (`Soufflé`).
   - *(2) Design Philosophy & Tradeoffs:* `optgen` compiles declarative
     pattern-match/replace DSL files into Go optimizer code; `Calcite` provides
     Java `RelNode` Volcano/Hep planners; `RisingLight` uses Rust `egg` equality
     saturation; `Soufflé` compiles Datalog via Magic Sets and semi-naive
     evaluation ($\Delta R_{i+1} = F(R_i, \Delta R_i) \setminus R_i$) into
     parallel C++ B-tree/Brie loops. None of these production optimizers verify
     rule soundness mechanically, leading to recurring Kleene-3VL, `OUTER JOIN`,
     and guard-pushdown bugs.

#### 1.3 Mapping Domain 1 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Rel.Prog`: SQL AST, Substrait plan, or stratified Datalog program;
    `L_Phys.Prog`: vectorized physical plan or DBSP $\mathbb{Z}$-set circuit.
  - `Query`: Database catalog instance $D$ (or stream of $\mathbb{Z}$-set deltas
    $[\Delta D_0, \dots, \Delta D_T]$) plus session parameters.
  - `SemObs` (`obs : Out → SemObs`): Canonical multiset (`Tuple → Int`) or
    ordered sequence of output rows paired with completion status
    (`.committed rows` vs. `.aborted err`).
  - `Partial.ub` (`defined = False`): Out-of-bounds physical tuple-slot access,
    unstratified Datalog negation oscillation, or **evaluation-order traps**
    (division by zero `1 / 0` or invalid `CAST` introduced by pushing a filter
    below its guard). Because `Compiles` requires
    `(L_Rel.sem Q D).defined → (L_Phys.sem P D).defined`, any rewrite rule (in
    `optgen`, `Calcite`, or `WeTune`) that pushes an unguarded `1 / x` below
    `WHERE x <> 0` flips `defined` from `True` to `False` on databases
    containing `x = 0` and is immediately rejected by Lean!
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `PartialBehaviorCodec L_Rel L_Phys`: `encodeQuery` / `decodeQuery` relates
    logical relations to physical Arrow columnar batches or B-tree pages;
    `decodeOut` reconstructs the logical multiset and returns `none` if Arrow
    validity bitmaps or sort orders are violated. For `DBSP`/`Feldera`,
    `encodeQuery` differentiates a sequence of database snapshots into
    $\mathbb{Z}$-set deltas $\mathcal{D}(D)$, and `decodeOut` integrates the
    output delta stream $\mathcal{I}(\Delta O)$, turning the DBSP fundamental
    theorem $\mathcal{I} \circ Q^\Delta \circ \mathcal{D} = Q$ directly into
    `Compiles L_Rel L_DBSP dbspCodec Q Q_delta`!
  - `Abstracts`: Certifies partition pruning and zone-map / MinMax / Bloom
    filtering (`Abstracts L_ZoneMap L_Phys codec ZoneSummary ScanPlan`), proving
    that pruned Parquet row groups contain zero matching tuples.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `InhabitedPre SchemaInv` proves that table `CHECK` and foreign-key
    constraints are mutually satisfiable; `ProductiveOn SchemaInv P_phys` blocks
    the degenerate optimizer cheat of compiling complex joins to
    `return .aborted .outOfMemory`.
  - `EventualBehaviorOf` bridges 1-step relational algebra evaluation with
    $O(N \log N)$ physical sort-merge or semi-naive Datalog fixpoint iterations.
  - `StepResult.externalCall` models Wasm/Python scalar UDFs and Foreign Data
    Wrappers, checking buffer alignment and transaction snapshot locks in
    `boundaryInv`.
- **`VerificationResult` and `TrustPolicy`:**
  - An external `egglog`/`WeTune`/`Calcite` optimizer emits an $N$-step rewrite
    trace. Each step $i$ becomes an obligation `ob_i : Compiles ... plan_i plan_{i+1}`
    in `ScopedVerificationResult`. If 148 standard relational rules are proved
    in Lean over Kleene-3VL multisets and 2 vendor GIS rules (`ST_Intersects`)
    are unproved, `waived := [.rule "ST_Intersects"]` audits the exact waiver
    without tainting the remaining 148 steps.

---

### 2. Domain 2: Crash-Consistent Storage Engines, LSM/B+-Trees, and Write-Ahead Logging

`Basis: documentation + source + derived`

#### 2.1 Domain Problem Space and Tool Families

Storage engines (`RocksDB`, `SplinterDB`, `SQLite` WAL, `WiredTiger`, `Fxfs`)
maintain durable state across asynchronous block devices (`io_uring`, NVMe)
where power loss can occur at any instruction boundary. Unflushed volatile page
caches evaporate, in-flight NVMe writes without `FUA`/`Flush` barriers reorder
or tear, and background LSM compactions or B+-tree node splits must never
resurrect deleted keys (tombstone garbage-collection bugs) or violate the
Write-Ahead Logging (WAL) invariant (`flushedLSN >= pageLSN`).

#### 2.2 Exhaustive Tool Deep-Dives (8 Core Tools + Adjacent Systems)

1. **`FSCQ` (`mit-pdos/fscq`, Chen et al., SOSP 2015, DOI
   `10.1145/2815400.2815402`) and `DFSCQ` (Chen et al., SOSP 2017, DOI
   `10.1145/3132747.3132776`):**
   - *(1) Goals & Users:* First file systems with machine-checked Coq proofs of
     crash safety under arbitrary power failures and crashes during recovery.
   - *(2) History & Lineage:* Built at MIT PDOS by Haogang Chen, Daniel Ziegler,
     Tej Chajed, Adam Chlipala, Frans Kaashoek, and Nickolai Zeldovich.
     Introduced **Crash Hoare Logic (CHL)**, which augments Hoare triples with a
     dedicated `crash_cond` predicate and models asynchronous disk writeback via
     lists of historical block values (`disk : Addr → val × list val`). `DFSCQ`
     added tree-structured `fdatasync` metadata-prefix specifications.
   - *(3) Design Philosophy & Tradeoffs:* Complete interactive verification in
     Coq extracted to Haskell (`FUSE`). High proof burden (~10$\times$ code-to-proof
     ratio) and sequential single-threaded execution model.
   - *(4) Ecosystem Comparison:* Laid the foundation for `Perennial` (concurrent
     crash safety) and `Yggdrasil` (SMT-automated crash refinement).
   - *(5) Formal Theory & TCB:* Crash Hoare Logic in Coq; TCB is the Coq kernel,
     Haskell GHC runtime, FUSE bindings, and disk-model axioms.

2. **`Perennial` (`mit-pdos/perennial`, Chajed et al., SOSP 2019, DOI
   `10.1145/3341301.3359632`), `GoJournal` (OSDI 2021), and `DaisyNFS`
   (`mit-pdos/daisy-nfsd`, Chajed et al., OSDI 2022):**
   - *(1) Goals & Users:* Verify high-performance **concurrent**, crash-safe
     storage systems written in Go (`Goose` subset) and Dafny.
   - *(2) History & Lineage:* Developed at MIT PDOS by Tej Chajed, Joseph
     Tassarotti, Frans Kaashoek, and Nickolai Zeldovich on top of the **Iris**
     higher-order concurrent separation logic in Coq. `DaisyNFS` (OSDI 2022)
     achieved a major architectural breakthrough: it verified the concurrent
     write-ahead journaling transaction manager (`GoTxn`/`GoJournal`) once in
     Perennial/Coq, proved that `GoTxn` exposes an atomic sequential interface to
     callers, and verified the upper NFSv3 file-system operations using
     push-button SMT automation in **Dafny**!
   - *(3) Design Philosophy & Tradeoffs:* Combines foundational concurrent crash
     separation logic (for the subtle lock/WAL kernel) with automated SMT
     verification (for high-level file-system operations).
   - *(4) Ecosystem Comparison:* Directly inspires Anneal's separation between
     foundational `trusted/` operational primitives and automated/external proof
     discharge in `theory/`.
   - *(5) Formal Theory & TCB:* Iris step-indexed crash separation logic (`wpc`
     weakest preconditions with crash modalities) + `Goose` Go-to-Coq translator
     + Dafny/Boogie/Z3 for `DaisyNFS`'s upper layer.

3. **`Yggdrasil` (`uwplse/yggdrasil`, Sigurbjarnarson et al., OSDI 2016,
   `https://www.usenix.org/conference/osdi16/technical-sessions/presentation/sigurbjarnarson`):**
   - *(1) Goals & Users:* "Push-button" Z3-based verification of crash-consistent
     file systems (`Yxv6`, `Yaffs`, `LFSCK`) in Python/C without manual Coq
     proofs.
   - *(2) History & Lineage:* Created at UW by Helgi Sigurbjarnarson, James
     Bornholt, Emina Torlak, and Xi Wang.
   - *(3) Design Philosophy & Tradeoffs:* Introduces **Crash Refinement**: an
     implementation $I$ crash-refines a specification $S$ if for every operation
     and every subset of unflushed disk writes, the set of possible post-crash
     states of $I$ is a subset of $S$'s post-crash states. Restricts Loops to
     bounded unrolling so Rosette/Z3 can decide refinement automatically.
   - *(4) Ecosystem Comparison:* Orders of magnitude lower proof effort than
     `FSCQ`, at the cost of restricting implementation structures to finitary
     symbolic paths and trusting Python/Rosette/Z3.
   - *(5) Formal Theory & TCB:* Set-inclusion crash refinement ($I \sqsubseteq_{\text{crash}} S$);
     TCB includes Python symbolic interpreter, LLVM backend, and Z3.

4. **`VeriBetrKV` (`secure-foundations/veribetrkv-osdi2020`, Hance et al., OSDI
   2020, `https://www.usenix.org/conference/osdi20/presentation/hance`):**
   - *(1) Goals & Users:* High-performance, crash-safe $B^\epsilon$-tree
     key-value store verified in Dafny (and later ported to Linear Dafny /
     Verus) that outperforms unverified `RocksDB` on write-heavy workloads.
   - *(2) History & Lineage:* Built by Travis Hance, Andrea Lattuada, Chris
     Hawblitzel, Jon Howell, Rob Johnson, and Bryan Parno (CMU, VMware Research,
     MSR).
   - *(3) Design Philosophy & Tradeoffs:* Organizes verification as a layered
     refinement stack of state machines (`MapSpec` $\to$ `Betree` $\to$
     `PagedBetree` $\to$ `PivotBetree` $\to$ concrete cache/disk implementation
     with linear memory management).
   - *(4) Ecosystem Comparison:* Demonstrates that multi-layer state-machine
     refinement scales to complex write-optimized $B^\epsilon$-tree compaction
     and journal replay.
   - *(5) Formal Theory & TCB:* TLA-style state-machine refinement checked via
     Dafny/Boogie/Z3 and compiled to C++.

5. **`Cogent` and `BilbyFS` (`NICTA/cogent`, Amani et al., ASPLOS 2016, DOI
   `10.1145/2872362.2872404`):**
   - *(1) Goals & Users:* Co-generate efficient C code and Isabelle/HOL
     equational specifications for Linux file systems (`BilbyFS` raw flash file
     system, `ext2`).
   - *(2) History & Lineage:* Developed at Data61 / UNSW Sydney (Sidney Amani,
     Alex Hixon, Zilin Chen, Christine Rizkallah, Toby Murray, Gerwin Klein).
   - *(3) Design Philosophy & Tradeoffs:* Restricted uniqueness/linear type
     system without recursion or garbage collection; the compiler emits an
     Isabelle/HOL refinement certificate proving the generated C refines the
     pure functional Cogent semantics.
   - *(4) Ecosystem Comparison:* Like Anneal, `Cogent` uses **certifying
     compilation** (generating a per-program theorem in Isabelle/HOL) rather
     than verifying the compiler once and for all.
   - *(5) Formal Theory & TCB:* Linear type system + AutoCorres C-to-Isabelle
     parser + Isabelle/HOL kernel.

6. **`Flashix` (Schellhorn, Pfähler, Bodenmüller, Reif et al., IEEE TSE 2020 /
   ABZ, Univ. Augsburg):**
   - *(1) Goals & Users:* Mechanically verified POSIX-compliant flash file
     system (wear leveling, erase-block garbage collection, UBIFS-style index
     wandering trees, and crash recovery) in the **KIV** interactive theorem
     prover.
   - *(3) Design Philosophy & Tradeoffs:* Tower of 11 Abstract State Machine
     (ASM) refinement levels from POSIX VFS down to raw NAND flash pages.
   - *(5) Formal Theory & TCB:* ASM crash refinement in KIV; Scala/C code
     generator in TCB.

7. **`Atmosphere` (`mars-research/atmosphere`, Chen et al., SOSP 2023, DOI
   `10.1145/3600006.3613148`) and Industrial `SplinterDB` (`vmware/splinterdb`,
   Conway et al., USENIX ATC 2020) / `RocksDB` (`facebook/rocksdb`):**
   - *(1) Goals & Users:* `Atmosphere` is a Rust microkernel and storage/memory
     isolation substrate verified in **Verus** using linear ghost permissions;
     `SplinterDB` (VMware $B^\epsilon$-tree) and `RocksDB` (Meta LSM-tree) are
     the dominant unverified C/C++ NVMe storage engines whose compaction,
     snapshot-watermark tombstone retention, and WAL recovery invariants are key
     targets for formal verification.

#### 2.3 Mapping Domain 2 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_KV`: Atomic crash-consistent KV specification maintaining
    `(volatileMap, durableMap)` (`sync()` copies `volatileMap` to `durableMap`;
    `crash()` resets `volatileMap := durableMap`).
  - `L_Storage`: Concrete LSM-tree / $B^\epsilon$-tree (`RocksDB`/`SplinterDB`/
    `VeriBetrKV`) with memtables, SSTables, WAL, `MANIFEST`, and `recover()`.
  - `Partial.ub` (`defined = False`): Silent data corruption on `get(k)`
    (returning unverified bit-rotted bytes without raising `ChecksumError`),
    losing a key whose `sync()` returned `Ok`, or **tombstone resurrection**
    (compaction dropping `(k, seq, DEL)` while an older SSTable level $L_i$
    still holds `(k, seq', VAL)`).
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `PartialBehaviorCodec L_KV L_Storage`: `decodeOut` runs the recovery/read
    abstraction function and validates all SSTable CRC32c/xxHash checksums,
    B+-tree key ordering, and `MANIFEST` version chains, returning `none` if any
    on-disk representation invariant is violated. `Compiles L_KV L_Storage`
    directly expresses `Yggdrasil` / `VeriBetrKV` crash refinement!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Zero-change Crash Modality via `StepResult.externalCall`:** Every block
    device submission (`io_uring_enter`, NVMe `Write`/`Flush`) is a
    `StepResult.externalCall boundaryInv branches` where:
    - `boundaryInv` enforces the **Write-Ahead Logging rule**
      (`flushedLSN >= dirtyPage.pageLSN` before writing any dirty B+-tree page);
      violating WAL steps immediately to `.failed` (`Partial.ub`)!
    - `branches` demonically selects any crash subset of unflushed in-flight
      sector writes, capturing `FSCQ`/`Perennial`'s asynchronous disk crash
      semantics with **zero modifications** to `Trusted/StepResult.lean`!
  - `EventualBehaviorOf` absorbs variable $1 \to k$ background LSM compaction
    and B+-tree split steps, while `ProductiveOn` prevents `recover()` from
    trivially returning `Err(CorruptDisk)` on every crash image.
- **`VerificationResult` and `TrustPolicy`:**
  - Isolates cryptographic/checksum assumptions (`.waive "crc32c_collision_free"`,
    `.waive "zstd_block_codec"`) in `TrustPolicy` while machine-checking WAL
    ordering, snapshot watermark tombstone retention, and crash recovery
    idempotence.

---

### 3. Domain 3: Distributed Consensus, Transactions, and Replicated State Machines

`Basis: documentation + source + derived`

#### 3.1 Domain Problem Space and Tool Families

Distributed state machines and transactional databases (`Raft`, `Multi-Paxos`,
`Spanner` TrueTime + 2PL, `FoundationDB`, `CockroachDB`, `Calvin`, `Riak` CRDTs)
execute concurrent client operations over asynchronous networks subject to
packet loss, reordering, duplication, network partitions, node crash-recovery,
and bounded clock uncertainty $[t - \epsilon, t + \epsilon]$. Correctness
requires linearizability, strict serializability (external consistency), causal
consistency, or strong eventual consistency (SEC) without degenerating into a
system that aborts every transaction or stalls forever after Global
Stabilization Time (GST).

#### 3.2 Exhaustive Tool Deep-Dives (10 Core Tools)

1. **`Verdi` (`uwplse/verdi`, Wilcox et al., PLDI 2015, DOI
   `10.1145/2737924.2737958`) and `Verdi Raft` (`uwplse/verdi-raft`, Woos et al.,
   CPP 2016, DOI `10.1145/2854065.2854081`):**
   - *(1) Goals & Users:* Coq framework for implementing and verifying
     distributed systems (`Verdi Raft`: 50,000 lines of Coq proving
     `StateMachineSafety` and linearizability of Raft, extracted to OCaml).
   - *(2) History & Lineage:* Built at UW PLSE by James R. Wilcox, Doug Woos,
     Pavel Panchekha, Zachary Tatlock, Xi Wang, Michael D. Ernst, and Thomas
     Anderson.
   - *(3) Design Philosophy & Tradeoffs:* Introduces **Verified System
     Transformers (VSTs)**: an application is verified under an idealized single
     fault model, and compositional Coq transformers compile it to handle
     packet duplication, reordering, or crash recovery. Proves safety
     (linearizability via ghost history variables) but not liveness.
   - *(4) Ecosystem Comparison:* Contrast with `IronFleet` (which proves both
     safety and liveness in Dafny/Z3) and `Ivy` (which restricts invariants to
     decidable EPR).
   - *(5) Formal Theory & TCB:* Small-step network semantics in Coq + 90
     coupled inductive invariants for Raft; TCB is the Coq kernel, OCaml
     extraction, and the `vard` network shim.

2. **`IronFleet` (`microsoft/Ironclad`, Hawblitzel et al., SOSP 2015, DOI
   `10.1145/2815400.2815428`):**
   - *(1) Goals & Users:* Proves **both safety and liveness** of practical
     distributed protocol implementations (`IronRSL` Multi-Paxos replicated
     state machine and `IronKV` sharded key-value store) in Dafny.
   - *(2) History & Lineage:* Microsoft Research (Chris Hawblitzel, Jon Howell,
     Manos Kapritsos, Jacob R. Lorch, Bryan Parno, Michael L. Roberts, Srinath
     Setty, Brian Zill).
   - *(3) Design Philosophy & Tradeoffs:* Combines TLA-style state-machine
     refinement (`AbstractService` $\sqsubseteq$ `ProtocolLayer` $\sqsubseteq$
     `ConcreteImplementation`, using reduction/mover arguments to commute local
     steps between network I/O boundaries) with embedded Temporal Logic of
     Actions in Dafny for eventual leader election and progress after GST.
   - *(4) Ecosystem Comparison:* First distributed verification framework to
     machine-check liveness of a runnable Paxos implementation, directly
     motivating `Anvil`'s temporal logic in Verus.
   - *(5) Formal Theory & TCB:* Lipton reduction + TLA refinement in Dafny; TCB
     is Dafny, Boogie, Z3, the `.NET`/C# compiler, and UDP socket bindings.

3. **`Ivy` (`kenmcmil/ivy` / `microsoft/ivy`, Padon et al., PLDI 2016, DOI
   `10.1145/2908080.2908118`; Taube et al., PLDI 2018):**
   - *(1) Goals & Users:* Interactive inductive invariant discovery and
     decidable verification for distributed protocols (`Paxos`, `Raft`, ` two-phase
     commit`, `QUIC` network stack specification).
   - *(2) History & Lineage:* Created by Kenneth L. McMillan and Oded Padon
     (MSR / Tel Aviv / Stanford / VMware).
   - *(3) Design Philosophy & Tradeoffs:* Restricts protocol transition
     relations and inductive invariants to the **Effectively Propositional (EPR)**
     / Bernays-Schönfinkel-Ramsey fragment ($\exists^* \forall^*$ relational
     first-order logic without function cycles), where Z3 is a **complete
     decision procedure** (avoiding SMT quantifier-instantiation divergence /
     "matching loops" and yielding finite counterexample models whenever an
     inductive invariant is too weak).
   - *(4) Ecosystem Comparison:* Solves the #1 usability bottleneck of Dafny/Z3
     in `IronFleet` (flaky quantifier triggers), and supports compositional
     assume-guarantee decomposition (`Modularity for Decidability`, PLDI 2018).
   - *(5) Formal Theory & TCB:* EPR decidable logic + liveness-to-safety
     reductions (`Padon et al., POPL 2018`); TCB is the Ivy Python/C++
     compiler and Z3.

4. **`Aneris` (`logsem/aneris`, Krogh-Jespersen et al., ESOP 2020, DOI
   `10.1007/978-3-030-44914-8_14`) and `Chapar` (`mit-pdos/chapar`, Lesani,
   Bell, Chlipala, POPL 2016, DOI `10.1145/2837614.2837622`):**
   - *(1) Goals & Users:* Coq frameworks for modular distributed separation
     logic (`Aneris`, built on Iris at Aarhus/MPI-SWS) and causally consistent
     replicated key-value stores (`Chapar`, MIT).
   - *(3) Design Philosophy & Tradeoffs:* `Aneris` introduces node-local heaps
     paired with socket/network protocols inside higher-order Iris ghost state,
     allowing verification of node-local concurrency + network message passing
     in one logic. `Chapar` defines an operational Characterization of Causal
     Consistency (`CausalSpec`) and proves that concrete vector-clock /
     dependency-tracking KV algorithms refine `CausalSpec`.
   - *(5) Formal Theory & TCB:* Iris step-indexed separation logic in Coq
     (`Aneris`); labeled transition system (LTS) simulation in Coq (`Chapar`).

5. **`VeriFx` (`kevin-dp/VeriFx`, De Porre et al., ECOOP 2021 / OOPSLA 2023)
   and `Isabelle CRDT` (`Archive of Formal Proofs: CRDT`, Gomes, Kleppmann,
   Mulligan, Beresford, PACMPL / OOPSLA 2017, DOI `10.1145/3133933`):**
   - *(1) Goals & Users:* Verify Conflict-Free Replicated Data Types (CRDTs:
     `RGA` collaborative text editing, `OR-Set`, `LWW-Element-Set`) and
     Operational Transformation (OT) for Strong Eventual Consistency (SEC).
   - *(3) Design Philosophy & Tradeoffs:* Gomes et al. (OOPSLA 2017) mechanized
     a network model with causal delivery in Isabelle/HOL and proved that
     concurrent op-based CRDT effectors commute (`x ∘ y = y ∘ x` under concurrent
     causal histories); `VeriFx` compiles a Scala-like functional OOP language
     to Z3 to automatically check join-semilattice laws (associativity,
     commutativity, idempotence) and op-commutativity.
   - *(5) Formal Theory & TCB:* Isabelle/HOL kernel (`Isabelle CRDT`); Scala
     compiler + Z3 (`VeriFx`).

6. **`TLA+` and `TLAPS` (`tlaplus/tlapm`, Lamport, Cousineau, Doligez et al.,
   FM 2012, DOI `10.1007/978-3-642-32759-9_14`; Newcombe et al., CACM 2015
   "How Amazon Web Services Uses Formal Methods"):**
   - *(1) Goals & Users:* Industry standard specification language (`TLA+`),
     explicit-state model checker (`TLC`), symbolic SMT model checker (`Apalache`),
     and hierarchical proof system (`TLAPS`) used at AWS (DynamoDB, S3, EBS),
     Microsoft Azure (Cosmos DB), and MongoDB.
   - *(3) Design Philosophy & Tradeoffs:* Specifies systems as $Init \land \square [Next]_vars \land Liveness$,
     proving refinement via stuttering-insensitive refinement mappings
     ($Impl \implies Spec$). `TLAPS` dispatches proof obligations to Zenon,
     Z3, CVC4, and Isabelle/Pure, but models only the abstract algorithm,
     leaving an unverified gap between `TLA+` and production Rust/Go/C++ code.

7. **Deterministic Simulation & Black-Box History Checkers: `FoundationDB
   Simulation` (`apple/foundationdb`, Zhou et al., SIGMOD 2021, DOI
   `10.1145/3448016.3457559`) and `Jepsen` / `Elle` (`jepsen-io/jepsen`,
   `jepsen-io/elle`, Kingsbury & Alvaro, PVLDB 14(3) 2020, DOI
   `10.14778/3430915.3430918`):**
   - *(1) Goals & Users:* Industrial bug-finding for distributed databases.
   - *(3) Design Philosophy & Tradeoffs:* `FoundationDB` compiles its C++ actor
     code (`Flow`) against a deterministic single-threaded simulator (`sim2`)
     that deterministically permutes network partitions, disk stalls, clock
     skew, and machine reboots over billions of simulated CPU hours. `Jepsen`
     injects real network partitions/SIGKILL faults into live clusters and feeds
     the recorded client history into `Elle`, which reconstructs Adya
     read-write (`rw`), write-write (`ww`), and write-read (`wr`) dependency
     graphs to detect cycles violating Strict Serializability, Snapshot
     Isolation, or Read Committed in polynomial time (avoiding the
     NP-completeness of general `Knossos` Wing-Gong linearizability checking).

#### 3.3 Mapping Domain 3 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Serial`: Atomic single-node sequential transaction state machine.
  - `L_TLA`: Abstract distributed protocol state machine (`Raft`/`Paxos`/`SSI`).
  - `L_Dist`: Concrete replica event handlers (`on_rpc`, `on_timer`, `on_client`).
  - `SemObs` (`obs : Out → SemObs`): External client transaction history $H$
    (invocations, commit/abort outcomes, read values, and real-time timestamps)
    with internal heartbeats, `Prepare`/`Promise` messages, and lock tables
    erased.
  - `Partial.ub` (`defined = False`): Split-brain commit (`ElectionSafety` /
    `StateMachineSafety` violation), Adya cycle / write skew under `SERIALIZABLE`
    (`Elle` cycle), stale read violating TrueTime external consistency, or
    non-convergent CRDT replica state.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - Two-tier refinement via `Abstracts` + `Compiles` (`verify_through_passes` in
    `theory/Anneal/Refinement.lean:243-253`):
    1. `Abstracts L_TLA L_Dist nodeCodec ProtocolModel ConcreteReplica` lifts
       concrete Rust/C++ handlers to an `Ivy`/`TLA+` protocol specification.
    2. `Compiles L_Serial L_TLA histCodec SerialSpec ProtocolModel` proves via
       inductive invariants and linearization/prophecy witnesses that every
       protocol execution refines a serial history!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Abort-All Transactions" Goodhart Trap:** Any transaction
    manager that returns `.Aborted` on 100% of requests vacuously satisfies
    Strict Serializability and `Elle` cycle-freedom! Under Anneal's
    `ProductiveOn ContentionFreeAfterGSTPre ReplicaImpl`, the implementation is
    mathematically forced to produce a `.Committed` outcome whenever a quorum is
    healthy after GST and transactions do not contend.
  - `EventualBehaviorOf` natively models `TLA+` stuttering refinement: 1 serial
    step in `L_Serial` corresponds to $k$ asynchronous message-passing steps
    (2PC `Prepare` $\to$ Paxos `Accept` $\to$ TrueTime `CommitWait` $\to$
    `Apply`) in `L_Dist`.
  - `StepResult.externalCall` models network RPC transmissions and TrueTime
    `TT.now()` hardware clock reads, with `boundaryInv` enforcing Spanner's
    **Commit Wait Invariant** (`TT.now().earliest > commit_ts` before releasing
    locks or exposing writes) and Raft's **Persistent State before RPC** rule
    (`persistedTerm == currentTerm` before sending `RequestVoteResp` or
    `AppendEntriesResp`).
- **`VerificationResult` and `TrustPolicy`:**
  - Separates unconditional safety obligations (`.linearizability`,
    `.stateMachineSafety`) from conditional partial-synchrony liveness
    assumptions (`.gstBoundedDelay`) and BFT cryptographic assumptions
    (`.ed25519Unforgeable`).

---

### 4. Domain 4: Software-Defined Networking (SDN / P4 Data Planes) and BGP Control-Plane Verification

`Basis: documentation + source + derived`

#### 4.1 Domain Problem Space and Tool Families

Network infrastructure separates into three planes with distinct bug classes:
1. **Network Intent:** End-to-end reachability matrices, tenant slice isolation,
   waypoint chaining (e.g., traffic must traverse `Firewall` before `Backend`),
   and link-capacity / ECMP congestion bounds under $\le k$ link failures.
2. **Control Plane (`BGP`, `OSPF`, `ISIS`, `EVPN`):** Distributed policy
   filtering (`route-map`, `community`, `local_pref`, AS-path prepending) where
   policy interactions create **Griffin-Shepherd-Wilf Dispute Wheels**
   (permanent BGP route oscillation), BGP wedgies, or routing blackholes under
   single-link failures.
3. **Data Plane (`P4_16`, `eBPF/XDP`, `OpenFlow`, `Envoy`):** Packet header
   parsers, match-action tables (TCAM/SRAM), and tunnel encapsulation (`VXLAN`,
   `Geneve`, `SRv6`), where reading an unvalidated header (`hdr.ipv4` when
   `!hdr.ipv4.isValid()`) or miscompiling a match-action dependency corrupts or
   leaks packets in flight.

#### 4.2 Exhaustive Tool Deep-Dives (10 Core Tool Families / 14 Concrete Tools)

1. **`Batfish` (`batfish/batfish`, Fogel et al., NSDI 2015) and `Minesweeper`
   (`batfish/batfish`, Beckett et al., SIGCOMM 2017, DOI
   `10.1145/3098822.3098828`):**
   - *(1) Goals & Users:* Industry-standard multi-vendor router configuration
     analyzers (Cisco IOS, Juniper Junos, Arista EOS, AWS VPC) used by cloud and
     enterprise network engineers.
   - *(2) History & Lineage:* `Batfish` (UCLA / USC / Microsoft / Intentionet:
     Ari Fogel, Ratul Mahajan, Todd Millstein, George Varghese) parses vendor
     configs into control-plane Datalog (`LogicBlox`/`Soufflé`) to simulate one
     concrete fixed point and analyzes the resulting data plane using BDDs.
     `Minesweeper` (Princeton / MSR: Ryan Beckett, Aarti Gupta, Ratul Mahajan,
     David Walker) encodes the *entire stable routing problem* (BGP, OSPF,
     static routes, route redistribution, ACLs, and $k$-link failures) into a
     single combinatorial SMT formula in Z3 without simulating message-by-message
     convergence.
   - *(3) Design Philosophy & Tradeoffs:* `Batfish` is fast for concrete
     environment snapshots; `Minesweeper` verifies symbolic equivalence classes
     of external eBGP announcements and arbitrary $k$-link failure combinations,
     assuming BGP has a unique stable solution (or checking uniqueness via a
     2-copy SMT encoding).
   - *(5) Formal Theory & TCB:* Stable Routing Problem (SRP) SMT encoding +
     Java vendor config parsers + Z3.

2. **`Bagpipe` (`uwplse/bagpipe`, Weitz et al., OOPSLA 2016, DOI
   `10.1145/2983990.2984012`):**
   - *(1) Goals & Users:* Mechanically verifies that ISP BGP router
     configurations satisfy declarative routing policies (such as **Gao-Rexford**
     valley-free routing: never export routes learned from a peer or provider to
     another peer or provider).
   - *(2) History & Lineage:* Built at UW PLSE by Konstantin Weitz, Doug Woos,
     Emina Torlak, Michael D. Ernst, Arvind Krishnamurthy, and Zachary Tatlock.
   - *(3) Design Philosophy & Tradeoffs:* Formalizes RFC 4271 BGP semantics in
     **Coq** and proves that if a per-router export/import policy check holds on
     all single-hop announcements, then every reachable multi-hop network state
     satisfies the policy—reducing a distributed infinite-trace Coq theorem to a
     finite, decidable SMT check in Rosette/Z3!
   - *(5) Formal Theory & TCB:* Coq-verified inductive reduction from
     distributed BGP traces to local router checks + Rosette/Z3 solver.

3. **`NetKAT` (`frenetic-lang/netkat` / `google/netkat`, Anderson et al., POPL
   2014, DOI `10.1145/2535838.2535862`) and `KATch` (Moeller et al., PLDI 2024,
   DOI `10.1145/3656436`):**
   - *(1) Goals & Users:* Algebraic specification and PSPACE-complete
     decidable equivalence checking of SDN packet-forwarding and topology graphs
     (checking reachability, slicing isolation, loop freedom, and compiler
     correctness).
   - *(2) History & Lineage:* Created at Cornell and Princeton by Carolyn Jane
     Anderson, Nate Foster, Arjun Guha, Jean-Baptiste Jeannin, Dexter Kozen,
     Cole Schlesinger, and David Walker; `KATch` (PLDI 2024) introduced
     symbolic Brzozowski derivatives with Binary Decision Diagrams (SPPs:
     Symbolic Packet Programs) for orders-of-magnitude faster equivalence
     decision.
   - *(3) Design Philosophy & Tradeoffs:* Models switches as functions on packet
     histories using **Kleene Algebra with Tests (KAT)** plus packet field
     modification `f ← n` and `dup` history-recording operators. Sound and
     complete axiomatization mechanized in Coq.
   - *(5) Formal Theory & TCB:* Coalgebraic Brzozowski automata derivatives over
     Kleene Algebra with Tests; Coq metatheory.

4. **P4 Verification & Formal Semantics Suite: `p4v` (Liu et al., SIGCOMM 2018,
   DOI `10.1145/3230543.3230582`), `Vera` (Stoenescu et al., SIGCOMM 2018, DOI
   `10.1145/3230543.3230548`), `Petr4` (`cornell-netlab/petr4`, Doenges et al.,
   POPL 2021, DOI `10.1145/3434301`), `Poulet4` (`verified-network-toolchain/poulet4`,
   Coq P4 semantics), and `Gauntlet` (`p4gauntlet/gauntlet`, Ruffy et al., OSDI
   2020):**
   - *(1) Goals & Users:* Verify P4 programmable switch programs (`p4v`, `Vera`),
     mechanize the normative `P4_16` language standard (`Petr4`, `Poulet4`), and
     validate production P4 compilers (`p4c`, Barefoot Tofino) via translation
     validation (`Gauntlet`).
   - *(3) Design Philosophy & Tradeoffs:* `p4v` (Barefoot/Cornell/SRI) translates
     P4 + control-plane interface assumptions into Guarded Command Language
     (GCL) and verifies safety via Z3; `Vera` (UPB/Broadcom) uses SymNet
     symbolic execution to catch invalid header accesses, parser loops, and
     arithmetic overflows; `Petr4` & `Poulet4` mechanize big-step and small-step
     operational semantics and type soundness of `P4_16` in OCaml and Coq;
     `Gauntlet` (NYU) translates `p4c` IR passes into Z3 SMT queries and uncovered
     90+ bugs (including 25 silent miscompilations!) in `p4c` and Tofino.

5. **Real-Time Data-Plane Equivalence & Control-Plane Abstract Interpretation:
   `Header Space Analysis (HSA)` (Kazemian et al., NSDI 2012), `VeriFlow`
   (Khurshid et al., NSDI 2013), `APKeep` (`XJTU-NetVerify/apkeep`, Zhang et al.,
   NSDI 2020), and `NV` (`NetworkVerification/nv`, Giannarakis et al., PLDI 2020)
   / `ShapeShifter` (Beckett et al., PLDI 2019) / `Timepiece` (Tang et al.,
   PLDI 2023):**
   - *(3) Design Philosophy & Tradeoffs:* `HSA` treats headers as points in
     $\{0,1\}^L$; `VeriFlow` slices prefixes into trie equivalence classes;
     `APKeep` maintains a minimal partition of **Atomic Predicates** (BDDs)
     across ACLs and NATs for sub-millisecond incremental verification. On the
     control plane, `NV` models routing protocols as SRP algebraic attributes in
     OCaml, `ShapeShifter` applies **abstract interpretation** (Galois
     connections over route attributes) to verify BGP convergence/reachability,
     and `Timepiece` uses modular assume-guarantee temporal interfaces to verify
     2,000-node data-center BGP fabrics.

#### 4.3 Mapping Domain 4 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Intent`: End-to-end reachability/waypoint/isolation matrix (`NetKAT`
    specification).
  - `L_BGP` / `L_P4`: Distributed BGP router configs or compiled `P4_16` switch
    pipeline (`Poulet4` / `Petr4` semantics).
  - `SemObs` (`obs : Out → SemObs`): Egress `(zone, payload, waypoints)` or
    `.dropped` (stripping transit MPLS/VXLAN/SRv6 tunnel headers).
  - `Partial.ub` (`defined = False`): Forwarding loops (TTL exhaustion),
    tenant isolation violations, P4 invalid header reads/writes
    (`!hdr.ipv4.isValid()`), or BGP Dispute Wheel oscillation.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Compiles L_P4_MidEnd L_P4_BackEnd p4Codec ir_before ir_after` turns
    `Gauntlet`'s unverified Z3 translation validation into a kernel-checked Lean
    refinement proof over `Poulet4`-style semantics!
  - `Abstracts L_AtomicPred L_P4 apCodec BDDPartition SwitchPipeline` formalizes
    `APKeep`'s Atomic Predicate equivalence-class partitioning and
    `ShapeShifter`'s Galois-connection abstract interpretation directly as an
    Anneal `Abstracts` pass!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Drop-All Firewall" Goodhart Loophole:** A firewall compiler
    that emits `DROP ALL` trivially satisfies every negative tenant-isolation
    invariant. Under Anneal, `ProductiveOn AuthorizedTrafficPre CompiledTables`
    (paired with `obs_decodeOut` preserving `.forwarded`) forces legitimate
    production traffic to be delivered!
  - `EventualBehaviorOf` models BGP asynchronous message convergence: because
    `EventualBehaviorOf` requires a finite termination step count `steps : Nat`
    for every valid failure scenario $|F| \le k$, any BGP Dispute Wheel
    (route oscillation) fails `EventualBehaviorOf` automatically!
  - `StepResult.externalCall` models eBGP peer announcements and stateful L7
    middleboxes, checking RPKI Route Origin Validation and bogon filters in
    `boundaryInv`.
- **`VerificationResult` and `TrustPolicy`:**
  - Certifies LP-synthesized Traffic Engineering WCMP weights outside the TCB
    while scoping hardware TCAM parity assumptions in `TrustPolicy`.

---

### 5. Domain 5: Cloud Infrastructure-as-Code (IaC) and Kubernetes Reconciliation Loops

`Basis: documentation + source + derived`

#### 5.1 Domain Problem Space and Tool Families

Cloud orchestration operates through (a) **Declarative-to-DAG Planners**
(`Terraform`, `OpenTofu`, `Pulumi`, `CloudFormation`) that synthesize partially
ordered `Create`/`Update`/`Destroy` plans from state diffs, and (b)
**Event-Driven Kubernetes Reconciliation Controllers** (Operators, `ArgoCD`,
`Crossplane`) executing continuous `reconcile(ctx, req)` loops over `etcd`.
Controllers fail when **Time-of-Check-to-Time-of-Use (TOCTOU) stale reads** from
local informer caches, partial API failures, misordered `finalizers`, or
competing controllers cause orphan resource leaks, rolling-update availability
blackouts, or infinite reconciliation oscillation.

#### 5.2 Exhaustive Tool Deep-Dives (6 Core Tool Families / 8 Concrete Tools)

1. **`Anvil` (`anvil-verifier/anvil`, Sun et al., USENIX OSDI 2024 Best Paper,
   `https://www.usenix.org/conference/osdi24/presentation/sun`):**
   - *(1) Goals & Users:* Formal verification framework for building production
     Kubernetes controllers (ZooKeeper, RabbitMQ, FluentBit operators) in Rust
     with machine-checked **liveness and safety** proofs.
   - *(2) History & Lineage:* Developed at UIUC, VMware Research, CMU, and UW
     (Xudong Sun, Wenjie Ma, Jiawei Tyler Gu, Zicheng Ma, Tej Chajed, Jon Howell,
     Andrea Lattuada, Oded Padon, Lalith Suresh, Adriana Szekeres, Tianyin Xu)
     on top of **Verus** (`verus-lang/verus`).
   - *(3) Design Philosophy & Tradeoffs:* Formulates **Eventually Stable
     Reconciliation (ESR)**: $\square (\text{DesiredStateStable}(spec) \land
     \text{FairFailureFreeSuffix} \implies \lozenge \square \text{Matches}(state, spec))$.
     Handles arbitrary crash restarts, network retries, and stale views in the
     controller runtime (`deps_hack` / `kube-rs` shim).
   - *(4) Ecosystem Comparison:* Directly supersedes testing-only tools (`Sieve`)
     by proving absence of stale-read TOCTOU bugs and liveness stalls across all
     interleavings.
   - *(5) Formal Theory & TCB:* Embeds TLA+ temporal logic (`always`,
     `eventually`, `leads_to` with WF1/SF1 rules) inside Verus/Z3; TCB is Verus,
     Z3, the `kube-apiserver` cluster model, and `kube-rs` shim.

2. **`Sieve` (`sieve-project/sieve`, Sun et al., OSDI 2022,
   `https://www.usenix.org/conference/osdi22/presentation/sun`):**
   - *(1) Goals & Users:* Automated black-box/grey-box reliability testing tool
     for Kubernetes controllers written in Go (`operator-sdk` / `controller-runtime`).
   - *(3) Design Philosophy & Tradeoffs:* Instruments `client-go` informer
     caches and API calls to inject **time-travel (stale-read) perturbations**,
     controller crash-restarts after side-effecting API calls, and reordered
     watch events, checking whether the final cluster state differs from a
     reference unperturbed run (Differential Observability). Discovered 46
     serious bugs across 10 popular K8s operators (Cassandra, CockroachDB,
     Percona XtraDB, RabbitMQ).
   - *(5) Formal Theory & TCB:* Dynamic trace perturbation and differential
     state-equivalence testing (no formal proof).

3. **`K8s-TLA+` (Kubernetes Controller / Scheduler / Informer TLA+ Specifications,
   `kubernetes-sigs`, AWS/RedHat/ByteDance formal models):**
   - *(1) Goals & Users:* Model checking Kubernetes informer reflector/delta-FIFO
     pipelines, lease election, and custom operators using `TLC` and `Apalache`.
   - *(3) Design Philosophy & Tradeoffs:* Finds high-level protocol races in
     design documents but leaves the Go/Rust controller implementation unverified.

4. **Policy-as-Code & IaC Static Analyzers: `Terraform Sentinel` (HashiCorp),
   `Conftest` (`open-policy-agent/conftest`, Rego), and `Checkov`
   (`bridgecrewio/checkov`, Python graph-based IaC analyzer):**
   - *(1) Goals & Users:* Shift-left CI/CD policy gating for `terraform plan`
     JSON outputs, Kubernetes manifests, Helm charts, and CloudFormation
     templates.
   - *(3) Design Philosophy & Tradeoffs:* `Conftest` runs OPA `Rego` assertions
     over structured YAML/JSON configs; `Checkov` builds a resource dependency
     graph across Terraform modules to evaluate 1,000+ security compliance rules
     (e.g., S3 encryption, IAM wildcard restrictions). Both inspect **static
     target snapshots** only—they do not model the **intermediate transition
     states** of executing the `terraform apply` DAG (such as a 20-second outage
     when a Security Group or Target Group is destroyed before its replacement
     is attached).

5. **`Tiros` (Backes et al., CAV 2019, DOI `10.1007/978-3-030-25543-5_14`, AWS
   Automated Reasoning Group):**
   - *(1) Goals & Users:* Production symbolic reachability engine powering
     **Amazon Inspector Classic / AWS Network Access Analyzer** across millions
     of customer VPCs.
   - *(3) Design Philosophy & Tradeoffs:* Encodes AWS VPC routing tables,
     Security Groups (stateful), Network ACLs (stateless), Internet Gateways,
     NAT Gateways, Transit Gateways, and VPC Peering into Datalog (`Soufflé`)
     and SMT (`Z3`/`CVC4`/`MonoSAT`) to prove whether any packet can reach an
     EC2 instance from the public internet without sending probe packets.

6. **`Rehearsal` (`plasma-umass/rehearsal`, Shambaugh, Weiss, Guha, PLDI 2016,
   DOI `10.1145/2908080.2908122`):**
   - *(1) Goals & Users:* Verification tool for **Puppet** declarative server
     configuration manifests.
   - *(3) Design Philosophy & Tradeoffs:* Compiles Puppet resource graphs and
     POSIX file/package/service operations into a decidable, loop-free
     filesystem state-transformation semantics checked with Z3. Proves two key
     properties: **Determinism** (every valid topological execution order of the
     underspecified Puppet dependency DAG yields the exact same machine state)
     and **Idempotence** (running the manifest a second time is a no-op).

#### 5.3 Mapping Domain 5 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Decl`: Declarative desired cluster/cloud specification + continuous
    availability envelope (e.g., `activeHealthyPods >= PDB_minAvailable` and
    `neverPubliclyExposed(RDS)`).
  - `L_Ctrl`: Concrete Kubernetes operator `reconcile` step function (`Anvil`)
    or Terraform/Puppet DAG execution plan (`Rehearsal`).
  - `Partial.ub` (`defined = False`):
    - **Intermediate Rollout Outage / Transient Security Exposure:** Destroying
      old pods or security rules before replacements pass readiness checks at
      any intermediate step $0 \le i \le n$.
    - **Orphan Resource Leak / Data Loss:** Deleting a `PersistentVolumeClaim`
      before draining state, or failing to register a `finalizer` before
      provisioning an external cloud resource.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Compiles L_Decl L_Ctrl k8sCodec DesiredRolloutSpec ReconcileFn` captures
    both `Anvil`'s ESR property and `Rehearsal`'s DAG determinism (since
    demonic choice in `L_Ctrl` ranges over all topological schedules of the
    Terraform/Puppet DAG, and `Compiles` requires *every* schedule to refine the
    deterministic target state!).
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **All-Prefix Intermediate Availability + Eventual ESR in One Primitive:**
    Look at how `EventualBehaviorOf` in Anneal (`BehaviorOf` in
    `Trusted/StepResult.lean:176-187` combined with `EventualOut` in
    `support/BehaviorCodecExpressiveness.lean`) works:
    1. `defined` quantifies over **all finite prefixes** (`∀ n tr out,
       ReachesPrefix M.step p n init tr out → out.isSafe`), automatically
       enforcing **zero-downtime rolling updates** (no availability drop or
       transient security gap at any intermediate step $0 \le i \le n$)!
    2. `val` requires termination in a quiescent state matching `DesiredSpec`
       after $k$ reconcile ticks (`EventualOut.terminated`), proving `Anvil`'s
       **Eventually Stable Reconciliation (ESR)** without needing a separate
       temporal logic DSL in `trusted/lean/`!
    3. `ProductiveOn` blocks a controller that trivially avoids unsafe mutations
       by returning `RequeueAfter(∞)`.
  - `StepResult.externalCall` models `kube-apiserver` / Cloud SDK mutations,
    where `boundaryInv` enforces optimistic concurrency (`resourceVersion`
    precondition present) and `finalizer` attachment before provisioning
    external resources, while `branches` demonically models `409 Conflict`
    responses and `Sieve`-style stale informer cache reads!
- **`VerificationResult` and `TrustPolicy`:**
  - Waives external cloud control-plane propagation bounds
    (`.waive "aws_iam_eventual_consistency"`) while strictly proving controller
    idempotence, finalizer safety, and multi-controller non-oscillation.

---

### 6. Domain 6: Fine-Grained Authorization (`Cedar` / `Zanzibar` / `OPA`) and Differential Privacy Engines

`Basis: documentation + source + derived`

#### 6.1 Domain Problem Space and Tool Families

Authorization and privacy engines gate every data access:
1. **Attribute-Based & Relationship-Based Access Control (`Cedar`, `Zanzibar`/
   `SpiceDB`/`OpenFGA`, `OPA` Rego, AWS IAM):** Evaluate `(principal, action,
   resource, context)` against policy sets (`permit`/`forbid`) and relation
   graphs (`doc:readme#viewer@group:eng#member`). When listing or searching
   millions of records, engines use **Partial Evaluation** (residual policy
   compilation) to compile a policy into a SQL `WHERE` clause or vector-index
   filter; any mismatch between the residual filter and reference evaluation
   causes **unauthorized data leakage** or **silent over-filtering**.
2. **Differential Privacy (`OpenDP`, `Chorus`, `Fuzz`/`DFuzz`/`LightDP`,
   `CertiPriv`/`EasyCrypt apRHL`):** Bound the maximum change in a query's
   output when one user's data is added or removed (**global sensitivity**
   $\Delta f$), add calibrated Laplace/Gaussian noise, and enforce privacy
   budget accounting ($\sum \epsilon_i \le \epsilon_{\text{max}}$).

#### 6.2 Exhaustive Tool Deep-Dives (9 Core Tool Families / 13 Concrete Tools)

1. **`Cedar` and `cedar-spec` (`cedar-policy/cedar`, `cedar-policy/cedar-spec`,
   Cutler et al., OOPSLA 2024, DOI `10.1145/3649835`):**
   - *(1) Goals & Users:* Open-source authorization policy language powering
     **Amazon Verified Permissions** and **AWS IAM Identity Center**, designed
     from day one using **verification-guided development in Lean 4**!
   - *(2) History & Lineage:* Built by AWS Automated Reasoning Group (Craig
     Disselkoen, Aaron Eline, Shaobo He, Kyle Headley, Michael Hicks, Kesha
     Hietala, Emina Torlak, et al.).
   - *(3) Design Philosophy & Tradeoffs:* `cedar-spec` models Cedar's evaluator,
     validator (typechecker), symbolic compiler (for SMT equivalence/subsumption
     queries via `cvc5`), and partial evaluator in **Lean 4**. Proves in Lean 4:
     - **Default-Deny & `forbid`-Overrides-`permit` Safety:** A request is
       allowed iff at least one `permit` matches and zero `forbid` rules match.
     - **Policy Slicing Soundness:** Evaluating a request over a manifest-sliced
       subset of policies equals evaluating over the full policy set.
     - **Validator Type Soundness:** If the Cedar validator accepts a policy set
       under a schema, evaluation never fails with type errors (modulo explicit
       entity-dereference/extension traps).
     - **Differential Testing Bridge:** Because Cedar's production runtime is
       written in Rust (`cedar-policy`) while the proofs live in Lean 4
       (`cedar-spec`), AWS bridges the gap using millions of cargo-fuzz / DRT
       (Differential Random Testing) runs between the extracted Lean 4 reference
       evaluator and the Rust crate!
   - *(4) Ecosystem Comparison:* Closest real-world industrial cousin to Anneal
     in the Lean 4 ecosystem—and highlights the exact gap Anneal closes: Cedar
     relies on differential fuzzing between Lean 4 `cedar-spec` and Rust
     `cedar-policy`, whereas Anneal directly captures and verifies the Rust MIR
     of `cedar-policy` inside Lean 4!
   - *(5) Formal Theory & TCB:* Lean 4 kernel (`cedar-spec`) + unverified Rust
     re-implementation gap (mitigated by DRT) + `cvc5` for SMT analysis queries.

2. **`Zelkova` (Backes et al., FMCAD 2018, DOI `10.23919/FMCAD.2018.8603013`,
   AWS) and `Margrave` (Fisler, Krishnamurthi, Meyerovich, Tschantz, ICSE 2005,
   DOI `10.1145/1062455.1062502`):**
   - *(1) Goals & Users:* Policy equivalence, change-impact, and public-exposure
     analyzers for AWS IAM policies (`Zelkova`, powering **AWS IAM Access
     Analyzer** and S3 Block Public Access) and XACML access-control policies
     (`Margrave`, Brown Univ. / WPI).
   - *(3) Design Philosophy & Tradeoffs:* `Zelkova` translates AWS IAM JSON
     policies (including `Allow`, `Deny`, `NotAction`, `NotResource`, regex
     wildcards `*`/`?`, and condition keys) into SMT bitvector/string/regex
     formulas solved by `Z3`, `CVC4`, and a custom regex solver (`Z3-str3`).
     `Margrave` compiles XACML policies into Multi-Terminal Binary Decision
     Diagrams (MTBDDs) to compute exact change-impact diffs ($P_1$ vs. $P_2$)
     and query completeness.

3. **`Zanzibar` (Pang et al., USENIX ATC 2019, Google), `SpiceDB`
   (`authzed/spicedb`), and `OpenFGA` (`openfga/openfga`, CNCF):**
   - *(1) Goals & Users:* Planet-scale Relationship-Based Access Control (ReBAC)
     systems evaluating graph reachability over relation tuples
     (`object#relation@user_or_userset`) with union, intersection, and exclusion
     set rewrites plus ABAC `caveats`.
   - *(3) Design Philosophy & Tradeoffs:* `Zanzibar` achieves sub-10ms latency
     and **external consistency** (preventing the **"New Enemy Problem"**, where
     a user removed from an ACL reads newly updated content via a stale cache)
     using **Spanner TrueTime Zookies** (opaque consistency tokens bounding
     staleness) and the **Leopard Indexing System** (denormalized transitive
     group-to-group reachability bitmaps updated incrementally). `SpiceDB` and
     `OpenFGA` implement Zanzibar in Go over CockroachDB/Spanner/Postgres.

4. **`Open Policy Agent (OPA)` (`open-policy-agent/opa`, CNCF):**
   - *(1) Goals & Users:* General-purpose cloud-native policy engine evaluating
     declarative **Rego** (Datalog derivative over hierarchical JSON documents).
   - *(3) Design Philosophy & Tradeoffs:* Supports **OPA Partial Evaluation**
     (`opa compile`), which specializes a Rego policy with known `input.user`
     context into residual simplified Rego ASTs that are translated into SQL
     `WHERE` clauses or Elasticsearch filters for data-layer enforcement.

5. **Differential Privacy Verification & Runtime Engines: `OpenDP`
   (`opendp/opendp`, Gaboardi, Hay, Vadhan, Harvard), `Chorus`
   (`uvm-plaid/chorus`, Johnson, Near, Hellerstein, Song,PVLDB / EuroSys 2020),
   `Fuzz` (Reed & Pierce, ICFP 2010), `DFuzz` (Gaboardi et al., POPL 2013),
   `LightDP` (Zhang & Kifer, POPL 2017) / `Fuzzi` (POPL 2019), and `CertiPriv` /
   `EasyCrypt apRHL` (`EasyCrypt/easycrypt`, Barthe et al., POPL 2012, DOI
   `10.1145/2103656.2103670`):**
   - *(3) Design Philosophy & Tradeoffs:*
     - `OpenDP` structures DP pipelines in Rust as composable
       `Transformation`s (with stability map $d_{\text{out}} \le c \cdot d_{\text{in}}$)
       chained into `Measurement`s (with privacy map $\epsilon$) via manual
       LaTeX proof documents audited by a review board.
     - `Chorus` rewrites SQL queries (via `Apache Calcite`) to enforce clipping,
       join-sensitivity bounding, and noise injection on existing databases.
     - `Fuzz` & `DFuzz` use linear indexed type systems ($!_k \tau$) to track
       $k$-sensitivity of functions statically; `LightDP` uses relational shadow
       execution types to reduce adaptive DP verification (e.g., Sparse Vector
       Technique) to off-the-shelf safety assertions; `CertiPriv` (Coq) and
       `EasyCrypt` mechanize **Approximate Probabilistic Relational Hoare Logic
       (apRHL)** ($\vdash c_1 \sim_{\epsilon, \delta} c_2 : P \implies Q$) using
       probabilistic liftings/couplings.

#### 6.3 Mapping Domain 6 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_AuthSpec`: Reference `Cedar` (`cedar-spec`) or `Zanzibar` graph
    reachability evaluator, or reference post-filtered query
    `Filter(CheckAuth(u), Scan(T))`.
  - `L_CompiledAuth`: Rust `cedar-policy` MIR implementation, OPA partially
    evaluated SQL `WHERE` filter, or Zanzibar `Leopard` bitmap index.
  - `SemObs` (`obs : Out → SemObs`): Exact `Allow`/`Deny` boolean decision (or
    authorized row set) + mandatory security audit records.
  - `Partial.ub` (`defined = False`): Privilege escalation / unauthorized data
    leakage (`Allow` when `forbid` matches), evaluation traps, or **"New Enemy"
    causality violation** (evaluating ACLs at timestamp $t_{\text{acl}} <
    t_{\text{content}}$).
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - **Bridging `cedar-spec` (Lean 4) and `cedar-policy` (Rust) Without Fuzzing:**
    Instead of relying on differential random testing between `cedar-spec` and
    the Rust `cedar-policy` crate, Anneal's `anneal-rustc-capture` extracts the
    Rust MIR of `cedar-policy` and proves
    `Compiles L_CedarSpec L_Mir cedarCodec SpecEval MirEval` directly in the
    Lean 4 kernel!
  - **Certified Residual SQL Compilation (`OPA` / `Cedar` Partial Evaluation):**
    `Compiles L_PostFilter L_PushedSQL sqlCodec (Filter(Policy, Table)) ResidualSQL`
    proves that the pushed-down SQL `WHERE` clause returns the **exact same**
    rows as row-by-row policy evaluation.
  - **Differential Privacy Sensitivity & `OpenDP` Transformation Proofs via
    `Abstracts`:** `Abstracts L_Sensitivity L_SQL sensCodec BoundSpec SQLQuery`
    certifies relational query sensitivity $\Delta f$, and instantiating
    `Language` over 2-safety neighboring database pairs $(D_1, D_2)$ checks
    `LightDP`/`apRHL` coupling witnesses deterministically in Lean!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Deny-Everything" Security Goodhart Trap:** A policy compiler
    that compiles every residual query to `WHERE FALSE` (or returns `Deny` on
    all requests) commits zero unauthorized data leaks! Because Anneal's
    `PartialBehaviorCodec` enforces `obs_decodeOut` (`Allow ↔ Allow` and
    `Deny ↔ Deny`) and `ProductiveOn` requires a valid decision on every query,
    silent over-denial is refuted. Furthermore, `InhabitedPre (fun q =>
    eval p q = .Allow)` detects shadowed/dead `permit` rules during policy
    refactoring (`Margrave`/`Zelkova`).
  - `StepResult.externalCall` gates DP output release on `boundaryInv :=
    (remainingBudget >= queryEpsilon && sensitivityVerified)`.
- **`VerificationResult` and `TrustPolicy`:**
  - Enforces zero waivers on `forbid` rules and DP privacy-budget accounting
    while explicitly logging any hardware CSPRNG assumptions.

---

### 7. Domain 7: Hermetic Build Systems, Fine-Grained Incremental Computation, and Package Resolvers

`Basis: documentation + source + derived`

#### 7.1 Domain Problem Space and Tool Families

Build systems (`Bazel`, `Buck2`, `Nix`, `Shake`) and fine-grained incremental
computation engines (`Salsa` in `rust-analyzer`, `Adapton`) refine a clean,
from-scratch topological build (`L_CleanBuild`) using persistent memoization
caches, content-addressed Merkle digests (CAS), dynamic dependency discovery
(monadic build rules), and **Early Cutoff** (skipping downstream actions when a
recomputed dependency produces the same output hash). Bugs in dependency
tracking or sandbox mount isolation cause **stale build artifacts** (where an
incremental build diverges from a clean build) or **remote cache poisoning**.

#### 7.2 Exhaustive Tool Deep-Dives (7 Core Tool Families)

1. **`Build Systems à la Carte` (`snowleopard/build`, Mokhov, Mitchell, Peyton
   Jones, ICFP 2018, DOI `10.1145/3236774`; JFP 2020, DOI
   `10.1017/S0956796820000088`):**
   - *(1) Goals & Users:* Unifying executable taxonomy and formal correctness
     definition for build systems (`Make`, `Ninja`, `Shake`, `Bazel`, `Buck`,
     `Excel`, `Nix`) in Haskell.
   - *(2) History & Lineage:* Created by Andrey Mokhov (Newcastle / Jane Street),
     Neil Mitchell (Shake / Meta `Buck2`), and Simon Peyton Jones (MSR).
   - *(3) Design Philosophy & Tradeoffs:* Factorizes any build system into two
     orthogonal choices: a **Scheduler** (`Topological`, `Restarting`,
     `Suspending`) and a **Rebuilder** (`DirtyBit`, `VerifyingTraces`,
     `ConstructiveTraces` / Content-Addressed Early Cutoff), parameterized by the
     **Task Abstraction** (`Applicative` static dependencies vs. `Monad` dynamic
     dependencies). Defines **Build Correctness (From-Scratch Consistency)**:
     after building target $k$ from initial store $S_0$ with warm cache, the
     resulting store $S'$ agrees on $k$ and all its transitive dependencies with
     recomputing every task purely from scratch on the current input files.
   - *(4) Ecosystem Comparison:* Directly shaped the architecture of Meta's
     `Buck2` and Jane Street's `Jenga`.
   - *(5) Formal Theory & TCB:* Functional Haskell semantics (`Tasks Monad k v`);
     mechanized Coq/Isabelle adaptations exist for subsets, while the original
     paper provides pen-and-paper + property-tested proofs.

2. **`Pluto` (`pluto-build/pluto`, Erdweg, Lichter, Weiel, OOPSLA 2015, DOI
   `10.1145/2814270.2814277`):**
   - *(1) Goals & Users:* Incremental build system in Java supporting **dynamic
     dependencies**, **cyclic task dependencies** (via fixed-point iteration or
     cycle-handler plugins, e.g., $\text{LaTeX} \leftrightarrows \text{BibTeX}$),
     and fine-grained custom stamps (early cutoff).
   - *(5) Formal Theory & TCB:* Operational semantics with mechanized
     soundness/minimality proofs of dynamic dependency graph rebuilding.

3. **`Salsa` (`salsa-rs/salsa`, Matsakis et al., Rust incremental query
   framework powering `rust-analyzer`, `ruff`/`red-knot`, and `fe`):**
   - *(1) Goals & Users:* Demand-driven, fine-grained incremental computation in
     Rust with automatic dependency tracking, durability tiers, and Early Cutoff.
   - *(3) Design Philosophy & Tradeoffs:* Implements the **Red-Green Algorithm**
     (originally developed for `rustc`'s incremental query engine): each
     memoized query stores `(value, verified_at_revision, changed_at_revision,
     dependencies)`. When verifying whether query $Q$ is still valid at revision
     $R$, Salsa walks $Q$'s recorded inputs in execution order; if an input $I_1$
     is re-evaluated at $R$ and its output `PartialEq` equals its previous value
     (`changed_at < Q.verified_at`), $I_1$ is marked **Green** (Early Cutoff!),
     preventing $Q$ from re-executing and avoiding evaluating later dynamic
     branches $I_2$ that might depend on $I_1$!

4. **`Buck2` and `DICE` (`facebook/buck2`, Mitchell et al., Meta 2023):**
   - *(1) Goals & Users:* High-performance polyglot hermetic build system in
     Rust replacing `Buck1`, powered by the **DICE** (Deterministic Incremental
     Computation Engine) crate (`buck2/shed/dice`).
   - *(3) Design Philosophy & Tradeoffs:* Unifies configuration loading,
     Starlark evaluation, `Bxl` (Buck Extension Language) dynamic build graphs,
     and action execution inside a single monadic DICE dependency graph with
     content-addressed Early Cutoff and Remote Execution (`REAPI`) integration.

5. **`Adapton` (`adapton/adapton.rust`, Hammer, Phang, Hicks, Foster, PLDI 2014,
   DOI `10.1145/2594291.2594324`; Nominal Adapton OOPSLA 2015; Fungi 2018):**
   - *(1) Goals & Users:* Demand-driven Self-Adjusting Computation (SAC) with
     first-class **programmer-controlled cache names** (solving the "anonymous
     allocation hash-shift" problem when inserting an element at the head of a
     list invalidates all subsequent memoization nodes).
   - *(4) Ecosystem Comparison:* Already documented in the `reference` corpus
     (`adapton-names-identity-freshness-2014-2018`).

6. **`Bazel Skyframe` (`bazelbuild/bazel`) and `Remote Execution API (REAPI)`
   (`bazelbuild/remote-apis`):**
   - *(1) Goals & Users:* Google's open-source hermetic build system (`Skyframe`
     asynchronous restarting parallel evaluation framework over `SkyKey` $\to$
     `SkyValue`) and content-addressed remote execution protocol (`Action`,
     `Command`, `Directory` Merkle trees in CAS, `ActionCache`).

7. **`PubGrub` (`pubgrub-rs/pubgrub`, Weizenbaum 2018, Dart `pub`, Astral `uv`,
   `cargo` next-gen resolver):**
   - *(1) Goals & Users:* Conflict-Driven Clause Learning (CDCL) version and
     feature dependency solver that Either produces a valid locked dependency
     graph (`Cargo.lock` / `uv.lock`) or derives a minimal, human-readable
     **incompatibility proof tree** explaining why no version assignment exists.

#### 7.3 Mapping Domain 7 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_CleanBuild`: Pure, memoization-free topological evaluation from scratch
    (`Mokhov et al.` specification).
  - `L_IncBuild`: Stateful incremental engine (`Salsa` Red-Green, `Buck2 DICE`,
    or `Bazel Skyframe` with `ActionCache`).
  - `Query`: Sequence of workspace source edits $[W_0, W_1, \dots, W_m]$ +
    target key $k$.
  - `SemObs` (`obs : Out → SemObs`): Output artifact SHA-256 / byte payload at
    each revision $W_i$ (ignoring cache hit/miss counters).
  - `Partial.ub` (`defined = False`):
    - **Sandbox Escape / Undeclared Dependency Read:** Reading a host file or
      env var not committed to the `ActionKey` Merkle digest.
    - **Stale Artifact / Cache Poisoning:** Returning an incremental build result
      at $W_i$ that differs from `L_CleanBuild` on $W_i$.
    - **Dynamic Cycle Unsoundness:** Accepting a dependency cycle without raising
      `.CycleDetected`.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Compiles L_CleanBuild L_IncBuild buildCodec CleanBuild DICE_or_Salsa`
    mechanizes **From-Scratch Consistency** across multi-step edit traces!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Invalidate-Everything (`bazel clean`)" Degeneracy Trap:**
    An incremental engine that clears its entire cache on every edit trivially
    satisfies From-Scratch Consistency (`Compiles L_CleanBuild L_IncBuild`)!
    Anneal's `CertifiedOptimizationPass` (mechanized in
    `anneal-behavior-codec-and-progress-refinement-2026`,
    `support/AntiDegeneracyAndCallbackFraming.lean`) directly enforces strict
    dynamic step reduction on incremental edit benchmarks, proving that Early
    Cutoff and Green-node reuse genuinely skip downstream recomputations!
  - `EventualBehaviorOf` makes the $O(|G|) \to O(1)$ step collapse on an Early
    Cutoff cache hit completely transparent.
  - `StepResult.externalCall` models spawning a `linux-sandbox` / `REAPI` action
    worker, where `boundaryInv` checks `sandboxMountedPaths ⊆ actionKeyHashedInputs`
    before executing the compiler subprocess!
- **`VerificationResult` and `TrustPolicy`:**
  - Certifies `PubGrub` resolution witnesses and conflict derivation trees in
    Lean (turning an untrusted SAT/CDCL solver into a proof-producing resolver)
    while scoping `.waive "sha256_collision_resistance"` in `TrustPolicy`.

---

### 8. Domain 8: ML, Tensor, and Polyhedral Compilers, GPU Kernel Verifiers, and Distributed SPMD Sharding

`Basis: documentation + source + derived`

#### 8.1 Domain Problem Space and Tool Families

Modern AI/HPC compilers (`XLA`, `MLIR` Affine/Linalg, `Halide`, `Triton`, `TVM`,
`Exo`, `Mirage`) transform pure mathematical tensor graphs through:
1. **Polyhedral & Schedule Transformations:** Tiling, fusion, loop skewing,
   sliding-window storage folding, and software pipelining, where an off-by-one
   bound or violated loop-carried dependence (`RAW`/`WAR`/`WAW`) silently reads
   stale SRAM or faults out of bounds.
2. **GPU Kernel Lowering:** Mapping blocked tiles across threads/warps with
   XOR-swizzled shared memory (`smem`), async `TMA` copies, and `mbarrier` /
   `__syncthreads()` synchronization, risking intra-warp data races and
   thread-divergent barrier deadlocks.
3. **Distributed SPMD Tensor Sharding (`XLA GSPMD`, `PartIR`, `Shardy`):**
   Partitioning single-device tensor graphs across multi-dimensional device
   meshes and inserting collective operations (`AllReduce`, `ReduceScatter`,
   `AllGather`, `AllToAll`), where a missing collective silently corrupts
   multi-million-dollar training runs.

#### 8.2 Exhaustive Tool Deep-Dives (8 Core Tool Families / 13 Concrete Tools)

1. **`MLIR-TV` (`llvm/mlir-tv`, Bang et al., CAV 2022 / LLVM Dev, Alive2-style
   SMT translation validation for MLIR `arith`/`linalg`/`tensor`/`memref`
   dialects) and `VeriHLO` / `Alive2` (`AliveToolkit/alive2`, Lopes et al.,
   PLDI 2021, DOI `10.1145/3453483.3454030`):**
   - *(1) Goals & Users:* Automated SMT translation validation catching
     miscompilations in LLVM (`Alive2`) and MLIR/StableHLO (`MLIR-TV`,
     `VeriHLO`) passes.
   - *(3) Design Philosophy & Tradeoffs:* Encodes source and target IR
     semantics (including `poison` and `undef` / UB refinement) into Z3
     bitvector/array/FP queries for bounded loop unrollings and concrete small
     tensor shapes. Finds dozens of compiler bugs, but cannot verify parametric
     $N \times M \times K$ tensor shapes or unbounded polyhedral loops without
     timeout, and trusts the C++ Z3 encoder.

2. **`Halide` (`halide/Halide`, Ragan-Kelley et al., PLDI 2013) and
   `verified-halide` (`halide/Halide` formal verification / Clément & Cohen,
   OOPSLA 2022, DOI `10.1145/3563321`; Kortekaas et al., VerCors Halide):**
   - *(1) Goals & Users:* Decouples pure functional image/tensor **algorithms**
     (`f(x, y) = ...`) from **schedules** (`split`, `reorder`, `tile`,
     `vectorize`, `compute_at`, `store_at`).
   - *(3) Design Philosophy & Tradeoffs:* Clément & Cohen (OOPSLA 2022) and the
     Coq/VerCors Halide verification projects prove that Halide's schedule-lowering
     passes preserve functional equivalence and buffer bounds by checking
     Presburger arithmetic producer-consumer coverage conditions (`∀ consumer
     read, box_provided ⊇ box_required`) and absence of out-of-bounds memory
     accesses.

3. **`Exo` (`exo-lang/exo`, Ikarashi et al., PLDI 2022, DOI
   `10.1145/3519939.3523446`; `Exo 2` ASPLOS 2025; `Exo-GPU`):**
   - *(1) Goals & Users:* User-Schedulable Language (USL) based on
     **Exocompilation** for writing high-performance matrix/tensor kernels
     targeting AVX-512, ARM Neon, Apple AMX, Gemmini, and NVIDIA Tensor Cores.
   - *(3) Design Philosophy & Tradeoffs:* Moves the hardware backend and
     scheduling policies *out* of the compiler into user-defined libraries,
     while keeping a small **effect-analysis and Presburger SMT equivalence
     checker** inside the compiler's TCB! Every primitive scheduling rewrite
     (` divide_loop`, `reorder_loops`, `stage_mem`, `replace` with hardware
     intrinsic instruction spec) is checked by verifying that read/write/reduce
     effects and integer index expressions are preserved under Z3 Presburger
     arithmetic.
   - *(4) Ecosystem Comparison:* Shares Anneal's philosophy of keeping the
     core soundness checker small while allowing arbitrary external scheduling
     strategies.

4. **Distributed Tensor Sharding Compilers: `XLA GSPMD` (Xu et al., arXiv
   `2105.04663`, Google), `PartIR` (Alabed et al., Google DeepMind, MLIR loop-based
   incremental partitioner), and `Shardy` (`openxla/shardy`, OpenXLA 2024–2026):**
   - *(1) Goals & Users:* Partition single-device `StableHLO` / JAX / PyTorch
     models across thousands of TPUs/GPUs using mesh-axis sharding annotations
     and automatic collective insertion.
   - *(2) History & Lineage:* `GSPMD` propagated sharding specs across XLA HLO
     graphs heuristically; `PartIR` modeled sharding as formal rewrite steps over
     explicit `spmd` tile loops and collectives in MLIR; **`Shardy` (`sdy`
     dialect in `openxla/shardy`)** unified the `GSPMD` and `PartIR` teams into
     Google/OpenXLA's canonical MLIR tensor partitioning system.

5. **Polyhedral Compilers & Farkas-Lemma Certifiers: `Polly` (`llvm/llvm-project/polly`,
   Grosser et al., 2012), `isl` (Integer Set Library, Verdoolaege, ICMS 2010),
   and `Pluto`Polyhedral (Bondhugula et al., PLDI 2008):**
   - *(3) Design Philosophy & Tradeoffs:* Represent loop iteration domains
     $\mathcal{D}_S$, memory access relations $\mathcal{A}_S$, and schedules
     $\theta_S(\vec{i})$ as Presburger sets and relations in `isl`. Legality of
     an affine schedule transformation requires that for every dependence pair
     $(\vec{i}, \vec{j}) \in \mathcal{R}_{\text{dep}}$,
     $\theta_T(\vec{j}) - \theta_S(\vec{i}) \ge 0$. By the **Affine Form of
     Farkas' Lemma** (Schrijver / Feautrier), $\psi(\vec{x}) \ge 0$ holds on a
     non-empty polyhedron $A\vec{x} + \vec{b} \ge \vec{0}$ iff $\psi(\vec{x}) \equiv
     \lambda_0 + \vec{\lambda}^T (A\vec{x} + \vec{b})$ for some non-negative
     Farkas multipliers $\lambda_k \ge 0$! Checking a Farkas multiplier
     certificate $\vec{\lambda} \ge 0$ requires only **elementary polynomial
     ring identity checking (`ring` / `omega` in Lean)** without trusting `isl`
     or an ILP solver!

6. **GPU Concurrency & Data-Race Verifiers: `GPUVerify` (`imperial/gpuverify`,
   Betts et al., OOPSLA 2012, DOI `10.1145/2384616.2384625`) and `Faial`
   (`umb-svl/faial`, Cogumbreiro et al., CAV 2021, DOI
   `10.1007/978-3-030-81685-8_19`):**
   - *(1) Goals & Users:* Verify CUDA and OpenCL GPU kernels for absence of
     intra-block shared-memory data races, inter-block global-memory data races,
     and **barrier divergence** (threads in the same warp/block taking different
     branches across `__syncthreads()`).
   - *(3) Design Philosophy & Tradeoffs:* `GPUVerify` reduces $N$-thread SIMD
     lockstep execution to a **2-thread arbitrary-pair product program** verified
     in Boogie/Z3; `Faial` introduces **Memory Access Protocols (MAPs)** that
     decouple barrier-aligned access phases into parallel, loop-invariant-free
     SMT checks, achieving exponential speedups over `GPUVerify` on real CUDA
     kernels.

7. **Equality-Saturation & Multi-Level Tensor Superoptimizers: `Tensat`
   (`uwplse/tensat`, Yang et al., MLSys 2021) and `Mirage`
   (`mirage-project/mirage`, Wu et al., OSDI 2025, arXiv `2405.05751`):**
   - *(3) Design Philosophy & Tradeoffs:* `Tensat` uses `egg` equality saturation
     with ILP extraction to optimize tensor graphs; `Mirage` (CMU) superoptimizes
     custom GPU kernels across three hierarchy levels (kernel graph, threadblock
     graph, thread graph) using **$\mu\text{Graphs}$** and checks equivalence
     via **probabilistic algebraic fingerprinting over finite fields $\mathbb{F}_p$**
     (Schwartz-Zippel lemma), discovering fused FlashAttention/Lora kernels that
     outperform Triton and cuBLAS.

#### 8.3 Mapping Domain 8 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Tensor`: Single-device mathematical `StableHLO` / `Halide` / `MLIR Linalg`
    semantics parameterized by symbolic dimension variables `(B S H D : Nat)`.
  - `L_SPMD` / `L_Kernel`: `Shardy`/`PartIR` multi-device SPMD program or
    scheduled `Exo`/`Halide`/CUDA kernel.
  - `Partial.ub` (`defined = False`): Out-of-bounds SRAM/HBM tile indexing,
    shared-memory data races or barrier divergence (`GPUVerify`/`Faial`), or
    collective shape/participation mismatch across mesh devices.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - **SPMD Sharding Is an Exact `PartialBehaviorCodec`:**
    In `Shardy` / `PartIR` / `GSPMD`:
    - `encodeQuery`: Partitions a global input tensor $T \in \mathbb{R}^{B \times D}$
      into per-device shard buffers $\{T_p\}_{p \in \text{Mesh}}$ according to the
      `sdy.sharding` annotation.
    - `decodeOut`: Reconstructs the global output tensor from the per-device
      shard buffers $\{O_p\}_{p \in \text{Mesh}}$, and **returns `none` if
      replicated shards on different devices disagree** (e.g., when a compiler
      pass forgets to insert an `AllReduce` after a partial-sum reduction along
      a contracted axis)!
    - `decode_encode_out` and `encode_of_decode_some` enforce that the sharding
      layout is a lossless partial bijection, and `Compiles L_Tensor L_SPMD
      shardingCodec SingleDeviceProg ShardedProg` certifies the entire SPMD
      partitioner!
  - **Farkas-Lemma Polyhedral Certifier via `Abstracts`:**
    `Polly`/`isl` runs outside the TCB and emits non-negative Farkas multipliers
    $\vec{\lambda} \ge 0$ witnessing loop-dependence causality. Lean checks the
    linear combination identity via `ring`/`omega` inside `theory/`, discharging
    `Abstracts L_Polyhedra L_Kernel` and `Compiles L_Tensor L_Kernel` with zero
    solver trust!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `EventualBehaviorOf` collapses $O((M/T_M)(N/T_N)(K/T_K))$ tiled inner loop
    iterations and ring-collective steps into a 1-step tensor operation while
    checking `GPUVerify`/`Faial` barrier/race safety at every prefix step.
  - `StepResult.externalCall` models opaque vendor microkernels (`cuBLAS`,
    `wgmma`, TPU MXU) with `boundaryInv` enforcing 128-byte pointer alignment,
    leading-dimension stride divisibility, and SRAM residency.
- **`VerificationResult` and `TrustPolicy`:**
  - Turns `Mirage`'s probabilistic $\mathbb{F}_p$ fingerprint equivalence check
    or floating-point reassociation (`(a + b) + c` vs. `a + (b + c)` in
    tree-reduction `AllReduce`) into an explicit, auditable `TrustPolicy` item
    (`.waive "fp_associativity_in_allreduce"` or `.waive "schwartz_zippel_fp"`),
    or requires exact algebraic proof when `waived = []`.

---

### 9. Domain 9: Reactive Streaming Watermarks and Verified Lexer, Regex, and Parser Compilers

`Basis: documentation + source + derived`

#### 9.1 Domain Problem Space and Tool Families

This domain bridges two closely related finite-transducer and progress-tracking
Verification problems:
1. **Out-of-Order Streaming Engines & Watermarks (`Timely Dataflow`,
   `StreamBox`, `Apache Flink` ABS):** Events arrive out of order with logical
   event-time timestamps $t_e$, punctuated by watermarks $W(t)$ ("no future
   record has $t_e < W(t)$") and asynchronous checkpoint barriers (`Chandy-Lamport`
   ABS). Advancing a watermark prematurely drops valid in-flight events; holding
   a watermark at $-\infty$ forever stalls all window emissions and leaks memory.
2. **Verified Lexer, Regular-Expression, and Parser Compilers (`Coqlex`,
   `VeriLex`, `Ausaf-Dyckhoff-Urban` POSIX Regex, `lean-regex`, `CoStar`,
   `TRX`):** Compile declarative regular expressions and context-free / PEG
   grammars into high-speed DFA/VM/ALL(*) state machines while proving
   soundness, completeness, longest-match POSIX disambiguation, and absence of
   catastrophic backtracking (ReDoS) or left-recursion non-termination.

#### 9.2 Exhaustive Tool Deep-Dives (9 Core Tools)

1. **`Timely Dataflow` (`TimelyDataflow/timely-dataflow`, Murray, McSherry,
   Isaacs, Isard, Barham, Abadi, SOSP 2013, DOI `10.1145/2517349.2522738`;
   Abadi, McSherry, Plotkin, FossACS 2015):**
   - *(1) Goals & Users:* Low-latency cyclic dataflow runtime in Rust powering
     `Differential Dataflow` and `Materialize`.
   - *(2) History & Lineage:* Created at Microsoft Research Silicon Valley
     (`Naiad`) by Derek Murray, Frank McSherry, et al.; formalized by Martín
     Abadi, Frank McSherry, and Gordon Plotkin (2015).
   - *(3) Design Philosophy & Tradeoffs:* Tracks distributed progress across
     nested loop scopes using partially ordered **Pointstamps**
     `(location, timestamp) ∈ Location × Time` and **Capabilities** (an operator
     at `loc₁` holding capability `t₁` may emit messages at `(loc₂, t₂)` iff
     `(loc₁, t₁) ≤ (loc₂, t₂)` in the causal path-summary preorder). Workers
     maintain the minimal **Antichain Frontier** of active pointstamps; when no
     pointstamp in the frontier precedes `(loc, t)`, the runtime delivers a
     notification that timestamp `t` at `loc` is complete.
   - *(5) Formal Theory & TCB:* Partially ordered multiset transition semantics
     and antichain safety proof (Abadi-McSherry-Plotkin).

2. **`StreamBox` (`elijahr/StreamBox`, Miao et al., USENIX ATC 2017) and
   `Apache Flink ABS` (Asynchronous Barrier Snapshotting, Carbone et al.,
   arXiv `1506.08603` / VLDB 2017):**
   - *(1) Goals & Users:* High-throughput out-of-order stream engines.
   - *(3) Design Philosophy & Tradeoffs:* `StreamBox` decouples physical record
     containers (`Bundles`) from logical watermark punctuations so multi-core
     workers process out-of-order bundles lock-free while tracking the minimum
     in-flight event timestamp across upstream operators. `Flink ABS` adapts
     the **Chandy-Lamport distributed snapshot algorithm** to DAG stream
     pipelines by injecting `CheckpointBarrier(n)` markers into data streams,
     aligning barriers at multi-input operators (or buffering in-flight channel
     records in Unaligned Checkpoints), and committing external sinks via Two-Phase
     Commit (`TwoPhaseCommitSinkFunction`) to guarantee **exactly-once** state
     consistency across worker crashes.

3. **`Coqlex` (`Coqlex/coqlex`, Hills, Malik, et al., 2021–2023, arXiv
   `2301.10479`) and `VeriLex` (Egolf, Lasser, Casinghino, Coq verified lexer):**
   - *(1) Goals & Users:* Verified replacements for `ocamllex`/`flex` in Coq,
     closing the unverified lexer front-end gap in CompCert-style compilers.
   - *(3) Design Philosophy & Tradeoffs:* Prove in Coq that the generated
     longest-match, first-rule-priority tokenizer refines the declarative
     list-of-regexes specification using Brzozowski derivatives and fuel-bounded
     maximal munch.

4. **Verified Brzozowski/Thompson Regular-Expression Matchers:
   `Ausaf-Dyckhoff-Urban POSIX Lexing` (`Archive of Formal Proofs: Posix-Lexing`,
   Ausaf, Dyckhoff, Urban, ITP 2016, DOI `10.1007/978-3-319-43144-4_5`) and
   `lean-regex` (`pandaman64/lean-regex`, Sugiura, Lean 4 verified VM/DFA regex
   engine, 2024–2026):**
   - *(1) Goals & Users:* Formally verified regular-expression matching with
     submatch capture groups (`POSIX` longest-match / Perl greedy disambiguation)
     and linear-time $O(|s|)$ execution (immune to ReDoS catastrophic
     backtracking).
   - *(3) Design Philosophy & Tradeoffs:* Ausaf, Dyckhoff, and Urban mechanized
     Sulzmann-Lu bit-coded Brzozowski derivatives in Isabelle/HOL to prove exact
     POSIX longest-match submatch extraction. `lean-regex` (written in **Lean 4**)
     compiles regular expressions into a PikeVM / Thompson NFA virtual machine
     and proves inside the Lean 4 kernel that the VM matcher is sound and
     complete with respect to the inductive `Regex.Matches` semantics!

5. **`CoStar` (`slasser/CoStar`, Lasser, Casinghino, Fisher, Roux, PLDI 2021,
   DOI `10.1145/3453483.3454053`) and `TRX` (Koprowski & Binsztok, LMCS 2011,
   DOI `10.2168/LMCS-7(2:18)2011`):**
   - *(1) Goals & Users:* Formally verified parser engines in Coq.
   - *(3) Design Philosophy & Tradeoffs:* `CoStar` verifies Parr-Harwell's
     **$\text{ALL}(*)$** adaptive LL(*) parsing algorithm (the algorithm behind
     ANTLR4) in Coq, proving soundness, completeness, and termination on all
     non-left-recursive CFGs via DFA prediction over augmented transition
     networks (ATNs). `TRX` formalizes **Parsing Expression Grammars (PEGs)**
     (Ford, POPL 2004) in Coq and enforces termination on every grammar using a
     static structural **well-foundedness check (`wf_peg`: no nullable loop bodies
     and no unconsumed left recursion)** discharged over the product order on
     `(remaining_input_length, expression_height)`.

#### 9.3 Mapping Domain 9 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - *Streaming:* `L_IdealBatch` (sorted event-time window specification) vs.
    `L_Stream` (`Timely Dataflow` / `Flink ABS` out-of-order + barrier runtime).
  - *Lexing/Parsing:* `L_Grammar` (inductive `Regex.Matches` / POSIX maximal
    munch / CFG derivation tree) vs. `L_Automaton` (`lean-regex` PikeVM,
    `CoStar` ALL(*) ATN simulator, or `TRX` PEG interpreter).
  - `Partial.ub` (`defined = False`):
    - **Premature Watermark Advancement:** Firing/GC'ing a window at timestamp
      $t$ while an upstream operator or channel still holds a capability
      $t' \le t$ (`Timely Dataflow` frontier invariant violation).
    - **Duplicate/Lost State on Checkpoint Recovery:** Violating `Flink ABS`
      exactly-once barrier alignment.
    - **Grammar Left-Recursion / ReDoS Divergence:** Executing an ill-founded
      PEG (`¬ wf_peg`) or backtracking exponential regex traps.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Compiles L_IdealBatch L_Stream streamCodec IdealWindowQuery FlinkOrTimely`
    proves that out-of-order buffering + watermark emission + Chandy-Lamport
    checkpoint recovery produces the **exact same** output window aggregates as
    a failure-free sorted batch run!
  - `Abstracts L_Antichain L_Stream frontierCodec PointstampSummary TimelyGraph`
    models `Timely Dataflow`'s distributed antichain frontier tracking as an
    abstract interpretation over in-flight capabilities.
  - `Compiles L_Grammar L_Automaton parseCodec GrammarSpec PikeVM_or_ALLStar`
    embeds `lean-regex` and `CoStar` directly into Anneal's compiler hierarchy.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Hold-Watermark-at-$-\infty$-Forever" Goodhart Loophole:**
    A streaming engine that never advances its watermark ($W(t) = -\infty$)
    never prematurely fires a window—satisfying watermark safety vacuously by
    emitting zero outputs! In Anneal, `ProductiveOn BoundedOutOfOrderPre
    StreamPipeline` + `EventualBehaviorOf` forces the engine to advance
    watermarks, drain capabilities, and emit closed window results in finite
    steps for every bounded-lateness input prefix.
  - `StepResult.externalCall` models external `TwoPhaseCommitSink` commits in
    `Flink ABS`, where `boundaryInv` verifies that **every** parallel subtask
    has acknowledged `CheckpointBarrier(n)` before the sink commits externally!
- **`VerificationResult` and `TrustPolicy`:**
  - Scopes external Kafka partition watermark-monotonicity assumptions in
    `TrustPolicy` while machine-checking internal antichain progress and
    Chandy-Lamport barrier recovery.

---

### 10. Domain 10: Wire-Format Schemas, Bi-Directional Lenses, and Durable Execution Workflows

`Basis: documentation + source + derived`

#### 10.1 Domain Problem Space and Tool Families

Distributed services upgrade rolling-style across heterogeneous versions:
1. **Binary Wire Parsers & Zero-Copy Serializers (`EverParse`/`3D`, `Narcissus`,
   `Vest`, `zerocopy`, `Cap'n Proto`, `FlatBuffers`, `rkyv`):** Parse untrusted
   network byte slices into typed domain structures without buffer overreads,
   integer overflows, alignment faults, non-canonical wire encodings (malleability),
   or unknown-field truncation during proxy read-modify-write pass-through.
2. **Bi-Directional Schema Lenses (`Cambria`, `Boomerang`, `Buf`):** Translate
   API payloads across schema versions ($V_1 \leftrightarrows V_2$) while
   preserving round-trip lens laws (`GetPut`, `PutGet`, `PutPut`).
3. **Durable Execution Workflows (`Temporal`, `Restate`, `P Language`):**
   Execute long-running sagas and workflows by persisting an append-only event
   history log and replaying the workflow code from the beginning on worker
   recovery. Any **non-deterministic replay divergence** (where replayed code
   issues a command sequence incompatible with the recorded history log) causes
   a fatal `NonDeterministicWorkflowError` stall in production.

#### 10.2 Exhaustive Tool Deep-Dives (7 Core Tool Families / 11 Concrete Tools)

1. **`EverParse` and `3D` (`project-everest/everparse`, Ramananandro et al.,
   USENIX Security 2019; Swamy et al., OOPSLA 2022) and `LowParse`:**
   - *(1) Goals & Users:* Microsoft Research / Project Everest framework
     generating formally verified, zero-copy C and Rust binary message validators
     and parsers from `3D` (Dependent Data Descriptions) specifications, deployed
     inside the **Windows Kernel VirtualSwitch (`vmswitch.sys`)**, Hyper-V, TLS
     1.3 (`miTLS`), and DICE/TPM firmware.
   - *(3) Design Philosophy & Tradeoffs:* Compiles declarative C-like struct
     format specs with dependent field constraints (e.g., length fields, tag
     unions, bounds checks) into **F\*** / **Low\*** / **Pulse** validators that
     check wire validity in-place with zero heap allocations. Proves memory
     safety, arithmetic overflow freedom, parser injectivity, and **non-malleability**
     (canonical serialization: `∀ b₁ b₂, parse b₁ = some v ∧ parse b₂ = some v → b₁ = b₂`).

2. **`Narcissus` (`uwplse` / Delaware, Sorawit, et al., PACMPL / POPL 2019, DOI
   `10.1145/3290389`, MIT / Purdue / UPenn):**
   - *(1) Goals & Users:* Coq combinator framework (`Fiat` ecosystem) for
     automatically synthesizing correct-by-construction binary encoders and
     decoders for network protocols (DNS, TCP, Ethernet, ARP, Protobuf varints).
   - *(3) Design Philosophy & Tradeoffs:* Separates relational format
     specifications (`Format : Domain → ByteString → Prop`) from executable
     encoders and decoders, using Coq tactics to automatically derive a
     decoder `decode` and prove round-trip correctness (`encode m bs →
     decode bs = some m`).

3. **`Vest` (`secure-foundations/vest`, Cai, Bosamiya, et al., CMU / USENIX
   Security 2025) and Rust Zero-Copy Frameworks (`google/zerocopy`,
   `Cap'n Proto`, `FlatBuffers`, `rkyv`):**
   - *(1) Goals & Users:* `Vest` is a formally verified parser and serializer
     combinator library for **Rust** built in **Verus** (`verus-lang/verus`),
     providing panic-free, zero-copy slice parsing with machine-checked proofs
     of round-trip inversion (`parse(serialize(v)) == Ok(v)` and
     `serialize(parse(b)) == Ok(b)`—ruling out format malleability and parser
     differential bugs like CVE-2020-0601!). Connects directly to `zerocopy`
     (`TryFromBytes`, `IntoBytes`, `KnownLayout`) and archive validators like
     `rkyv::check_archived_root` and `FlatBuffers` vtable verifiers.

4. **`Cambria` (`inkandswitch/cambria-project`, Litt, Hardenberg, Orion, Ink &
   Switch 2020) and `Boomerang` (`boomerang-lang/boomerang`, Bohannon, Foster,
   Pierce, Pilkiewicz, Schmitt, POPL 2008, DOI `10.1145/1328438.1328487`):**
   - *(1) Goals & Users:* Bi-directional data lenses translating structured
     documents (`Cambria` for JSON/YAML API & local-first schema evolution) and
     strings (`Boomerang` regular string lenses at UPenn) across versions.
   - *(3) Design Philosophy & Tradeoffs:* `Boomerang` pioneered compositional
     lens combinators satisfying the **Well-Behaved Lens Laws**:
     - `GetPut`: `put s (get s) = s`
     - `PutGet`: `get (put s v) = v`
     - `PutPut`: `put (put s v₁) v₂ = put s v₂`
     `Cambria` applies **Symmetric / Edit Lenses** (Hofmann, Pierce, Wagner,
     POPL 2011) to JSON schemas using a **complement store** (cloud/unknown-field
     storage) so that when a $V_2$ document is downgraded to $V_1$, edited by a
     $V_1$ client, and upgraded back to $V_2$, all $V_2$-only fields survive
     intact!

5. **`Buf` (`bufbuild/buf`, Protobuf schema linter and `buf breaking` wire
   compatibility checker):**
   - *(1) Goals & Users:* Industry-standard CLI enforcing syntactic and wire-level
     backward/forward compatibility across `.proto` commits (`FILE`, `PACKAGE`,
     `WIRE`, and `WIRE_JSON` breaking-change categories).

6. **Durable Execution & Event-Driven State Machine Engines: `Temporal`
   (`temporalio/temporal`), `Restate` (`restatedev/restate`, Ewen et al.), and
   `P Language` (`p-org/P`, Desai, Gupta, Jackson, Qadeer, Rajamani, Zufferey,
   PLDI 2013, DOI `10.1145/2491956.2462184`, MSR / AWS):**
   - *(1) Goals & Users:* `Temporal` and `Restate` execute fault-tolerant
     microservices and workflows via deterministic event-journal replay; `P`
     is an asynchronous communicating state-machine DSL with integrated model
     checking and symbolic execution used by AWS (S3, Firecracker) and Microsoft
     (Windows USB 3.0 driver stack).
   - *(3) Design Philosophy & Tradeoffs:* In `Temporal` and `Restate`, when a
     worker crashes mid-workflow, a new worker replays the workflow function
     from the start against the persisted journal of completed side effects
     (`ActivityTaskCompleted`, `TimerFired`). If a code deployment changes the
     order of nondeterministic calls without a ` workflow.GetVersion` / patch
     gate, replay fails with a non-determinism error.

#### 10.3 Mapping Domain 10 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - *Wire Formats & Lenses:* `L_Domain` (typed domain values + unknown-field
    complement) vs. `L_Wire` (serialized wire bytes / zero-copy buffer slices).
  - *Durable Workflows:* `L_IdealSaga` (crash-free sequential workflow execution)
    vs. `L_Replay` (`Temporal`/`Restate` journal-replay state machine across
    arbitrary crash-recovery boundaries and code upgrades $V_1 \to V_2$).
  - `Partial.ub` (`defined = False`):
    - **Parser Buffer Overread / Unaligned Zero-Copy Cast:** Reading past slice
      bounds or transmuting an invalid bit pattern (`zerocopy` / `Vest`).
    - **Unknown-Field Loss in Proxy Pass-Through:** A $V_1$ intermediary
      deserializing and re-serializing a $V_2$ message and dropping $V_2$ fields.
    - **Durable Replay Non-Determinism (`Temporal`/`Restate`):** Replaying
      workflow code against a committed journal prefix and emitting a command
      type or ID that mismatches the journal entry!
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - **Anneal's `PartialBehaviorCodec` IS the Exact Mathematical Primitive of
    `EverParse`, `Narcissus`, `Vest`, and `Cambria`/`Boomerang`!**
    Compare the fields of `PartialBehaviorCodec L₁ L₂` (in
    `anneal-behavior-codec-and-progress-refinement-2026`,
    `support/BehaviorCodecExpressiveness.lean`) with `Vest`/`EverParse`/`Boomerang`:
    1. `encodeOut : L₁.Out → L₂.Out` is the **Serializer / `put`**.
    2. `decodeOut : L₂.Out → Option L₁.Out` is the **Partial Parser / Validator /
       `get`**.
    3. `decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁` is the
       **Round-Trip Deserialization / `GetPut` Law**!
    4. `encode_of_decode_some : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`
       is **`EverParse` & `Vest`'s Canonical Non-Malleability / `PutGet` Law**!
    5. `obs_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁`
       is **Cross-Version Semantic Projection Preservation (`Cambria` / `Buf`)**!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Reject-All-Messages (`return Err`)" Parser Goodhart Trap:**
    A parser that returns `None` (`Err(InvalidInput)`) on 100% of inputs
    trivially satisfies partial soundness (`decodeOut b = some v → Valid v`)!
    In Anneal, `ProductiveOn ValidSchemaV1Pre DeserializerV2` proves **Backward
    Wire Compatibility** (every valid $V_1$ wire message parses to `some` in
    $V_2$), and `ProductiveOn ValidSchemaV2Pre DeserializerV1` proves **Forward
    Wire Compatibility**!
  - **Certifying `Temporal`/`Restate` Replay Determinism via `StepResult.externalCall`:**
    Each durable side-effect (`ExecuteActivity`, `Sleep`, `GetVersion`) is a
    `StepResult.externalCall boundaryInv branches` where `boundaryInv` checks
    that during replay mode, the emitted command matches the next entry in the
    recorded workflow history log! Proving `Compiles L_WorkflowV1 L_WorkflowV2`
    over all recorded $V_1$ journal prefixes mathematically certifies that a
    live `Temporal`/`Restate` workflow upgrade will never throw
    `NonDeterministicWorkflowError`!
- **`VerificationResult` and `TrustPolicy`:**
  - Requires an explicit, auditable waiver (`waived := [.breakingFieldRemoval 4]`)
    whenever a team intentionally breaks wire compatibility or deprecates an old
    workflow version branch.

---

### 11. Cross-Domain Synthesis Matrix: Goodhart Failure Modes and Anneal Primitive Defenses

`Basis: derived`

The table below synthesizes how all 10 domains exhibit isomorphic "degenerate
implementation / Goodhart" failure modes when specifications are checked without
Anneal's four primitives, and how `Partial`, `PartialBehaviorCodec`,
`ProductiveOn`, `EventualBehaviorOf`, `StepResult.externalCall`, and
`ScopedVerificationResult` close each loophole uniformly:

| Domain & Representative Tools | Degenerate "Goodhart Cheat" Admitted by Naive Specifications | How Anneal's 4 `trusted/` Primitives Block the Cheat |
| :--- | :--- | :--- |
| **1. SQL / Datalog & IVM** (`Cosette`, `UDP`, `SPES`, `WeTune`, `QCert`, `DBSP`/`Feldera`, `Calcite`, `Soufflé`) | Compile complex joins to `.aborted .outOfMemory`, conflate set/bag multiplicities, or push `1/x` below `WHERE x <> 0` | `obs_decodeOut` locks in the multiset & Kleene-3VL spine; `ProductiveOn` forbids synthetic errors; `defined` rejects new evaluation-order traps |
| **2. Crash-Safe Storage** (`FSCQ`, `Perennial`/`DaisyNFS`, `Yggdrasil`, `VeriBetrKV`, `BilbyFS`, `Flashix`, `SplinterDB`) | Have `recover()` always return `Err(Corrupt)`, drop LSM tombstones early, or flush dirty B+-tree pages before WAL `fsync` | `StepResult.externalCall` enforces `flushedLSN >= pageLSN` in `boundaryInv` and branches demonically over crash subsets; `ProductiveOn` forces `recover()` to succeed |
| **3. Distributed Consensus & Txns** (`Verdi`, `IronFleet`, `Ivy`, `Aneris`, `Chapar`, `VeriFx`, `TLAPS`, `FoundationDB`, `Elle`) | Abort 100% of client transactions to be trivially "serializable", or never elect a leader after GST | `ProductiveOn ContentionFreeAfterGST` forces transactions to `.Committed`; `Abstracts` + `Compiles` proves refinement to serial execution |
| **4. SDN / P4 & BGP Networking** (`Batfish`, `Minesweeper`, `Bagpipe`, `NetKAT`, `p4v`, `Vera`, `Petr4`/`Poulet4`, `Gauntlet`, `APKeep`, `NV`/`ShapeShifter`) | Emit a `DROP ALL` firewall to satisfy tenant isolation, or leave BGP Dispute Wheels that oscillate forever | `obs_decodeOut` + `ProductiveOn AuthorizedPre` forces positive delivery of allowed traffic; `EventualBehaviorOf` rejects non-terminating BGP oscillations |
| **5. Cloud IaC & K8s Controllers** (`Anvil`, `Sieve`, `K8s-TLA+`, `Conftest`, `Checkov`, `Tiros`, `Rehearsal`) | Return `RequeueAfter(∞)` (never reconcile) or cause a 30s availability drop during a rolling update | `EventualBehaviorOf` enforces **all-prefix intermediate safety** (`ReachesPrefix` at every step $0 \le i \le n$) and **eventual convergence (ESR)** |
| **6. Authorization & Diff. Privacy** (`Cedar`/`cedar-spec`, `Zelkova`, `Margrave`, `Zanzibar`/`SpiceDB`, `OPA`, `OpenDP`, `Chorus`, `Fuzz`/`DFuzz`, `CertiPriv`) | Compile residual SQL filters to `WHERE FALSE` (deny all), or release DP aggregates without budget/sensitivity checks | `obs_decodeOut` preserves `Allow ↔ Allow` bijectively; `InhabitedPre` flags shadowed `permit` rules; `StepResult.externalCall` gates DP release on `budget >= ε` |
| **7. Build Systems & Incremental Comp.** (`Build Systems à la Carte`, `Pluto`, `Salsa`, `Buck2 DICE`, `Adapton`, `Skyframe`, `PubGrub`) | Mount undeclared host files into the sandbox, or invalidate 100% of the cache (`clean`) on every edit | `StepResult.externalCall` checks `sandboxMounts ⊆ hashedInputs`; `obs_decodeOut` proves From-Scratch Consistency; `CertifiedOptimizationPass` enforces Early Cutoff |
| **8. ML / Tensor / GPU Compilers** (`MLIR-TV`, `verified-halide`, `Exo`, `PartIR`/`GSPMD`/`Shardy`, `Polly`/`isl`, `GPUVerify`/`Faial`, `Tensat`/`Mirage`) | Forget an `AllReduce` across TPU shards, or mis-tile a GPU shared-memory loop with barrier divergence | Sharding `PartialBehaviorCodec` returns `decodeOut = none` if replicated shards disagree; `defined` rejects SRAM races and barrier divergence |
| **9. Streaming & Verified Parsing** (`Timely Dataflow`, `StreamBox`, `Flink ABS`, `Coqlex`, `VeriLex`, `lean-regex`, `CoStar`, `TRX`) | Hold watermarks at $-\infty$ forever so windows never fire with wrong data, or loop on left-recursive PEGs | `ProductiveOn` + `EventualBehaviorOf` forces watermark progress and window emission; `defined` enforces `TRX`/`CoStar` termination guards |
| **10. Wire Schemas, Lenses & Workflows** (`EverParse`, `Narcissus`, `Vest`, `Cambria`/`Boomerang`, `Buf`, `Temporal`/`Restate`, `P`) | Return `ParseError` on all wire bytes, drop unknown fields in proxies, or diverge on `Temporal` workflow replay | `PartialBehaviorCodec` laws directly encode `GetPut`/`PutGet`/non-malleability; `ProductiveOn` enforces parse totality; `externalCall` checks replay journal parity |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **SQLSolver (SIGMOD 2024), VeriEQL (OOPSLA 2024), Polygon (OOPSLA 2024),
  SeQLean (Lean 4 SQL), Mediator (PLDI 2018), and DBToaster / F-IVM:** Unbounded
  $\text{LIA}^*$ bag-equivalence provers, 3VL NULL/constraint SMT checkers, Lean
  4 relational algebra, and higher-order ring IVM compilers.
- **SFSCQ / DISKSEC (OSDI 2018), Argosy (`mit-pdos/argosy`, PLDI 2019), BesFS,
  Notary (SOSP 2019), and ALICE (OSDI 2014):** Compositional crash-safe storage
  recovery, storage non-interference, and persistence vulnerability explorers.
- **Grove (`mit-pdos/grove`, SOSP 2023), Trillium (`logsem/trillium`, POPL
  2021), Velisarios (ESOP 2018), Armada (`microsoft/armada`), and ByMC:**
  Perennial/Iris time-lease distributed separation logic, TLA trace refinement,
  Coq PBFT verification, and threshold automata model checking.
- **`bf4` (`verified-network-toolchain/bf4`, SIGCOMM 2020), Plankton/Hoyan
  (NSDI/SIGCOMM 2020), SecGuru/NoD (Azure), and Vigor/Klint (`vigor-nf/vigor`,
  SOSP 2019 / OSDI 2022):** Controller-guard synthesis for P4, packet
  equivalence-class BGP checking, and end-to-end verified C/binary network
  functions.
- **Welder (2024-2025) and Acto (`acto-project/acto`, SOSP 2023); Quacky, Duet,
  and ShadowDP/CheckDP; PIE (`metaborg/pie`), Jane Street `Incremental`, and
  Skip:** Compositional multi-controller Kubernetes verification, quantitative
  IAM/DP verifiers, and statically typed early-cutoff build pipelines.
- **TASO (SOSP 2019), PET (OSDI 2021), Glenside, CuTe Layout Algebra
  (`NVIDIA/cutlass`), Isabelle `Timely_Dataflow` (`isa-afp`), Flumina, BiGUL,
  and HasChor/Zooid:** Tensor superoptimizers, GPU `(Shape, Stride)` layout
  algebra, Isabelle/HOL Timely Dataflow progress proofs, Agda putback lenses
  (`BehaviorCodec`), and choreographic projection.

### Part II: Historical Verification, Compiler, and Operational Failure Postmortems

### Historical Failure Analysis 1. SQL Query Optimizer, Equivalence Prover, and Incremental View Maintenance Failures

`Basis: documentation + source + derived`

#### 1.1 Three-Valued Kleene `NULL` Logic (`UNKNOWN`) and Query-Partitioning Failures (`SQLancer` across `PostgreSQL`, `MySQL`, `CockroachDB`, `SQLite`, and `TiDB`)

In standard SQL (ISO/IEC 9075), predicates evaluate in Kleene three-valued logic
(`TRUE`, `FALSE`, `UNKNOWN`, where `NULL` acts as `UNKNOWN`). While `WHERE p`
and `INNER JOIN ... ON p` retain only rows where `p` evaluates to `TRUE`
(collapsing `FALSE` and `UNKNOWN`), `NOT p`, `CASE WHEN`, `LEFT/RIGHT/FULL
OUTER JOIN`, `NOT IN`, and `HAVING` treat `UNKNOWN` and `FALSE` asymmetrically
($\neg \text{UNKNOWN} = \text{UNKNOWN}$).

Manuel Rigger and Zhendong Su exposed the systemic fragility of industrial query
optimizers under three-valued logic through three metamorphic and differential
testing oracles in `SQLancer`:

- **Ternary Logic Partitioning (`TLP`, OOPSLA 2020, `10.1145/3428279`):** For
  any query $Q$ and predicate $p$, `TLP` partitions $Q$ into three sub-queries
  filtered by `WHERE p`, `WHERE NOT (p)`, and `WHERE (p) IS NULL`. By the law of
  excluded fourth in Kleene logic, the multiset union (or aggregate combination)
  of the three partitioned queries must equal $Q$.
- **Non-Optimizing Reference Engine Construction (`NoREC`, ESEC/FSE 2020,
  `10.1145/3368089.3409710`):** Rewrites an optimizable query `SELECT * FROM T
  WHERE p` (which triggers index selection, predicate pushdown, and join
  reordering) into an unoptimizable projection `SELECT (p) IS TRUE FROM T` and
  counts matching rows.
- **Pivoted Query Synthesis (`PQS`, OSDI 2020):** Selects a concrete database
  row $r_{\text{pivot}}$ (including `NULL` columns), synthesizes complex AST
  predicates guaranteed to evaluate to `TRUE` on $r_{\text{pivot}}$ under
  three-valued rules, and verifies that the engine returns $r_{\text{pivot}}$.

Across `SQLite`, `MySQL`, `PostgreSQL`, `CockroachDB`, and `TiDB`, `SQLancer`
found **over 350 previously unknown logic bugs** (175 in `TLP`, 159 in `NoREC`,
and 99 in `PQS`). Representative root causes include:

1. **Pushing predicates past `OUTER JOIN` null-extension (`PostgreSQL`,
   `MySQL`, `CockroachDB`):** When `LEFT JOIN` fails to match a right-hand row,
   it synthesizes `NULL` columns. If an upper filter $p(R.b)$ is **not
   null-rejecting** (for example, `R.b IS NULL`, `COALESCE(R.b, 0) = 0`, or
   `NOT (R.b = 1 AND FALSE)`), pushing $p$ into the `LEFT JOIN` condition or
   converting the `LEFT JOIN` into an `INNER JOIN` alters the output multiset:
   either the join drops the left row entirely (wrongly converting `LEFT JOIN`
   to `INNER JOIN`), or pushing $p$ into the `ON` clause causes the `LEFT JOIN`
   to emit a null-extended row that the post-join `WHERE` would have filtered or
   vice versa.
2. **Short-circuit boolean/algebraic rewrites unsound on `NULL` (`MySQL`,
   `CockroachDB`, `TiDB`):** Rewriting `x = x` to `TRUE` (unsound when `x IS
   NULL`, where `NULL = NULL` is `UNKNOWN`), rewriting `x NOT IN (y₁, y₂)` via
   De Morgan's law without preserving `UNKNOWN` propagation when any $y_i$ is
   `NULL` (`x <> y₁ AND x <> y₂` evaluates to `UNKNOWN`, not `TRUE`, if $y_2$
   is `NULL`), or simplifying `NOT (a AND b)` using two-valued boolean complements
   in range-index scan builders (`CockroachDB` `optgen` constraint-propagation
   rules).
3. **Partial-index and generated-column `NULL` equivalence mismatches (`SQLite`,
   `PostgreSQL`, `MySQL`):** Using `IS NOT DISTINCT FROM` (where `NULL` equals
   `NULL`) vs. `=` (where `NULL = NULL` is `UNKNOWN`) when matching query
   predicates against partial-index conditions or `UNIQUE` constraints (where
   SQL standard allows multiple `NULL` keys unless `NULLS NOT DISTINCT` is
   specified).

#### 1.2 Bag (Multiset) vs. Set Duplicate Semantics and `COUNT(*)` Empty-Group Bugs (`Cosette`, `UDP`, `WeTune`)

Relational algebra in textbooks is typically defined over **sets** ($R \subseteq
\text{Tuple}$), where idempotence ($R \cup R = R$) and join-projection pushdown
hold unconditionally. Real SQL engines execute over **bags (multisets)** ($R :
\text{Tuple} \to \mathbb{N}$), where every tuple carries a non-negative integer
multiplicity.

When Shumo Chu, Konstantin Weitz, Chenglong Wang, Alvin Cheung, and Dan Suciu
developed `Cosette` (CIDR 2017 / PLDI 2017, built on Rosette and Coq/`HoTTSQL`)
and `UDP` (VLDB 2018, `10.14778/3192965.3192971`, modeling queries as symbolic
semiring/U-expressions over $\mathbb{N}$), and when Zhaoguo Wang et al. built
`WeTune` (SIGMOD 2022, `10.1145/3514221.3526125`), their verification campaigns
highlighted both historical optimizer bugs and hard boundaries in early automated
SQL verifiers:

1. **The Kim (1982) `COUNT` Bug and Empty-Group Aggregation Distortion:**
   Won Kim's classic 1982 paper *"On Optimizing an SQL-like Nested Query"*
   proposed unnesting a correlated `SELECT ... FROM R WHERE R.a = (SELECT
   COUNT(S.b) FROM S WHERE S.c = R.c)` into a `GROUP BY` subquery joined with
   `R` via an inner join. As `Cosette` and `HoTTSQL` mechanized in Coq, this
   rewrite is **unsound whenever a group is empty**: for an $r \in R$ with no
   matching rows in $S$, the correlated subquery returns `COUNT(S.b) = 0` (so if
   `r.a = 0`, $r$ must be returned), whereas `SELECT c, COUNT(b) FROM S GROUP
   BY c` produces **zero rows** for that `c`, causing the unnested join to drop
   $r$! Even replacing `INNER JOIN` with `LEFT OUTER JOIN` fails if `COUNT` is
   evaluated after the outer join as `COUNT(*)` (which counts the single
   null-padded outer-join row and returns `1` instead of `0`) rather than
   `COUNT(S.b)` on a non-nullable column of $S$.
2. **Bag Multiplicity Inflation/Deflation in Semi-Join and Pushdown Rewrites
   (`Apache Calcite`, `Spark SQL`, `MySQL`):**
   Rewriting `SELECT R.* FROM R WHERE EXISTS (SELECT 1 FROM S WHERE R.k = S.k)`
   into `SELECT R.* FROM R INNER JOIN S ON R.k = S.k` is sound only if `S.k` is
   guaranteed to be unique (`UNIQUE NOT NULL`); without a uniqueness constraint,
   multiple matching rows in $S$ multiply the multiplicity of $R$'s rows in the
   output bag. Conversely, pushing `DISTINCT` below a union or join—or eliminating
   a self-join `R JOIN R ON R.k = R.k` when `R.k` is not a primary key—silently
   changes tuple multiplicities from $m^2$ to $m$. `WeTune` (SIGMOD 2022) showed
   that verifying rewrite rules requires explicit SMT constraints over uniqueness,
   not-null, and foreign-key invariants; omitting any of those preconditions in
   `Apache Calcite` or `Spark Catalyst` causes silent duplicate corruption.
3. **Early Verifier Expressiveness Boundaries (`Cosette` & `UDP`):**
   Early versions of `Cosette` and `UDP` themselves exhibited instructive
   verification boundaries: `HoTTSQL`/`Cosette` initially modeled `NULL`-free set
   and bag fragments using homotopy type theory / univalent relations, struggling
   to decide three-valued `NULL` predicates combined with arithmetic or
   correlated outer joins; `UDP` relied on canonicalizing U-expressions ($\sum_t
   \llbracket P(t) \rrbracket$) via syntactic isomorphism and SMT over linear
   integer arithmetic, which could not decide equivalence of queries involving
   non-linear aggregations, `ORDER BY ... LIMIT` tie-breaking, or stateful window
   functions (`ROW_NUMBER() OVER (PARTITION BY ...)`).

#### 1.3 Correlated Subquery Decorrelation (`Apply` Unnesting) and Guard-Ordering Traps

Modern analytical optimizers (`PostgreSQL`, `CockroachDB`, `DuckDB`, `HyPer`,
`Spark SQL`) rely on general subquery decorrelation algorithms (most notably
Thomas Neumann and Alfons Kemper's *"Unnesting Arbitrary Queries"*, BTW 2015)
that push a dependent join (`Apply` operator $\bowtie_{\text{dep}}$) down the
query plan tree using a duplicate-eliminated domain projection $D =
\Pi_{\text{corr}}(L)$.

Two recurring bug classes affect decorrelation and predicate pushdown in
production engines:

1. **Domain-Projection Nullability and Lateral Correlation Mismatches:**
   When pushing $D$ through a `LEFT OUTER JOIN` or `FULL OUTER JOIN` on the
   correlated side, the identity $L \bowtie_{\text{dep}} (T_1 \ T_2) = (L
   \bowtie_{\text{dep}} T_1) \ (D \bowtie_{\text{dep}} T_2)$ requires joining on
   `IS NOT DISTINCT FROM` (`<=>`) over the correlation attributes of $D$. Using
   ordinary equality `=` drops correlation bindings whenever a correlation
   attribute in $L$ is `NULL`, causing correlated rows with `NULL` keys to lose
   their right-hand matches.
2. **Guard-Ordering and Introduced Runtime Exceptions (`Division-by-Zero` /
   `CAST` Traps):**
   In SQL, a query such as `SELECT 100 / x FROM (SELECT x FROM T WHERE x <> 0)
   WHERE 100 / x > 5` is well-defined because the inner filter `x <> 0` guards
   the division `100 / x`. When a cost-based optimizer merges subqueries and
   reorders predicates by selectivity—or when decorrelation evaluates the inner
   plan over a superset domain before applying outer filters—evaluating `100 / x
   > 5` or `CAST(str_col AS INT) > 10` before the guard predicate `x <> 0` or
   `is_numeric(str_col)` triggers a runtime `.divByZero` or `.invalidTextRepresentation`
   abort on rows that the unoptimized query never evaluated (`PostgreSQL` planner
   predicate-ordering hazard; `Spark SQL` / `Calcite` filter-pushdown bugs).

#### 1.4 Incremental View Maintenance (`DBSP`, `Materialize`, `Apache Flink`) Retraction Drift and Watermark Bugs

Incremental View Maintenance (`IVM`) and streaming SQL engines (`Materialize`,
`Feldera` / `DBSP` VLDB 2023 `10.14778/3587136.3587137`, and `Apache Flink`
Table/SQL) compile a relational query $Q(I)$ into a stateful streaming dataflow
graph $Q^\Delta(\Delta I)$ over $\mathbb{Z}$-sets (multisets where each tuple
carries a signed integer weight $w \in \mathbb{Z}$: $+1$ for insertion, $-1$ for
retraction/deletion).

Historical bugs in `Apache Flink` and differential/incremental dataflow systems
fall into three distinct mechanisms:

1. **Missing or Asymmetric Retraction Propagation (`Flink` Upsert/Retract Stream
   Bugs, e.g., `FLINK-9528`, `FLINK-17093`, `FLINK-20374`):**
   In `Apache Flink`'s Blink/Table planner, operators communicate via append-only,
   retract (`+I`, `-U`, `+U`, `-D` changelog kinds), or upsert streams. When a
   non-monotonic operator (such as `GROUP BY` aggregation followed by a `JOIN`,
   `OVER` window, or `ROW_NUMBER() <= k` Top-$N$ rank filter) updates an existing
   key's value, it emits a retraction `-U(old_row)` followed by `+U(new_row)`.
   Bugs in changelog mode inference (`ModifyKindSetTrait` / `UpdateKindTrait`)
   or sink materialization (`SinkUpsertMaterializer`) caused downstream operators
   to drop `-U` retractions, process `+U` before `-U` across hash-partitioned
   channels with different key sharding, or fail to retract previous Top-$N$
   winners, leaving phantom rows permanently materialized in the output view.
2. **Non-Linear / Non-Associative Aggregate State Drift Under Retractions
   (`Materialize` / `DBSP` / `Flink`):**
   For linear group-by aggregates like `COUNT` and integer `SUM`, maintaining a
   $\mathbb{Z}$-set state is an exact ring homomorphism ($\sum (w_i \cdot v_i)$).
   However, for **`MIN` / `MAX`** (which are semilattice operations without
   additive inverses!) or **floating-point `SUM(float8)`**, retracting the
   current minimum value requires maintaining the full ordered multiset of values
   in the group (creating $O(N)$ state amplification unless garbage-collected),
   and retracting floating-point values via subtraction $(S + x) - x$ accumulates
   catastrophic IEEE-754 cancellation drift so that after a burst of insertions
   followed by retracting every row back to the empty table, the materialized
   view outputs a non-zero residual (`1.42e-14`) instead of `0.0` (or fails to
   delete the empty group).
3. **Premature Watermark Advancement and State Garbage-Collection Drops (`Flink`
   / `Timely Dataflow`):**
   In event-time streaming, a watermark $W(t)$ asserts that no future input
   records carry timestamp $t' \le W(t)$. In `Apache Flink`, when a multi-input
   operator (such as `IntervalJoin` or `WindowOperator`) computes its output
   watermark as $\min(W_{\text{left}}, W_{\text{right}})$, bugs in idle-partition
   watermark alignment (`WatermarkStatus.IDLE`) or asynchronous Chandy-Lamport
   checkpoint recovery caused one input's watermark to jump ahead while buffered
   records from the other input were still in flight. Once the watermark crossed
   the window's cleanup timer (`window.maxTimestamp() + allowedLateness`), the
   operator fired the incomplete window and purged its `RocksDBStateBackend`
   entries, silently dropping all remaining valid in-flight events.

#### 1.5 Architectural Lessons for Anneal's Four `trusted/` Primitives in Relational and Streaming Engines

Each of the SQL and IVM failure classes above maps directly onto a specific invariant
in Anneal's four `trusted/lean/` primitives:

- **Primitive 1 (`Language SemObs` & `Partial`):**
  - **Guarding against introduced runtime exceptions (`100 / x` pushdown):** In
    Anneal's `Partial`, `defined = False` (`Partial.ub`) sits at the top of the
    refinement order ($\top$). If `L_Rel` models runtime data traps (division by
    zero, invalid `CAST`, regex compile errors) either as `defined = False` or
    as an explicit `.aborted err` variant in `SemObs` (`obs : Out → SemObs`),
    then `Compiles` ($L_{\text{Phys}}.\text{sem}(P) \le \pi(L_{\text{Rel}}.\text{sem}(Q))$)
    **categorically forbids** a predicate-pushdown or decorrelation pass from
    turning a query that succeeds (`defined = True`, `.committed rows`) into a
    plan that traps (`.aborted .divByZero` or `Partial.ub`).
  - **Three-valued Kleene logic in `SemObs`:** Defining `Query` over nullable
    tuples (`Option Val`) and three-valued evaluation (`KleeneBool : .true |
    .false | .unknown`) inside `L_Rel.sem` makes `TLP` (Ternary Logic
    Partitioning) a theorem of the semantic model rather than an ad-hoc fuzzer
    oracle: any rewrite rule sound under `Compiles` must preserve `SemObs` on
    all `NULL` combinations, automatically rejecting `x = x ↦ TRUE` and
    non-null-rejecting outer-join pushdowns.
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, &
  `Abstracts`):**
  - **Bag multiplicity and empty-group preservation via `obs_decodeOut`:** By
    fixing `SemObs` to the exact multiset of output rows (`Multiset Tuple`) and
    requiring `obs_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ =
    L₁.obs o₁`, no physical plan or `egglog` rewrite can alter row multiplicities
    (ruling out unguarded semi-join-to-inner-join rewrites) or drop empty groups
    in Kim-style `COUNT` decorrelation.
  - **DBSP $\Delta$-circuit correctness via stream-codec retraction:** For IVM,
    the `BehaviorCodec` between batch relational semantics $L_{\text{Rel}}$ and
    streaming $\mathbb{Z}$-set semantics $L_{\text{DBSP}}$ defines `encodeQuery`
    by splitting a database history into $\Delta D_t$ steps and `decodeOut` by
    integrating ($\mathcal{I}(\Delta O) = \sum_{t} \Delta O_t$) the emitted
    changelog stream (requiring weights to be non-negative and `+U`/`-U` pairs to
    be balanced; otherwise `decodeOut = none`). `Compiles` then directly proves
    the fundamental DBSP invariant $\mathcal{I}(Q^\Delta(\Delta I)) =
    Q(\mathcal{I}(\Delta I))$ and rejects Flink-style missing retractions!
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`):**
  - **Blocking the "Abort-All / Hold-Watermarks-Forever" loopholes:** A query
    optimizer that compiles complex joins to `.aborted .outOfMemory` or a Flink
    pipeline that holds watermarks at $-\infty$ forever is refuted by
    `ProductiveOn SchemaInv P_phys` + `EventualBehaviorOf`, which requires
    finite-step termination with a valid decoded output (`decodeOut o₂ = some
    o₁`) on all database instances and bounded-lateness streams satisfying
    `SchemaInv` (which itself must be non-empty by `InhabitedPre SchemaInv`).
- **Primitive 4 (`VerificationResult` / `ScopedVerificationResult` &
  `TrustPolicy`):**
  - In a rule-based optimizer (`Apache Calcite`, `CockroachDB` `optgen`, or an
    `egglog` equality-saturation certifier) applying a chain of rewrite steps
    $P_0 \to P_1 \to \dots \to P_m$, positive per-obligation scoping (`ob.id ∈
    waived ∨ ob.prop`) allows verified core relational/Kleene rules to run at
    `waived = []` while explicitly isolating any unverified vendor UDF rule or
    floating-point `SUM` reassociation waiver (`waived := [.fpSumReassoc]`)
    without contaminating the soundness of the surrounding join/decorrelation
    plan.

### Historical Failure Analysis 2. Storage Engines, Distributed Consensus, and Kubernetes Controller Failures

`Basis: normative + documentation + source + derived`

#### 2.1 Verified Storage Boundary Gaps: Unverified FUSE/C Shims and Volatile Disk Write-Cache Reordering (`FSCQ`, `Yggdrasil`, `Perennial`)

Even landmark formally verified file systems have suffered bugs at the boundary
between their mechanized proof models and the unverified host/hardware
environment:

1. **`FSCQ` (SOSP 2015, `10.1145/2815400.2815402`) and `Perennial` / `GoJournal`
   (SOSP 2019 / OSDI 2020) Unverified Shim and Extraction Seams:**
   `FSCQ` mechanized Crash Hoare Logic (`CHL`) in Coq and extracted the verified
   Coq specification to Haskell, executing in user space on top of a `FUSE` C/Haskell
   binding layer and raw block device I/O wrapper. Subsequent analysis by the MIT
   PDOS group (during `DFSCQ` SOSP 2017 and `Perennial` SOSP 2019) identified
   concrete defects along this boundary:
   - **Haskell integer/buffer marshaling and FUSE protocol assumptions:** In
     `FSCQ`, the unverified Haskell FUSE driver and block-device syscall layer
     initially contained bugs in multi-block write offset calculations and error-code
     translations, and because Coq extraction erased static type proofs before the
     unverified Haskell/C FUSE glue executed, a mismatch in how `stat` / `rename`
     flags were unpacked could bypass the Coq theorem's preconditions.
   - **Asynchronous disk write-back vs. barrier modeling:** Early crash models
     assumed synchronous sector writes enhanced with explicit `flush` barriers.
     In `DFSCQ` (SOSP 2017), modeling page-cache write-back asynchronous queues
     revealed that if an application calls `fsync(fd)` on a file whose directory
     entry was newly created, flushing the file's data blocks and inode without
     also flushing the parent directory's log/inode barrier allows a power cut
     to leave an allocated inode unreachable after reboot.
2. **`Yggdrasil` (OSDI 2016) SMT Crash-Refinement and Unverified Cython/FUSE
   Wrapper Gaps:**
   `Yggdrasil` verified crash refinement ($\forall \text{crash}, \text{Recover}(\text{Impl})
   \subseteq \text{Spec}$) for `Yxv6` using Z3 decision procedures over bitvectors
   and arrays, compiling Python/Z3 models via Cython to C. While the Z3
   verification caught subtle bugs in `xv6` (such as freeing a data block in the
   on-disk bitmap before clearing the inode pointer to that block, which allows a
   crash + realloc to cross-link two files to the same physical disk block!),
   `Yggdrasil`'s TCB still trusted: (a) the translation from the Python DSL to
   both Z3 SMT formulas and Cython C code (a dual-emitter seam analogous to
   Anneal's `Mir.lean` vs. `Prog.s` seam), (b) the unverified C FUSE dispatch
   loop, and (c) the hardware assumption that an NVMe/SATA controller honors
   `fdatasync` / `FLUSH CACHE EXT` without silently dropping volatile drive-cache
   writes when `FUA` (Force Unit Access) is disabled.

#### 2.2 LSM-Tree Compaction and Range-Delete Tombstone Resurrection Bugs (`RocksDB` and `PebblesDB`)

Log-Structured Merge-tree (`LSM`) storage engines (`RocksDB`, `PebblesDB` SOSP
2017, `CockroachDB` `Pebble`) do not overwrite or delete keys in place. Instead,
`Delete(k)` appends a point tombstone `(k, seq, kTypeDeletion)` and
`DeleteRange(begin_key, end_key)` appends a range tombstone `[begin_key,
end_key) @ seq` to the active memtable and Write-Ahead Log (`WAL`). Background
**compaction** merges SSTables from level $L_i$ into $L_{i+1}$ and garbage-collects
tombstones only when two invariants simultaneously hold:
1. **Snapshot Visibility Invariant:** The tombstone's sequence number `seq` is
   strictly older than the earliest active MVCC snapshot (`seq <
   earliest_snapshot`); otherwise, an active reader holding `snap_seq < seq`
   could see keys hidden or exposed inconsistently.
2. **Bottommost Level / Lower-Level Disjointness Invariant:** No SSTable in any
   deeper level $L_j$ ($j > i+1$) has key bounds overlapping the tombstone's key
   So long as an older entry `(k, seq_old, kTypeValue)` with `seq_old < seq`
   resides in a deeper level $L_j$, dropping the tombstone at $L_{i+1}$ causes
   subsequent `Get(k)` or `Iterator::Seek(k)` calls to fall through to $L_j$ and
   **resurrect the deleted key**!

Across `facebook/rocksdb`'s production history, violating the interaction between
range tombstones, SSTable boundary clipping, and snapshot sequence numbers
produced a series of severe data-corruption and key-resurrection bugs:

- **Premature Range-Tombstone Dropping Across Snapshots (`facebook/rocksdb#4747`,
  `#4760`, `#5616`):** In `RocksDB` v5.x–v6.x (`RangeDelAggregator` /
  `CompactionIterator`), when a `DeleteRange` tombstone spanned multiple
  snapshots or was fragmented across SSTable file boundaries during compaction,
  `CompactionIterator::PrepareOutput` miscalculated which snapshot stripe a
  fragmented range tombstone belonged to, dropping range tombstones whose `seq`
  was still needed to mask keys at lower levels or violating snapshot isolation
  for concurrent iterators.
- **SSTable Boundary Truncation Bleed and Off-by-One Clipping
  (`facebook/rocksdb#7703`, `#10250`):** When splitting compaction output into
  multiple SSTables at target file-size boundaries, `RocksDB` truncates a spanning
  range tombstone `[a, z) @ seq` at the output SSTable's `largest_key`. Because
  SSTable `largest_key` metadata stores an **internal key** `(user_key, seq,
  type)`, off-by-one sequence-number comparisons at the truncation boundary either
  left a 1-key gap `(user_key, seq_older)` uncovered between adjacent SSTables
  (resurrecting `user_key`) or extended the tombstone to delete a newer version
  `(user_key, seq_newer)` written after the `DeleteRange`!
- **`PebblesDB` Fragmented LSM Guards (SOSP 2017):** `PebblesDB` introduced
  *guards* to partition LSM levels into disjoint key intervals without rewriting
  full levels. However, when guards are inserted dynamically and SSTables are
  lazily split across compaction rounds, failing to propagate range or point
  tombstones into every sub-guard interval that overlaps a deeper uncompacted
  guard resurrects stale values during range scans (`Seek` merging across guard
  iterators).

#### 2.3 Distributed Consensus and Transactional Isolation Failures Under Fault Injection (`Raft`, `CockroachDB`, `TiKV`, `MongoDB` via `Jepsen` and `Elle`)

Distributed consensus engines (`Raft`, `Multi-Paxos`) and distributed
transactional databases (`CockroachDB`, `TiKV`/`TiDB`, `MongoDB`, `etcd`) must
preserve linearizability and transactional isolation across asynchronous network
partitions, leader failovers, and dynamic cluster membership reconfigurations.
Historical verification and `Jepsen`/`Elle` (Kingsbury & Alvaro, VLDB 2020,
`10.14778/3457390.3457396`) investigations exposed four canonical protocol and
implementation failures:

1. **The Raft "Figure 8" Previous-Term Commit Bug (Ongaro & Ousterhout ATC 2014):**
   In `Raft`, if a newly elected leader in term $T$ immediately advances
   `commitIndex` for an uncommitted log entry from an **older term** $T' < T$ as
   soon as that entry is stored on a majority of servers—without first appending
   and replicating at least one entry from its **own current term $T$**—a
   subsequent leader elected in term $T+1$ (whose log has a higher last-entry
   term on a different majority quorum) can overwrite the "committed" entry from
   term $T'$, causing split-brain state-machine divergence. Multiple early Raft
   implementations tested by `Jepsen` omitted the `log[N].term == currentTerm`
   guard on `commitIndex` advancement and lost committed writes under asymmetric
   partitions.
2. **Diego Ongaro's Single-Server Raft Membership-Change Bug (2015 Erratum to
   Ongaro PhD Dissertation §4.1):**
   In his 2014 PhD dissertation, Ongaro proposed simplifying Raft cluster
   reconfiguration from two-phase *Joint Consensus* ($C_{\text{old,new}}$) to
   single-server additions/removals ($C_{\text{old}} \to C_{\text{new}}$
   differing by 1 node), arguing that because any majority of $C_{\text{old}}$
   and $C_{\text{new}}$ overlap on a single change, joint consensus was
   unnecessary. In 2015, Amosjel and Ongaro discovered a **protocol-level
   safety bug** when two single-server membership changes are pipelined or when
   a leader failure occurs mid-change: suppose $C_0 = \{s_1, s_2, s_3\}$. Leader
   $s_1$ appends $C_1 = \{s_1, s_2, s_3, s_4\}$ (not yet committed), then crashes;
   $s_3$ is elected leader in a new term using votes from $\{s_2, s_3\}$ (which
   have not seen $C_1$) and appends $C_2 = \{s_1, s_2, s_3, s_5\}$. Now $C_1$ and
   $C_2$ can have disjoint majorities ($\{s_1, s_2, s_4\}$ vs. $\{s_3, s_5\}$),
   allowing two concurrent leaders unless a new leader is forbidden from
   proposing a configuration change until it has committed a no-op entry in its
   own term! Both `etcd/raft` (`CockroachDB`) and `TiKV` (`tikv/raft-rs`) had to
   adopt explicit joint-consensus quorums and strict `pending_conf_index` guards
   after encountering reconfiguration split-brains.
3. **`MongoDB` v3.2–v3.6 Rollback and Read-Concern Majority Bugs (`Jepsen`
   2015–2020 & MongoDB TLA+ Verification):**
   In early `MongoDB` replica sets (`pv0` and early `pv1` before TLA+ model
   checking of `ReplSet`), replication pulled oplog entries asynchronously from
   any secondary rather than enforcing strict leader-to-follower prefix matching,
   and `readConcern: "local"` / `"majority"` decoupled dirty in-memory
   `WiredTiger` visibility from the majority-committed oplog point (`SOLR`/
   rollback bugs). `Jepsen` demonstrated that under network partitions,
   `MongoDB` acknowledged writes that were subsequently rolled back when the old
   primary rejoined, and `Elle` (VLDB 2020) further uncovered repeatable-read
   and snapshot-isolation anomalies in `MongoDB` v4.2.6 when client sessions
   omitted explicit causal-consistency timestamps (`afterClusterTime`).
4. **`CockroachDB` and `TiKV`/`TiDB` Timestamp-Cache and Lock-Resolution
   Isolation Bugs (`Jepsen` & `Elle`):**
   - In `CockroachDB` beta (`2016–2017` Jepsen audit), clock-offset assumptions
     and incomplete range-lease transfers during Raft leader elections allowed
     two nodes to serve reads/writes for the same key range during lease
     handoff, violating single-key linearizability.
   - In `TiDB`/`TiKV` (`Elle` VLDB 2020), Percolator-style two-phase commit
     (`Prewrite` $\to$ PD Timestamp Oracle `commit_ts` $\to$ `Commit`) suffered
     from an isolation bug when pessimistic/optimistic lock cleanup raced with
     schema metadata changes or when `ReadIndex` bypassed the Raft log without
     checking whether a higher-term leader had already committed a conflicting
     write, yielding `G1c` (circular information flow) and `G-single` (read skew)
     cycles in `Elle`'s dependency graph.

#### 2.4 Kubernetes Operator Stale-Informer-Cache TOCTOU, Orphan Leaks, and Infinite Reconciliation Livelocks (`Sieve` OSDI 2022 and `Anvil` OSDI 2024)

Kubernetes operators (`Cassandra-Operator`, `ZooKeeper-Operator`,
`RabbitMQ-Operator`, `MongoDB-Operator`, `Percona-XtraDB-Operator`, `Yugabyte-Operator`)
implement level-triggered control loops (`reconcile(ctx, req)`) that read
cluster state from a local in-memory **informer cache** (populated asynchronously
via `Watch` streams from `kube-apiserver`/`etcd`) and issue imperative API
mutations (`Create`, `Update`, `Delete`, `Patch`).

Xudong Sun et al. systematically analyzed and verified these operators in two
milestone studies—**`Sieve`** (OSDI 2022, which discovered **28 new safety and
liveness bugs across 10 widely used Kubernetes operators**) and **`Anvil`**
(OSDI 2024 Jay Lepreau Best Paper, which built formally verified Kubernetes
controllers for ZooKeeper, RabbitMQ, and FluentBit in `Verus` using **Eventually
Stable Reconciliation (`ESR`)**):

1. **Time-of-Check-to-Time-of-Use (`TOCTOU`) Stale-Cache Overwrites and Data
   Loss (`Sieve` Stale-State Bug Class):**
   Suppose at step $t_1$, an operator reconciler creates a `PersistentVolumeClaim`
   (`PVC-0`) or scales a `StatefulSet` from 3 to 4 pods on `kube-apiserver`. At
   step $t_2$, another event triggers a second invocation of `reconcile` **before**
   the `Watch` notification for step $t_1$ has arrived at the operator's local
   informer cache. Reading the stale cache (`r.Get` / `r.List`), the operator
   believes `PVC-0` does not exist (or that the `StatefulSet` still has 3 pods)
   and re-issues a conflicting creation, overwrites a newer `Spec` with a stale
   in-memory struct (Without a `resourceVersion` precondition check!), or
   triggers a premature scale-down that deletes an active database node's
   underlying storage volume.
2. **Unobserved Intermediate State Transitions (`Sieve` Time-Travel /
   Skipped-State Bug Class):**
   Because Kubernetes `Watch` streams coalesce or drop intermediate updates when
   watches reconnect (`410 Gone` relist), an operator written with implicit
   **edge-triggered** assumptions (for example, waiting to observe `Pod.Status.Phase
   == Running` before initializing a Raft peer, or waiting to see a temporary
   annotation before removing a finalizer) permanently stalls when the cluster
   transitions `Pending -> Running -> Terminating` between two informer snapshots.
3. **Orphan Resource Leaks on Crash / Partial Failure Before Finalizer
   Registration (`Anvil` OSDI 2024):**
   When an operator provisions an external resource (such as an AWS RDS instance,
   load balancer, or sub-resource `Secret`) before persisting a Kubernetes
   `finalizer` or `ownerReference` in `etcd`, a crash or transient `500 Internal
   Server Error` right after the external creation leaves an untracked orphan
   resource that continues billing or exposing network ports even after the parent
   Custom Resource (`CR`) is deleted.
4. **Infinite Reconciliation Oscillation / Livelock (`Sieve` & `Anvil`):**
   Two controllers watching overlapping fields—or a single controller whose map/slice
   serialization order (`EnvVars`, volume mounts, or floating-point CPU resource
   strings `"100m"` vs. `"0.1"`) differs from `kube-apiserver`'s canonicalized
   admission defaults—detect a spurious diff on every `reconcile` tick, issuing
   an endless stream of `Update` calls that increment `resourceVersion`, trigger
   a new `Watch` event, and spin `kube-apiserver` and `etcd` at 100% CPU forever
   (`EventualOut.diverges`).

#### 2.5 Architectural Lessons for Anneal's Four `trusted/` Primitives in Storage, Consensus, and Control Loops

- **Primitive 1 (`Language SemObs` & `Partial`):**
  - **All-prefix availability and durability invariants:** In storage engines and
    Kubernetes controllers, correctness is not merely a property of the final
    quiescent state; a rolling update that drops `activePods` below
    `PodDisruptionBudget` at step 4 before recovering at step 8 has caused a
    production outage. Because Anneal's `BehaviorOf` and `EventualBehaviorOf`
    define `defined : Prop` by quantifying over **every finite step prefix $n$**
    (`∀ n tr out, ReachesPrefix M p init n init tr out → out.isSafe`), encoding
    continuous safety invariants (no key resurrection, no split-brain commit at
    any index, `activeReplicas >= minAvailable` at every step) into the transition
    guard `StepResult.failed` guarantees **zero-downtime intermediate safety** across
    all prefixes.
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, &
  `Abstracts`):**
  - **Closing the unverified shim / dual-emitter gap (`FSCQ` / `Yggdrasil`):**
    Just as `Yggdrasil` translated a Python model into both Z3 and Cython C, and
    Anneal's `x86-backend-pipeline` branch (`5fc1139f2208b3c9cfb513573c4a731cc32bb457`) initially translated MIR to
    both `Mir.lean` and `.anneal/Prog.s` in unverified Rust, any unverified shim
    between the verified model and the executed code is a single point of failure.
    Anneal's **proof-gated compilation** (`Compiles L_Spec L_Impl codec`) and
    single-source `.olean`-bound code emission
    (`anneal-rustc-obligation-inventory-and-single-source-codegen-2026`) keep the
    concrete implementation inside the refinement chain rather than trusting an
    external extractor.
  - **Linearizability and isolation (`Elle` VLDB 2020) via `Compiles`:** When the
    source language $L_{\text{Serial}}$ models a single-node atomic transaction
    executor and the target language $L_{\text{Dist}}$ models distributed Raft /
    2PC replicas, `Compiles L_Serial L_Dist codec` requires that for every
    asynchronous network schedule, the client-visible transaction history (`SemObs`)
    decoded from $L_{\text{Dist}}$ is a valid serial history of $L_{\text{Serial}}$,
    automatically ruling out `Elle`'s `G1c`/`G-single` isolation cycles and Raft
    Figure 8 split-brains.
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`):**
  - **`StepResult.externalCall` as the universal boundary guard for WAL, LSM
    compactions, and Kubernetes `resourceVersion` preconditions:**
    - In a storage engine, every disk write or SSTable compaction emit is an
      `externalCall (boundaryInv : Bool) branches`: `boundaryInv` checks
      `flushedLSN >= page.pageLSN` (the ARIES Write-Ahead Logging rule) and, for
      LSM tombstone drops, `tombstone.seq < earliest_snapshot ∧
      disjointFromDeeperLevels(tombstone.range)`. Any `RocksDB` `#4747`/`#7703`
      premature tombstone drop evaluates `boundaryInv = false` and steps
      immediately to `.failed`!
    - In a Kubernetes operator, every informer read and `kube-apiserver` write is
      an `externalCall`: `branches` demonically supplies arbitrary lagging
      informer states (modeling `Sieve`'s stale-cache perturbations), while
      `boundaryInv` on `Update`/`Delete` requires an explicit `resourceVersion`
      optimistic-concurrency check and requires finalizer registration before
      external cloud resource allocation (`Anvil` ESR safety).
  - **`ProductiveOn` + `EventualBehaviorOf` for ESR convergence and
    anti-abort-all:**
    - Rules out the trivial transaction manager that aborts 100% of transactions
      and the trivial Kubernetes controller that returns `RequeueAfter(∞)`: under
      post-GST / quiescent conditions (`pre`), `ProductiveOn` +
      `EventualBehaviorOf` forces finite-step convergence (`.terminated`) to a
      state satisfying `DesiredSpec`, refuting infinite reconciliation livelocks!
- **Primitive 4 (`VerificationResult` / `ScopedVerificationResult` &
  `TrustPolicy`):**
  - Separates unconditional safety obligations (which must hold under arbitrary
    message loss, crashes, and stale informer caches with `waived = []`) from
    conditional liveness/convergence obligations that depend on hardware/network
    fairness assumptions (such as `GST`—Global Stabilization Time—or bounded disk
    I/O completion, tracked as explicit `TCBModel` parameters or scoped policy
    entries).

### Historical Failure Analysis 3. Network Data/Control Planes (`P4` / `BGP`) and Cloud IAM / Differential Privacy Failures

`Basis: normative + documentation + source + derived`

#### 3.1 P4 Compiler Miscompilations and Specification Ambiguities (`Gauntlet` OSDI 2020 and `Petr4` POPL 2021)

Programmable network switches (Intel/Barefoot Tofino ASICs, SmartNICs, `BMv2`
software switches) execute packet-processing pipelines written in `P4-16` and
compiled by `p4c` into fixed-stage hardware Match-Action Tables (`MATs` backed
by TCAM and SRAM) and VLIW action engines. Because line-rate packet pipelines
have no general-purpose CPU loops or dynamic heap, `p4c` performs aggressive AST
inlining, side-effect hoisting, copy propagation, dead-code elimination, and
header-validity analysis.

Two foundational verification projects—**`Gauntlet`** (Fabian Ruffy, Tao Wang,
and Anirudh Sivaraman, OSDI 2020, `arXiv:2006.01074`, which applied SMT-based
translation validation across every IR pass of `p4c`) and **`Petr4`** (Ryan
Doenges et al., POPL 2021, `10.1145/3434304`, which mechanized a formal
operational semantics for `P4-16`)—uncovered **96 distinct compiler bugs** (62
crash bugs and 34 silent miscompilations across `p4c`, `BMv2`, and the
proprietary Barefoot Tofino compiler) and dozens of ambiguities in the official
`P4-16` specification:

1. **Side-Effect Ordering Corruption in Match-Action Table (`MAT`) Keys and
   Action Arguments (`Gauntlet` OSDI 2020):**
   In `P4-16`, expressions inside `table` match keys (`key = { f(hdr.ipv4.ttl) :
   exact; }`) or `switch (t.apply().action_run)` blocks can invoke functions or
   externs that mutate packet headers or metadata as a side effect. `p4c`'s
   `SideEffectOrdering` and `LocalCopyProp` passes hoisted side-effecting calls
   out of table keys or reordered them across short-circuiting boolean operators
   (`&&` / `||`) and array slice assignments (`hdr.eth.srcAddr[47:24]`),
   causing the hardware pipeline to match against the **post-mutation** header
   value instead of the **pre-mutation** value (or vice versa) and silently
   forwarding packets to the wrong egress port.
2. **Header Validity Bit (`isValid()`) Corruption and Uninitialized Header Reads
   (`Gauntlet` & `Petr4`):**
   Every `P4` header struct carries a hidden 1-bit validity flag (`valid : Bool`),
   set by `packet.extract(hdr.ipv4)` or `hdr.ipv4.setValid()` and cleared by
   `hdr.ipv4.setInvalid()`. Reading or writing a field of an invalid header
   (`!hdr.ipv4.isValid()`) produces an undefined value in `P4-16`, and emitting an
   invalid header in the deparser is a no-op. `Gauntlet` discovered multiple
   miscompilations in `p4c` and the Barefoot Tofino back end where:
   - Dead-code elimination or struct initialization passes (`SimplifyDefUse`,
     `RemoveMiss`) dropped a `.setValid()` / `.setInvalid()` assignment when
     none of the header's *data fields* were subsequently read before deparse,
     causing the deparser to silently drop an encapsulated tunnel header (or emit
     a deleted header onto the wire!).
   - Struct copy assignments (`hdr_a = hdr_b`) copied the data fields without
     copying the validity bit in certain Tofino PHV (Packet Header Vector)
     container allocations.
3. **Undefined Parser State Fallthrough and Header-Stack Out-of-Bounds Indexing
   (`Petr4` POPL 2021):**
   `Petr4`'s mechanized operational semantics exposed gaps where the `P4-16`
   specification left behavior contradictory or implementation-defined:
   - When a `parser` state finishes executing its statements without an explicit
     `transition` statement, does it implicitly transition to `reject` (dropping
     the packet) or `accept`? Different targets disagreed.
   - When indexing into a P4 header stack (`hdr.mpls[idx]`) with an out-of-bounds
     runtime index or pushing/popping (`push_front`, `pop_front`), `p4c`'s
     constant-folding passes wrapped or truncated indices differently from the
     `BMv2` software switch and Tofino hardware.

#### 3.2 BGP Persistent Route Oscillation, Dispute Wheels, and MED Non-Determinism (`Griffin-Shepherd-Wilf` 1999 and `RFC 3345`)

At the network control-plane layer, Autonomous Systems (`ASes`) run the Border
Gateway Protocol (`BGP-4`) to exchange reachability paths. Rather than computing
shortest paths over a global scalar metric (like `OSPF`/Dijkstra), each BGP
speaker applies local policy rankings (`LOCAL_PREF`, AS-path length, `ORIGIN`,
`MED`—Multi-Exit Discriminator, eBGP over iBGP, IGP cost to `NEXT_HOP`) and
advertises only its single best route to peers.

Two classic failure mechanisms cause BGP control planes to **diverge into
permanent oscillation** or converge to **non-deterministic routing tables** that
depend on the temporal arrival order of messages:

1. **The Stable Paths Problem (`SPP`) and Dispute Wheels (Griffin, Shepherd, &
   Wilf, ICNP 1999 / SIGCOMM 1999 / IEEE/ACM ToN 2002):**
   Timothy Griffin, Bruce Shepherd, and Gordon Wilf formalized policy-based
   routing as the Stable Paths Problem (`SPP`) and proved that checking whether a
   set of local BGP preference policies has a stable routing assignment is
   **NP-complete**, and that even when a unique stable solution exists,
   asynchronous BGP message passing can diverge forever if the policy graph
   contains a cyclic preference dependency structure called a **Dispute Wheel**
   (where AS $u_0$ prefers a path through $u_1$ over its direct path, $u_1$
   prefers $u_2$, ..., and $u_{k-1}$ prefers $u_0$). Under a single link failure
   or policy edit, routers trapped in a Dispute Wheel endlessly advertise and
   withdraw routes in an infinite loop (`EventualOut.diverges`), causing packet
   blackholes and route-flap damping cascades.
2. **iBGP Route Reflection + `MED` Persistent Oscillation and Non-Determinism
   (`RFC 3345`, McPherson, Gill, Walton, & Retana, August 2002):**
   Even **inside a single AS** (where `LOCAL_PREF` policies are uniform),
   combining iBGP **Route Reflection** (`RFC 4456`, where a route reflector
   advertises only its best path rather than a full mesh) with the `MED`
   attribute causes persistent route oscillation documented in **`RFC 3345`**.
   Because `MED` is compared *only* among paths received from the **same
   neighboring AS** (whereas IGP metric to `NEXT_HOP` is compared across *all*
   ASes), the BGP best-path relation is **non-transitive** ($A \prec B$ via
   IGP cost across different ASes, $B \prec C$ via lower `MED` within the same
   AS, and $C \prec A$ via IGP cost!). In a 3-cluster route-reflector topology
   (`RFC 3345` §2), choosing $A$ hides $C$, allowing $B$ to beat $A$, which
   re-exposes $C$ to beat $B$, oscillating ad infinitum. Furthermore, without
   `bgp deterministic-med`, the route selected by a Cisco/Juniper router depends
   on the chronological order in which routes arrived in the RIB (`age`-based
   tie-breaking), so two identically configured routers in the same AS converge
   to incompatible forwarding tables and create a **permanent forwarding loop**.

#### 3.3 Cloud IAM Authorization Policy Verification and Pre-Release Bug Discovery (`AWS Cedar` OOPSLA 2024)

Fine-grained cloud authorization engines (`AWS Cedar` powering Amazon Verified
Permissions and AWS Verified Access, Google `Zanzibar`, `Open Policy Agent` Rego)
evaluate security policies on every API request. Joseph W. Cutler, Craig Disselkoen,
Aaron Eline, Shaobo He, Kyle Headley, Michael Hicks, Kesha Hietala, Eleftherios
Ioannidis, John Kastner, Anwar Mamat, Darin McAdams, Matt McCutchen, Neha Rungta,
Emina Torlak, and Andrew Wells reported in *"Cedar: A New Language for Expressive,
Fast, Safe, and Analyzable Authorization"* (OOPSLA 2024, `arXiv:2403.04651`) how
they applied **Verification-Guided Development (`VGD`)**—mechanizing Cedar's
evaluator, authorizer, and validator in **Lean 4** while running **Differential
Random Testing (`DRT`)** (`cargo-fuzz` + Lean 4 FFI oracle executing at ~5 $\mu$s
per test case) against the production Rust implementation (`cedar-policy`).

Even though Cedar was designed from scratch by formal-methods experts alongside
its Lean 4 specification, the Lean 4 proofs and DRT campaign uncovered **25 real
bugs before production release** (**4 bugs during interactive Lean 4 proofs** and
**21 bugs during DRT and property-based testing**):

1. **4 Validator Soundness Bugs Caught During Interactive Lean 4 Proofs:**
   Cedar's static type/schema validator is intended to guarantee that any policy
   accepted by `validate(policy, schema)` will never encounter a runtime type
   error or missing-attribute error during authorization (`validate_sound`).
   While attempting to prove `validate_sound` in Lean 4, the authors discovered
   four edge cases where the validator unsoundly accepted ill-typed policies:
   - **Lub (Least Upper Bound) record-attribute optionality mismatch:** When
     computing the least upper bound of two record types in an `if-then-else`
     branch (`if c then {a: 1} else {}`), the validator failed to mark absent
     attributes as optional or failed to check capability sets across branches,
     allowing a subsequent `.a` access to crash at runtime.
   - **Short-circuiting boolean capability propagation (`&&` / `||`):** The
     validator tracks a set of "known-present" optional attributes (`has` guards,
     such as `principal has dept && principal.dept == "eng"`). A bug in how
     capability sets were intersected/unioned across negations (`!`) and `||`
     allowed an unguarded optional attribute read `principal.dept` to pass
     validation when `principal has dept` was false!
   - **Entity-type hierarchy (`in`) and unspecified entity handling:** Edge cases
     in checking `principal in Group::"admins"` when the schema defined empty
     entity sets or action groups.
2. **21 Evaluator, Parser, and Partial-Evaluation Bugs Caught by Lean 4 DRT:**
   Running millions of structure-aware fuzz inputs (`DRT`) comparing the Lean 4
   definitional evaluator against the Rust `cedar-policy` crate exposed 21
   discrepancies:
   - **Error-masking in `forbid` vs. `permit` (`Deny-Trumps-Allow` corner cases):**
     In Cedar, if a policy throws a runtime evaluation error (e.g., integer
     overflow in `ip()` or `decimal()` extension functions or missing entity),
     that individual policy is skipped while recording diagnostics, and `forbid`
     still overrides `permit`. Discrepancies in error short-circuiting and
     extension-function overflow checks caused Rust and Lean to disagree on error
     reporting or authorization outcomes.
   - **Unicode/escaping and namespace resolution in the parser:** Differences in
     how `\u{...}` escapes, wildcard `*` patterns in `like` expressions
     (`"foo*bar"`), and namespace prefixes were normalized between the CST-to-AST
     lowering passes in Rust and Lean.

#### 3.4 Floating-Point Discrete Sampling and Sensitivity Underestimation Attacks on Differential Privacy (`Mironov` CCS 2012 & `Casacuberta et al.` CCS 2022)

Differential Privacy (`DP`) systems (`OpenDP`, IBM `Diffprivlib`, `Chorus`,
Google `PipelineDP`) execute statistical queries over sensitive datasets by
bounding the query's global sensitivity $\Delta f = \max_{D \sim D'} \|f(D) -
f(D')\|_1$ and adding random noise drawn from a Laplace ($\text{Lap}(\Delta f /
\epsilon)$) or Gaussian distribution so that for all neighboring datasets $D \sim
D'$ and output sets $S$:
$$\Pr[\mathcal{M}(D) \in S] \le e^\epsilon \Pr[\mathcal{M}(D') \in S] + \delta$$

Two landmark papers proved that **translating textbook real-number ($\mathbb{R}$)
DP proofs directly into IEEE-754 floating-point (`f64`) software completely
destroys differential privacy ($\epsilon = \infty$)**:

1. **Ilya Mironov's Least-Significant-Bit (`LSB`) Floating-Point Attack (CCS
   2012, `10.1145/2382196.2382264`):**
   Standard implementations generate $\text{Lap}(b)$ noise via inverse transform
   sampling: drawing a uniform IEEE-754 double $U \in (0, 1)$ and computing
   $X = -b \ln(U)$. Because IEEE-754 `f64` has only 53 bits of significand and
   `ln(U)` is evaluated in finite precision, the set of reachable floating-point
   values $-b \ln(U)$ is **sparse**: over $99\%$ of adjacent `f64` bit patterns
   in certain intervals can *never* be produced for a given true count $f(D) =
   c$, and the set of possible `f64` outputs shifts when $f(D)$ changes from $c$
   to $c + 1$! By observing the **least significant bits** of the returned `f64`
   noisy sum, an attacker immediately rules out $f(D) = c$ in a single query
   (violating pure $\epsilon$-DP with $\epsilon = \infty$) and reconstructs the
   exact private record in a few queries. Fixing this required replacing
   continuous `f64` Laplace sampling with exact discrete or snapping mechanisms
   (such as Mironov's **Snapping Mechanism** or Canonne-Kamath-Steinke's exact
   rational **Discrete Laplace / Discrete Gaussian** samplers).
2. **Casacuberta, Shoemate, Vadhan, and Wagaman's Widespread Sensitivity
   Underestimation Attacks on `OpenDP`, `Diffprivlib`, and `Chorus` (CCS 2022,
   `10.1145/3548606.3560708`):**
   Even after libraries adopted discrete or snapping noise samplers, Sílvia
   Casacuberta et al. discovered that **every major open-source DP library
   (`OpenDP`, `Diffprivlib`, `Chorus`) underestimated the sensitivity $\Delta f$
   of basic `SUM` and `MEAN` queries over bounded floating-point or integer data**,
   allowing exact membership-inference attacks:
   - **Non-Associativity and Rounding Drift in Bounded `f64` Sums (`Diffprivlib`,
     `OpenDP`):** Over real numbers, if a user contributes one value $x \in [L,
     U]$ to a dataset $D$, the sensitivity of $\sum_{y \in D} y$ is $\Delta f =
     U - L$. Over IEEE-754 `f64`, floating-point addition is **neither
     associative nor distance-preserving**: if $D$ contains $N$ large numbers that
     shift the floating-point exponent (ULP spacing) and then cancel out, inserting
     a single record $x = 0$ at the start of the summation array changes the
     rounding of every subsequent addition! Consequently, the true IEEE-754
     sensitivity of `SUM(f64)` grows with the dataset size $N$ ($\Delta f_{\text{IEEE}}
     \gg U - L$), allowing an attacker to distinguish $D$ from $D'$ when the
     library calibrates noise only to $U - L$.
   - **Integer Overflow Wrap-Around and clamping/NaN bypasses (`Diffprivlib`,
     `Chorus`):** When computing bounded integer sums in fixed-width two's
     complement (`i32`/`i64`), if the unclipped or intermediate sum overflows and
     wraps from `INT64_MAX` to `INT64_MIN`, a single user's contribution changes
     the query output by $2^{64}$ instead of $U - L$, completely swamping the
     Laplace noise! Similarly, passing `-0.0`, `NaN`, or subnormal floats bypassed
     naive clamping comparisons (`if x < L { L } else if x > U { U } else { x }`
     returns `NaN` when `x` is `NaN` because both `<` and `>` evaluate to
     `false`!).

#### 3.5 Architectural Lessons for Anneal's Four `trusted/` Primitives in Networking, Authorization, and Privacy

- **Primitive 1 (`Language SemObs` & `Partial`):**
  - **P4 Header Validity & Side-Effect Ordering (`Gauntlet` / `Petr4`):** By
    modeling each P4 header in `State` as `Option HeaderBits` (where `none`
    represents `isValid() = false`) and defining `SemObs` as the deparser's
    serialized wire byte stream, any `p4c` optimization pass that drops a
    `.setValid()` call or reorders a side-effecting function inside a `MAT` key
    changes `SemObs` (or triggers `defined = False` on uninitialized header field
    reads) and is immediately rejected by `Compiles`.
  - **Machine-Checked IEEE-754 & Two's-Complement Semantics vs. Real-Arithmetic
    Fictions (`Mironov` / `Casacuberta`):** Just as Anneal's `BoundaryCanarySuite`
    (`anneal-structural-external-calls-and-tcb-mutation-testing-2026`) refuted
    the unmasked `Nat` ALU fiction in `X86Semantics.lean` and enforced exact
    64-bit modular arithmetic and `INT64_MIN / -1` trap checks, Casacuberta et
    al. (CCS 2022) and Mironov (CCS 2012) prove that verifying privacy or
    numerical compilers over idealized $\mathbb{R}$ or $\mathbb{Z}$ while
    executing `f64` or `i64` in production is fundamentally unsound. In Anneal,
    `L_Target` must model exact bit-level `BitVec 64` / IEEE-754 rounding (and
    reject `NaN` clamping bypasses via `defined = False`).
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, &
  `Abstracts`):**
  - **Certification of Residual Policy Compilation (`Cedar` / `Zanzibar` $\to$
    SQL):** When partially evaluating a `Cedar` policy into a residual SQL `WHERE`
    predicate, `obs_decodeOut` locks the boolean authorization decision (`Allow`
    vs. `Deny`): the residual SQL query neither leaks unauthorized rows nor
    silently over-filters authorized rows.
  - **Sensitivity Abstract Interpretation via `Abstracts` (`OpenDP`):** Computing
    a sound upper bound on floating-point or fixed-point query sensitivity (using
    exact integer/fixed-point accumulators or ULP-aware rounding bounds as
    prescribed by Casacuberta et al. CCS 2022) is a textbook instance of
    `Abstracts L_Sensitivity L_Query codec`: the abstract sensitivity domain must
    soundly over-approximate the concrete 2-safety distance across all neighboring
    pairs $(D_1, D_2)$.
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`):**
  - **Eliminating BGP Dispute Wheels and `RFC 3345` Route Oscillations via
    `EventualBehaviorOf`:** In BGP verification, a set of router configurations
    satisfies `Compiles L_Intent L_BGP` under `EventualBehaviorOf` **if and only
    if** for every link-failure scenario $F$ with $|F| \le k$ (`InhabitedPre`),
    asynchronous BGP route propagation **terminates in finitely many steps**
    (`.terminated fib`) and the converged `fib` satisfies the reachability/isolation
    intent. Any `RFC 3345` `MED` + Route-Reflection oscillation or Dispute Wheel
    diverges (`EventualOut.diverges`) and is rejected!
  - **Blocking the "Drop-All Firewall" and "Deny-All Authorizer" Goodhart Traps:**
    Requiring `ProductiveOn AuthorizedTrafficPre` paired with `obs_decodeOut`
    makes emitting a `DROP ALL` ACL or a `Deny`-everything policy compiler a hard
    kernel failure, while `InhabitedPre (fun req => eval policy req = .allow)`
    detects shadowed/dead `permit` rules in `Cedar` policies.
  - **`StepResult.externalCall` for DP Privacy-Budget & Discrete-Sampler Gating:**
    Before releasing a noisy query output or calling an external CSPRNG,
    `boundaryInv` verifies `remainingBudget >= queryEpsilon ∧
    noNaNOrOverflowInInput ∧ exactDiscreteSamplerUsed`.
- **Primitive 4 (`VerificationResult` / `ScopedVerificationResult` &
  `TrustPolicy`):**
  - In `Cedar`'s Verification-Guided Development (`OOPSLA 2024`), core theorems
    (`deny_trumps_allow`, `validate_sound`) are proved with zero waivers
    (`waived = []`), while any external IP/Decimal extension function or regex
    engine assumption is isolated as an explicit `TrustPolicy` entry.

### Historical Failure Analysis 4. Hermetic Build Systems, Tensor/ML Compilers, and Catastrophic Backtracking (`ReDoS`) Failures

`Basis: documentation + source + derived`

#### 4.1 Build System Dynamic Dependency Unsoundness, Non-Hermetic Cache Poisoning, and Cycle Panics (`Make`/`Ninja`, `Bazel`, `Salsa`, `Pluto`, and `Build Systems à la Carte`)

As Andrey Mokhov, Neil Mitchell, and Simon Peyton Jones formalized in *"Build
Systems à la Carte"* (ICFP 2018 / JFP 2020, `10.1145/3236774`) and Sebastian
Erdweg, Moritz Lichter, and Manuel Weiel proved in *"A Sound and Optimal
Incremental Build System with Dynamic Dependencies"* (`Pluto`, OOPSLA 2015,
`10.1145/2814270.2814316`), an incremental build system is **sound** ("from-scratch
consistent") if and only if building target $T$ in workspace state $W_i$ with a
warm cache produces the exact same output artifact as a clean build (`clean &&
build`) on $W_i$.

In production build and incremental computation engines (`Make`, `Ninja`,
`Bazel`, `Buck2`, `Salsa` in `rust-analyzer`, and `Lake` in Lean 4), four
recurring bug mechanisms break from-scratch consistency or crash the build:

1. **Post-Facto Depfile (`gcc -MMD` / `Ninja`) Header Insertion and Deletion
   Anomalies (`Pluto` OOPSLA 2015 & `Build Systems à la Carte`):**
   `Ninja` and `Make` discover C/C++ `#include` dependencies *only after*
   running `gcc`/`clang` with `-MMD -MF foo.o.d`. Because the `.d` depfile records
   only the files that were actually opened during the *previous* compilation:
   - **Shadowed include path insertion:** Suppose `foo.c` contains `#include
     "config.h"`, search path `-I dir1 -I dir2` is used, and initially only
     `dir2/config.h` exists. The recorded `.d` file lists `dir2/config.h`. If a
     developer later creates `dir1/config.h` (without touching `foo.c` or
     `dir2/config.h`), `Ninja` checks `stat()` only on `foo.c` and
     `dir2/config.h`, sees neither changed, and **skips recompiling `foo.o`**,
     even though a clean build would pick up `dir1/config.h`!
   - **Timestamp granularity (`mtime` slewing) and `stat` caching:** In classic
     `Make` (an *apriori* / timestamp-verifying rebuilder in Mokhov et al.'s
     taxonomy), sub-second edits within a single filesystem timestamp quantum or
     clock skew across NFS/containers cause newly generated headers to appear
     older than stale object files.
2. **Non-Hermetic Sandbox Escapes and Remote Build Execution (`RBE`) Cache
   Poisoning (`Bazel` / `Buck2` / `Lake`):**
   Content-addressed build systems (`Bazel`, `Buck2`) key their shared remote
   action cache (`ActionCache`) by the SHA-256 Merkle digest of the action's
   declared command line, environment variables, and input file tree. Whenever an
   action escapes its sandbox or reads an **undeclared input**—such as:
   - reading host environment variables (`PATH`, `LD_LIBRARY_PATH`, `LANG`,
     `PYTHONHOME`) when `--incompatible_strict_action_env` is not enforced,
   - reading untracked files inside a mounted directory or symlink tree (or in
     Lean 4 `Lake`, relocating prebuilt `.olean` archives across workspaces or
     changing toolchain/import graphs without invalidating cached module hashes,
     as documented in `anneal-v1-interactive-dependency-invalidation`),
   - or suffering a race condition between dynamic dependency discovery (`CppCompile`
     header scanning / `.d` pruning) and remote cache upload—
   the worker uploads an artifact built against unhashed local state into the
   shared remote CAS under a clean `ActionKey`, **poisoning the remote cache**
   for every developer and CI runner on the repository until the cache key is
   manually salted or flushed.
3. **Salsa / Red-Green Early-Cutoff Dynamic Dependency Cycle Panics
   (`rust-analyzer` / `salsa-rs`):**
   Fine-grained demand-driven incremental frameworks (`Salsa` in `rust-analyzer`,
   `Adapton`, `rustc` query engine) use the **red-green** algorithm: before
   re-executing query $Q(k)$ at revision $R_i$, the runtime walks $Q(k)$'s
   recorded dependencies from revision $R_{i-1}$ (`maybe_changed_after`). If
   every dependency's output equals its $R_{i-1}$ value (**Early Cutoff**), $Q(k)$
   is marked *green* without re-running. However, when a source edit in $R_i$
   changes control flow (for example, changing a Rust trait impl or macro expansion
   in `rust-analyzer`), checking whether an old dependency $D_{\text{old}}$ is
   green can dynamically re-enter $Q(k)$ along a newly formed path that would
   **not** even be reachable if $Q(k)$ were evaluated from scratch in $R_i$
   (a **phantom cycle** during `maybe_changed_after` validation), or can hit a
   genuine mutual-recursion cycle in user code (cyclic trait bounds / type
   aliases) that lacked a monotone fixed-point recovery handler
   (`cycle_recovery`), crashing the `rust-analyzer` LSP server with
   `panicked at 'dependency graph cycle when querying ...'`.

#### 4.2 Tensor and Polyhedral ML Compiler Silent Corruptions (`XLA GSPMD`, `Triton`, `Halide`, and `TVM` via `Tzer` and `NNSmith`)

Deep learning and image-processing compilers (`OpenXLA` / `GSPMD`, OpenAI
`Triton`, `Halide`, Apache `TVM`, `TensorRT`, `PyTorch Inductor`) apply
multi-stage schedule, layout, and distributed-sharding transformations to tensor
graphs. Automated compiler fuzzers—notably **`Tzer`** (Jiawei Liu et al., ISSTA
2022, `10.1145/3533767.3534388`, which found **49 new bugs in Apache `TVM`**)
and **`NNSmith`** (Jiawei Liu et al., ASPLOS 2023, `10.1145/3575693.3575707`,
which found **72 new bugs across `TVM`, `TensorRT`, `ONNXRuntime`, and
`PyTorch`**)—alongside production `OpenXLA` and `Triton` bug trackers document
three critical classes of silent numerical corruption:

1. **`XLA GSPMD` Sharding Propagation and Missing/Misplaced `AllReduce` Bugs:**
   In `OpenXLA`, `GSPMD` (Xu et al., `arXiv:2105.04663`) partitions a single-device
   `HLO`/`StableHLO` computation graph across an $N$-dimensional device mesh
   (`NamedSharding` / `HloSharding`: `Replicated`, `Tiled`, or `Partial`—meaning
   each device holds a partial sum that must be reduced via `AllReduce` or
   `ReduceScatter` before any non-linear operation). Historical bugs in `GSPMD`
   sharding propagation (which motivated Google's migration toward the MLIR-based
   `Shardy` dialect) occurred when:
   - A tensor in `Partial` sharding state (holding unreduced partial sums from a
     contracting `dot_general` matrix multiplication dimension) was passed through
     an elementwise operation, slice, pad, or custom call that assumed `Replicated`
     state without inserting an `AllReduce`, causing each TPU/GPU device to
     apply a non-linear activation ($\text{GeLU}(\sum_i x_i) \ne \sum_i
     \text{GeLU}(x_i)$) to its local partial sum and silently corrupting LLM
     training gradients!
   - Resharding across transposed or unevenly padded mesh dimensions (`PadToStatic`
     / dynamic slice with non-divisible shard sizes) failed to mask out-of-bounds
     halo padding elements (`0` vs. `-inf`) before a `ReduceMax` or `Softmax`
     collective, corrupting attention logits on boundary tokens.
2. **`Triton` GPU Compiler Shared-Memory (`smem`) Data Races, Swizzling Collisions,
   and `mbarrier` Synchronization Bugs:**
   The `Triton` compiler (`triton-lang/triton`) lowers blocked Python tile
   programs (`tl.load`, `tl.dot`, `tl.store`) into LLVM/NVPTX or AMDGCN assembly
   using multi-stage software pipelining (`num_stages`), shared-memory XOR
   swizzling (`TritonGPU` layout encodings: `#blocked`, `#mma`, `#shared`), and
   NVIDIA Hopper asynchronous Tensor Memory Accelerator (`TMA` / `cp.async` +
   `wgmma.mma_async` + `mbarrier`). Recurring miscompilations in `Triton`'s layout
   conversion and pipelining passes (`TritonGPUToLLVM`, `Pipeline`, `InsertBarriers`)
   include:
   - **Missing shared-memory read-after-write (`RAW`) and write-after-read (`WAR`)
     barriers across software-pipelined loop iterations:** When double- or
     triple-buffering `tl.dot` inside a `for` loop, if `InsertBarriers` /
     `MembarAnalysis` fails to insert `bar.sync` (or `wgmma.wait_group`) between
     the warp reading shared-memory buffer slot `stage % K` and the async copy
     overwriting that same slot in iteration `stage + K`, warps silently read
     half-overwritten tile data, producing non-deterministic `NaN`s or wrong
     matrix products that only manifest under high GPU occupancy.
   - **Broken layout-swizzle bijectivity and masked out-of-bounds vector loads:**
     When converting a tensor between `#blocked` and `#mma` layouts via shared
     memory, bugs in computing XOR swizzle parameters (`perPhase`, `maxPhase`,
     `order`) caused two threads in the same warp to write to the same shared-memory
     bank offset (overwriting elements), or caused vectorized `ld.global.v4`
     instructions to ignore a predicate mask `mask = offs < N` when the base
     pointer was not 16-byte aligned.
3. **`Halide` and `TVM` Polyhedral Bounds-Inference, Sliding-Window, and
   Loop-Vectorization Bugs (`Tzer` ISSTA 2022 & `NNSmith` ASPLOS 2023):**
   Both `Halide` and Apache `TVM` (`Tir` / `HalideIR`) separate pure functional
   tensor definitions from imperative scheduling directives (`split`, `reorder`,
   `compute_at`, `store_at`, `rfactor`, `vectorize`, `storage_align`). While
   Clément and Cohen (POPL 2022) and `HaliVer` (CAV 2023) worked to formalize
   Halide scheduling rewrites, `Tzer` and `NNSmith` demonstrated that unverified
   lowering passes in `TVM` and `Halide` routinely miscompile schedules:
   - **Interval-arithmetic bounds-inference underestimation on non-monotonic index
     expressions:** To allocate a scratchpad buffer for a producer stage `P`
     computed at consumer loop level `compute_at(C, xo)`, the compiler infers the
     min/max bounding box of `P` read by `C`. When `C` indexes `P` via modulo,
     floor-division, or negative-stride expressions (`P[x % 3 - y]`), naive
     interval evaluation under-approximated the required domain, allocating a
     buffer too small and reading out-of-bounds memory (`Tzer` `NarrowDataType` /
     `StorageRewrite` bugs).
   - **Unsound loop fusion and `LetStmt` / thread-extent hoisting (`Tzer` ISSTA
     2022):** Merging two loops or hoisting a conditional `Allocate` / `AttrStmt`
     (`threadIdx.x`) across a guard predicate caused threads outside the valid
     iteration domain to write garbage into output tensors or divide by zero in
     index expressions.

#### 4.3 Catastrophic Regular-Expression Backtracking (`ReDoS`) Global Outages (`Stack Overflow` July 20, 2016 and `Cloudflare` July 2, 2019)

Regular expressions are compiled into state machines executed on untrusted network
and user inputs in WAFs (Web Application Firewalls), API gateways, log parsers,
and authorization engines. Unlike Thompson's Non-deterministic Finite Automaton
(`NFA`) lockstep simulation (`RE2`, Rust `regex` crate) which processes an input
byte string of length $N$ in guaranteed $O(N \cdot |R|)$ time, backtracking
Spencer-style regex engines (`PCRE`, JavaScript, Python `re`, Java, `.NET`, Go
backtracking libs, and legacy Lua/PCRE WAF rules) explore ambiguous NFA
transitions via depth-first backtracking, taking **$O(2^N)$ exponential steps**
on inputs that nearly match an ambiguous quantified sub-pattern.

Two of the most famous global outages in modern internet history were caused by
a single catastrophic-backtracking regular expression:

1. **Stack Overflow Global Outage (July 20, 2016 — 34 Minutes Total Downtime):**
   - **Trigger:** A user posted a programming question containing a malformed line
     with approximately **20,000 consecutive space characters (`' '`)** at the end
     of a line without any non-whitespace character following them.
   - **Root Cause:** Stack Overflow's homepage/question list renderer invoked a
     built-in string-trimming routine implemented with the unanchored regular
     expression `^[\s\u200c]+|[\s\u200c]+$` to strip leading and trailing
     whitespace/zero-width non-joiners. Because the second alternation
     `[\s\u200c]+$` was unanchored at the start of the match, when the engine
     encountered 20,000 spaces followed by a non-matching character before the
     end of the string (`$`), it backtracked across every starting position and
     length combination ($O(N^2)$ steps—roughly $2 \times 10^8$ backtracking
     steps per render!).
   - **Blast Radius:** Every web server thread rendering the homepage or question
     feed was pinned at 100% CPU, exhausting the IIS thread pool across the entire
     fleet until engineers replaced the regex with a simple linear loop.
2. **Cloudflare Global Edge Outage (July 2, 2019 — 27 Minutes, 82% Global Traffic
   Drop):**
   - **Trigger:** A Cloudflare engineer deployed a routine Managed WAF rule update
     (`WAF-100178` / XSS detection) containing the sub-expression:
     `(?:(?:\"|'|\]|\}|\\|\d|(?:nan|infinity|true|false|null|undefined|symbol|math)|\`|\-|\+)+[)]*;?((?:\s|-|~|!|{}|\|\||\+)*.*(?:.*=.*)))`
   - **Root Cause:** Notice the nested adjacent wildcard quantifiers at the end:
     `.*(?:.*=.*)`. In a backtracking NFA/PCRE engine (or when PCRE/Lua fallback
     paths without DFA execution budgets are triggered), matching `.*.*=` against
     an HTTP request body containing $N$ characters before an `=` that later fails
     to match tries all $O(2^N)$ ways to split the string between the first `.*`
     and the second `.*`!
   - **Blast Radius:** Within seconds of global deployment, CPU utilization hit
     **100% across every CPU core** on Cloudflare's global edge proxy fleet in
     190+ cities, dropping 82% of global HTTP/HTTPS traffic (`HTTP 502 Bad
     Gateway`). Post-incident, Cloudflare migrated its entire WAF regex engine to
     the **Rust `regex` crate** (based on Thompson NFA / lazy DFA execution with
     guaranteed $O(N)$ linear-time complexity and zero backtracking).

#### 4.4 Architectural Lessons for Anneal's Four `trusted/` Primitives in Build Systems, Tensor Compilers, and Regex Engines

- **Primitive 1 (`Language SemObs` & `Partial`):**
  - **Out-of-bounds halo loads and GPU barrier races as `Partial.ub` (`Halide`,
    `TVM`, `Triton`):** In `L_Kernel`, any out-of-bounds tensor access, unaligned
    vectorized load, or shared-memory read without an intervening barrier after a
    cross-warp write steps to `.failed` (`defined = False`). Consequently,
    `Compiles L_Tensor L_Kernel` forces polyhedral schedule verifiers and
    `Triton` pipelining passes to prove bounds safety and barrier synchronization
    across all valid symbolic shapes `(B, S, H, D)`.
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, &
  `Abstracts`):**
  - **Distributed Tensor Sharding (`GSPMD` / `Shardy`) as a `PartialBehaviorCodec`:**
    When compiling a single-device tensor graph $L_{\text{Tensor}}$ to an $N$-device
    SPMD mesh $L_{\text{SPMD}}$, `encodeQuery` partitions input tensors into device
    shards and `decodeOut : L_SPMD.Out → Option L_Tensor.Out` reconstructs the
    global output tensor—returning **`none` whenever a tensor annotated as
    `Replicated` differs across devices or remains in an unreduced `Partial` sum
    state**! Thus, a `GSPMD` pass that forgets to insert an `AllReduce` before a
    non-linear activation fails `Compiles` (`decodeOut = none` violates
    `ProductiveOn` and `obs_decodeOut`).
  - **`Triton` Shared-Memory XOR Swizzling as a Verified `BehaviorCodec`:** A
    swizzled shared-memory layout is sound if and only if the coordinate transform
    `(row, col) ↦ (bank, offset)` is a **bijection** on the tile domain—which is
    literally the `decodeOut_encodeOut` and `encodeOut_of_decodeOut` round-trip
    law of `BehaviorCodec`!
  - **Incremental Build Soundness via Clean-vs-Warm `Compiles`:** Modeling clean
    topological evaluation as $L_{\text{CleanBuild}}$ and stateful incremental
    evaluation (`Skyframe`, `Buck2 DICE`, `Salsa`, `Lake`) as $L_{\text{IncBuild}}$
    with `SemObs := Sha256Digest` makes from-scratch consistency across any edit
    sequence $[W_0, \dots, W_m]$ a direct `Compiles L_CleanBuild L_IncBuild`
    theorem.
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`):**
  - **Preventing `Bazel` / `Ninja` Cache Poisoning via `StepResult.externalCall`:**
    When a build engine spawns a compiler action or reads a file (`externalCall`),
    `boundaryInv` verifies `accessedPath ∈ declaredActionKeyInputs` (and for
    `Ninja`/`Pluto` dynamic dependencies, verifies that *both* positive file reads
    and negative directory-lookup absences along `-I` search paths are recorded in
    the dependency trace). Any undeclared host read evaluates `boundaryInv = false`
    and aborts before polluting the remote cache!
  - **Preventing `Salsa` Cycle Panics and `Cloudflare`/`Stack Overflow` `ReDoS`
    Outages via `ProductiveOn`, `EventualBehaviorOf`, and `CertifiedOptimizationPass`:**
    - In `Salsa` / `DICE`, `EventualBehaviorOf` refutes phantom validation cycles
      by requiring `maybe_changed_after` to terminate on all acyclic query graphs
      (`ProductiveOn AcyclicGraphPre`) and requiring cyclic queries with
      monotone fixed-point handlers to converge in finitely many steps.
    - In regex and parser engines, using Anneal's step-dilated refinement
      `π_dilated k` (`anneal-polar-ctfe-admission-and-semantic-polarity-2026`,
      where $k = O(|R|)$ per input byte) proves **linear-time $O(N)$ execution
      progress** in `BehaviorOf`—mathematically rejecting exponential $O(2^N)$
      backtracking engines (`Cloudflare` `.*.*=.*` and `Stack Overflow`
      `[\s\u200c]+$`) at compile time!
- **Primitive 4 (`VerificationResult` / `ScopedVerificationResult` &
  `TrustPolicy`):**
  - In ML compilers (`XLA` / `TVM` / `Triton`), floating-point parallel reduction
    (`AllReduce` tree summation) is non-associative in IEEE-754. Rather than
    weakening the core `BehaviorCodec` for all passes, `ScopedVerificationResult`
    isolates `.fpAssocInAllReduce` as an explicit, per-pass `TrustPolicy` waiver
    while enforcing strict bitwise identity (`waived = []`) on layout
    transpositions, sharding gathers, and integer/quantized kernels.

#### 4.5 Cross-Domain Synthesis Matrix: Mapping Historical Failure Classes to Anneal's Trusted Primitives

| Historical Failure Case & Primary Source | Root Technical Failure Mechanism | Anneal `trusted/lean/` Primitive That Blocks It | Exact Mechanism in Anneal's TCB |
| :--- | :--- | :--- | :--- |
| **`SQLancer` `TLP`/`NoREC`** (OOPSLA/FSE 2020): >350 wrong-result bugs in `Postgres`, `MySQL`, `CockroachDB`, `SQLite`, `TiDB` | Conflating Kleene 3VL `UNKNOWN` (`NULL`) with `FALSE` in outer-join pushdowns and `NOT IN` / index rules | `Language SemObs` & `BehaviorCodec.obs_decodeOut` | `L_Rel` evaluates predicates in 3VL (`KleeneBool`); `obs_decodeOut` forces target plan to match exact `NULL`-partitioned multiset on all inputs |
| **Kim (1982) `COUNT` Bug & Bag-vs-Set Rewrites** (`Cosette` 2017, `UDP` 2018, `WeTune` SIGMOD 2022) | Inner-join decorrelation drops empty groups (`COUNT = 0`); semi-join rewrite inflates duplicate row counts | `BehaviorCodec` (`SemObs := Multiset Tuple`) | `obs_decodeOut` preserves exact tuple multiplicities ($\text{Tuple} \to \mathbb{N}$) and empty-group rows |
| **SQL Predicate-Pushdown Division-by-Zero Traps** (`Postgres`, `Calcite`, `Spark SQL`) | Pushing `100 / x > 5` below `WHERE x <> 0` introduces runtime trap on dead rows | `Partial` (`defined` vs. `Partial.ub`) & `Compiles` | `Compiles` ($t \le \pi(s)$) forbids turning a `defined = True` query into `Partial.ub` or `.aborted .divByZero` |
| **`Flink` / `Materialize` IVM Retraction & Watermark Bugs** (`DBSP` VLDB 2023, `FLINK-9528`) | Dropping `-U` retractions in Top-$N$/joins; advancing watermarks early and GC-dropping valid window state | `PartialBehaviorCodec` & `ProductiveOn` + `EventualBehaviorOf` | Stream codec returns `decodeOut = none` on unbalanced changelog retractions; `ProductiveOn` blocks holding watermarks at $-\infty$ |
| **`FSCQ` (SOSP 2015) & `Yggdrasil` (OSDI 2016)** FUSE/C shim and disk barrier gaps | Unverified Haskell/Cython FUSE glue bugs; missing `fsync`/`FUA` parent-directory or WAL barriers before data writes | Proof-Gated Compilation (`Compiles`) & `StepResult.externalCall` | Single-source `.olean` codegen eliminates dual-emitter shims; `externalCall` checks `boundaryInv : flushedLSN >= pageLSN` at every disk write |
| **`RocksDB` `DeleteRange` Compaction Bugs** (`#4747`, `#4760`, `#5616`, `#7703`) | Dropping or mis-clipping a range tombstone `[a, z) @ seq` above an active snapshot or deeper SSTable level | `StepResult.externalCall` & `PartialBehaviorCodec` | Compaction emit checks `boundaryInv : seq < earliest_snapshot ∧ disjointFromDeeperLevels`; `obs_decodeOut` rejects resurrected keys |
| **`Raft` Figure 8 & Single-Server Membership Bug** (Ongaro 2014/2015) & **`Jepsen`/`Elle`** (`CockroachDB`, `TiKV`, `MongoDB`) | Committing prior-term entries or pipelining membership changes creates disjoint quorums; stale reads cause `G1c`/`G-single` cycles | `Abstracts` + `Compiles` ($L_{\text{Serial}} \to L_{\text{TLA}} \to L_{\text{Dist}}$) & `ProductiveOn` | Refinement to atomic serial histories rules out split-brains and `Elle` cycles; `ProductiveOn` blocks "abort 100% of transactions" |
| **`Sieve` (OSDI 2022, 28 bugs) & `Anvil` (OSDI 2024)** Kubernetes Operator bugs | Stale informer-cache `TOCTOU` overwrites; orphan cloud resource leaks; infinite reconciliation livelocks | `StepResult.externalCall` & `EventualBehaviorOf` | `externalCall` models demonic lagging informer caches and requires `resourceVersion` + finalizer guards; `EventualBehaviorOf` enforces all-prefix safety + ESR convergence |
| **`Gauntlet` (OSDI 2020, 96 bugs) & `Petr4` (POPL 2021)** in `p4c`, `BMv2`, and Barefoot Tofino | Side-effect reordering in `MAT` keys; dropping `.setValid()` header validity updates; undefined parser fallthrough | `Language SemObs` & `Partial` (`defined`) | Reading an invalid header (`valid = false`) is `Partial.ub`; side-effect hoisting in `MAT` keys alters `SemObs` egress packet bytes |
| **BGP Persistent Route Oscillation** (`Griffin-Shepherd-Wilf` 1999 Dispute Wheels & `RFC 3345` `MED` + Route Reflection) | Non-transitive `MED` + route reflection hides alternate paths, causing infinite `UPDATE`/`WITHDRAW` oscillation | `EventualBehaviorOf` & `ProductiveOn` | `EventualBehaviorOf` requires finite-step BGP convergence (`.terminated fib`) on all $k$-link failures, rejecting `.diverges` |
| **AWS `Cedar` Pre-Release Bugs** (OOPSLA 2024: 4 validator bugs in Lean 4 proof + 21 DRT bugs) | Unsound record-attribute capability LUB in validator (`has` across `||`/`!`); Rust-vs-Lean parser/overflow divergences | `Abstracts` (Validator Soundness) & `Compiles` (Lean-to-Rust Equivalence) | `Abstracts` forces validator acceptance to imply `defined = True` (zero runtime attribute errors); `obs_decodeOut` locks `Allow ↔ Allow` |
| **`Mironov` (CCS 2012) LSB & `Casacuberta et al.` (CCS 2022)** DP Sensitivity Attacks on `OpenDP`, `Diffprivlib`, `Chorus` | Sparse `f64` `-b ln(U)` LSB leaks; `f64` sum non-associativity, `i64` overflow wrap, and `NaN` clamping bypasses | Exact Bit-Level `Language` (`BoundaryCanarySuite`), `Abstracts`, & `StepResult.externalCall` | Rejects idealized $\mathbb{R}$ fictions; `Abstracts` bounds exact bit-level sensitivity; `externalCall` checks budget, `NaN`-freedom, and discrete sampler |
| **`Pluto` (OOPSLA 2015), `Ninja` Depfiles, `Bazel` RBE Cache Poisoning, & `Salsa` Cycle Panics** | Missing negative directory-lookup dependencies; mounting unhashed host files in sandbox; `maybe_changed_after` phantom cycles | `StepResult.externalCall`, `Compiles` ($L_{\text{Clean}} \to L_{\text{Inc}}$), & `CertifiedOptimizationPass` | `externalCall` enforces `sandboxMounts ⊆ hashedInputs`; `Compiles` proves clean-build equivalence; `CertifiedOptimizationPass` enforces Early Cutoff |
| **`XLA GSPMD` Sharding, `Triton` GPU Barriers, & `Halide`/`TVM` Schedule Bugs** (`Tzer` ISSTA 2022, `NNSmith` ASPLOS 2023) | Omitted `AllReduce` on `Partial` shards; missing `bar.sync`/`mbarrier` across `smem` stages; under-approximated halo bounds | `PartialBehaviorCodec` (Sharding/Swizzle Bijection) & `Partial` (`defined`) | Sharding `decodeOut` returns `none` if replicated shards diverge or remain `Partial`; `defined` rejects out-of-bounds halo loads and barrier races |
| **`Stack Overflow` (2016) & `Cloudflare` (2019) `ReDoS` Outages** | Backtracking NFA regexes (`[\s\u200c]+$`, `.*.*=.*`) taking $O(N^2)$ to $O(2^N)$ steps on adversarial inputs | `BehaviorOf` Step-Dilated Refinement (`π_dilated k`) & `ProductiveOn` | Bounding target step budget by $k \cdot N$ per input of length $N$ in `BehaviorOf` proves guaranteed linear-time $O(N)$ execution |

## Boundaries

### Part I — Real-World Tool Survey Boundaries

The following scope boundaries and open questions govern the findings in this
report:

- **Mechanized domain instantiations (`not examined`):** While the core
  structural primitives (`Partial`, `PartialBehaviorCodec`, `Compiles`,
  `Abstracts`, `EventualBehaviorOf`, `CertifiedOptimizationPass`,
  `StepResult.externalCall`, and `ScopedVerificationResult`) are fully
  mechanized in Lean 4.34.1 across `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` and
  `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`, full domain object-language semantics for the
  86 external tools (such as a complete SQL-99 AST or `P4_16` parser inside
  Anneal's repository) were **not examined** as executable Lean 4 artifacts in
  this package.
- **Probabilistic and quantitative metrics in `Trusted/Refinement.lean`
  (`known not to apply` without `theory/` encoding):** `Trusted/Refinement.lean`
  defines `Behavior` over boolean-valued propositions (`Out → Prop`) and strict
  equality of observations (`L₂.obs o₂ = L₁.obs o₁`). Direct quantitative
  coupling metrics (such as $(\epsilon, \delta)$-differential privacy in
  `OpenDP`/`CertiPriv` or ULP floating-point error bounds in `XLA`/`Mirage`) are
  **known not to apply** as primitive fields of `Trusted.Language` unless
  encoded via a 2-safety product language $L^2$ carrying deterministic coupling
  or interval witnesses in `theory/`.
- **Infinite-trace fairness and liveness beyond finite horizons (`unsupported`
  in finite-prefix `ReachesPrefix` alone):** Both `BehaviorOf`
  (`Trusted/StepResult.lean:176`) and `EventualBehaviorOf`
  (`support/BehaviorCodecExpressiveness.lean`) intentionally avoid coinductive
  infinite traces and `Classical.choice` by quantifying over finite step budgets
  `steps : Nat`. Unbounded weak/strong fairness properties ($\square \lozenge A
  \implies \square \lozenge B$) over genuinely non-terminating executions that
  cannot be reduced to finite horizon or ranking-function bounds (`Padon et al.`
  liveness-to-safety or bounded watermark horizons $W_k$) are **unsupported** by
  `ReachesPrefix` without a ranking-function or horizon parameterization in
  `Query`.
- **Proprietary tool internals (`unknown`):** For closed-source industrial
  systems examined via published papers (`SlabCity`, `Zelkova`, `Tiros`,
  `Zanzibar`, `XLA PartIR`), internal implementation details beyond their
  published specifications and open-source counterparts (`Shardy`, `SpiceDB`,
  `cedar-spec`) remain **unknown**.

### Part II — Historical Verification Failure Postmortem Boundaries

To prevent future agents from over-generalizing the historical findings or
architectural mappings in this report, the following boundaries apply:

- **Not examined — Mechanized domain instantiations in `theory/`:** While
  Anneal's four core `trusted/lean/` primitives (`Language`/`Partial`,
  `BehaviorCodec`/`PartialBehaviorCodec`, `StepResult.externalCall`/
  `EventualBehaviorOf`/`ProductiveOn`, and `VerificationResult`/
  `ScopedVerificationResult`) are mechanized and kernel-verified across
  `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`,
  `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457`, and the five
  companion 2026 reference reports, full production front ends for SQL/DBSP,
  P4-16, Kubernetes controllers, or `StableHLO`/`Triton` have not yet been
  implemented inside `theory/`.
- **Known not to apply — Unmodified deterministic `Partial (Out → Prop)` for
  quantitative probabilistic couplings without relational lifting:** Standard
  single-trace `Partial (Out → Prop)` directly captures safety, totality,
  multiplicity, linearizability, and deterministic sensitivity bounds, but
  expressing approximate $(\epsilon, \delta)$-differential privacy
  ($\Pr[\mathcal{M}(D_1) \in S] \le e^\epsilon \Pr[\mathcal{M}(D_2) \in S] +
  \delta$) or quantitative floating-point ULP error envelopes requires either:
  (a) instantiating `Language` over a 2-safety relational product ($L^2$, where
  `Query := D₁ × D₂` and `Out` carries an approximate relational Hoare logic
  coupling witness), or (b) parameterizing `SemObs` with a quantitative
  approximation relation in `theory/`.
- **Unsupported — Proving true asynchronous liveness (`◇P`) without fairness or
  synchrony hypotheses:** Under completely unconstrained demonic environment
  nondeterminism (where an adversarial network drops 100% of packets forever or
  an OS scheduler never schedules a thread), no distributed consensus protocol
  (`FLP` impossibility, Fischer-Lynch-Paterson 1985) or Kubernetes controller
  can guarantee finite-step termination. In Anneal, `EventualBehaviorOf` and
  `ProductiveOn pre` verify convergence relative to an explicit precondition
  `pre : Query → Prop` that bounds adversarial faults prior to Global
  Stabilization Time (`GST`) or bounds link failures ($|F| \le k$).

## Evidence

### Part I — Real-World Tool Survey Evidence

1. **Anneal Trusted Core and MIR-to-x86-64 Repositories (`source`):**
   - `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` (`trusted-refinement-core`):
     - `trusted/lean/Trusted/Refinement.lean:208-471`: Definitions of `Preorder`,
       `Partial`, `Partial.pure`, `Partial.ub`, `instPreorderPartial`,
       `Monotone`, `Behavior`, `Language`, `Language.SpecOn`,
       `Language.WellFormedOn`, `Compiles`, `Abstracts`, `Compiler`,
       `Compiler.SoundOn`, `Compiler.Verified`, `TrustedAssumption`,
       `TrustPolicy`, and `VerificationResultOn`.
     - `trusted/lean/Trusted/StepResult.lean:58-198`: Definitions of
       `TerminationKind`, `StepResult`, `PrefixOutcome`, `PrefixOutcome.isSafe`,
       `ExecQuery`, `ExecOut`, `SmallStepMachine`, `ReachesPrefix`,
       `BehaviorOf`, and `SmallStepMachine.toLanguage`.
     - `theory/Anneal/Refinement.lean:50-286`: Proofs of `ub_top`, `ub_le_iff`,
       `le_specOn_iff`, `le_wellFormedOn_iff`, `pass_trans`, `Compiles.comp`,
       `Abstracts.comp`, `Compiler.SoundOn.verify`, and `verify_through_passes`.
     - `theory/Anneal/StepResult.lean:38-179`: Definitions of `TotalStep` and
       `InhabitedDemonic`, and proofs of `exists_reaches_prefix`,
       `non_vacuity_at_every_depth`, and `behaviorOf_le_specOn`.
   - `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457` (`x86-backend-pipeline`):
     - `trusted/lean/Trusted/X86Semantics.lean`,
       `theory/Anneal/Compiler/NaiveCodegen.lean`, and
       `theory/Anneal/Compiler/Peephole.lean`.
2. **Anneal Trusted-Boundary Hardening Corpus (`source` + `execution`):**
   - `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` (`reference`):
     - `support/BehaviorCodecExpressiveness.lean`
       and `support/BehaviorCodecExpressiveness.lean` (`PartialBehaviorCodec`,
       `EventualBehaviorOf`, `eventual_wellFormed_iff_prefix_wellFormed`,
       `CertifiedOptimizationPass`).
     - `support/StructuralExternalCallAndCanaries.lean`
       and `support/StructuralExternalCallAndCanaries.lean:148-236`
       (`StepResult.externalCall`, `CallerFramePreserved`,
       `open_world_callback_composition_sound`).
     - `support/ProofGatedCompilationAndTrustPolicy.lean`
       and `support/ProofGatedCompilationAndTrustPolicy.lean` (`TCBModel`,
       `BoundaryCodec`, `ScopedVerificationResult`,
       `proof_gated_compilation_eliminates_ir_from_tcb`).
   - Existing `reference` corpus report on incremental computation:
     - `Hammer et al. (OOPSLA 2015) nominal memoization tables`.
3. **Primary Literature and Open-Source Coordinates Across All 10 Domains
   (`documentation` + `normative` + `source`, observed `2026-10-31`):**
   - **Domain 1:** `uwdb/Cosette` & `uwdb/HoTTSQL` (DOI `10.1145/3035918.3056447`,
     `10.1145/3009837.3009848`); `UDP` (DOI `10.14778/3236187.3236200`);
     `EQUITAS` (DOI `10.1145/3299869.3319869`); `SPES` (DOI
     `10.1109/ICDE53745.2022.00201`); `Qex` (DOI `10.1007/978-3-642-17511-4_24`);
     `we-tune/WeTune` (DOI `10.1145/3514221.3526125`); `SlabCity` (DOI
     `10.1145/3589297`); `datacert/datacert`; `querycert/qcert` (DOI
     `10.1145/3035918.3056101`); `feldera/feldera` (`DBSP`, DOI
     `10.14778/3587136.3587140`); `MaterializeInc/materialize`;
     `cockroachdb/cockroach` (`pkg/sql/opt/optgen`); `apache/calcite`;
     `risinglightdb/risinglight`; `souffle-lang/souffle`.
   - **Domain 2:** `mit-pdos/fscq` (DOI `10.1145/2815400.2815402`,
     `10.1145/3132747.3132776`); `mit-pdos/perennial` & `mit-pdos/daisy-nfsd`
     (DOI `10.1145/3341301.3359632`, OSDI 2022); `uwplse/yggdrasil` (OSDI 2016);
     `secure-foundations/veribetrkv-osdi2020` (OSDI 2020); `NICTA/cogent`
     (`BilbyFS`, DOI `10.1145/2872362.2872404`); `Flashix` (IEEE TSE 2020);
     `mars-research/atmosphere` (DOI `10.1145/3600006.3613148`);
     `vmware/splinterdb` (USENIX ATC 2020); `facebook/rocksdb`.
   - **Domain 3:** `uwplse/verdi` & `uwplse/verdi-raft` (DOI
     `10.1145/2737924.2737958`, `10.1145/2854065.2854081`);
     `microsoft/Ironclad` (`IronFleet`, DOI `10.1145/2815400.2815428`);
     `kenmcmil/ivy` (DOI `10.1145/2908080.2908118`); `logsem/aneris` (DOI
     `10.1007/978-3-030-44914-8_14`); `mit-pdos/chapar` (DOI
     `10.1145/2837614.2837622`); `kevin-dp/VeriFx`; `Isabelle AFP: CRDT` (DOI
     `10.1145/3133933`); `tlaplus/tlapm` (`TLAPS`, DOI
     `10.1007/978-3-642-32759-9_14`); `apple/foundationdb` (DOI
     `10.1145/3448016.3457559`); `jepsen-io/jepsen` & `jepsen-io/elle` (DOI
     `10.14778/3430915.3430918`).
   - **Domain 4:** `batfish/batfish` & `Minesweeper` (DOI
     `10.1145/3098822.3098828`); `uwplse/bagpipe` (DOI `10.1145/2983990.2984012`);
     `frenetic-lang/netkat` & `KATch` (DOI `10.1145/2535838.2535862`,
     `10.1145/3656436`); `p4v` (DOI `10.1145/3230543.3230582`); `Vera` (DOI
     `10.1145/3230543.3230548`); `cornell-netlab/petr4` (DOI `10.1145/3434301`);
     `verified-network-toolchain/poulet4`; `p4gauntlet/gauntlet` (OSDI 2020);
     `XJTU-NetVerify/apkeep` (NSDI 2020), `VeriFlow` (NSDI 2013), `HSA` (NSDI
     2012); `NetworkVerification/nv` (PLDI 2020), `ShapeShifter` (PLDI 2019),
     and `Timepiece` (PLDI 2023).
   - **Domain 5:** `anvil-verifier/anvil` (OSDI 2024); `sieve-project/sieve`
     (OSDI 2022); `K8s-TLA+`; `Terraform Sentinel`, `open-policy-agent/conftest`,
     `bridgecrewio/checkov`; `Tiros` (DOI `10.1007/978-3-030-25543-5_14`);
     `plasma-umass/rehearsal` (DOI `10.1145/2908080.2908122`).
   - **Domain 6:** `cedar-policy/cedar` & `cedar-policy/cedar-spec` (DOI
     `10.1145/3649835`); `Zelkova` (DOI `10.23919/FMCAD.2018.8603013`);
     `Margrave` (DOI `10.1145/1062455.1062502`); `Zanzibar` (USENIX ATC 2019),
     `authzed/spicedb`, `openfga/openfga`; `open-policy-agent/opa`;
     `opendp/opendp`; `uvm-plaid/chorus`; `Fuzz` (ICFP 2010), `DFuzz` (POPL
     2013), `LightDP` (POPL 2017); `CertiPriv` & `EasyCrypt/easycrypt` (DOI
     `10.1145/2103656.2103670`).
   - **Domain 7:** `snowleopard/build` (`Build Systems à la Carte`, DOI
     `10.1145/3236774`, `10.1017/S0956796820000088`); `pluto-build/pluto` (DOI
     `10.1145/2814270.2814277`); `salsa-rs/salsa`; `facebook/buck2` (`DICE`);
     `adapton/adapton.rust` (DOI `10.1145/2594291.2594324`);
     `bazelbuild/bazel` (`Skyframe`) & `bazelbuild/remote-apis` (`REAPI`);
     `pubgrub-rs/pubgrub`.
   - **Domain 8:** `llvm/mlir-tv` & `AliveToolkit/alive2` (DOI
     `10.1145/3453483.3454030`); `halide/Halide` & `verified-halide` (DOI
     `10.1145/3563321`); `exo-lang/exo` (DOI `10.1145/3519939.3523446`);
     `XLA GSPMD` (arXiv `2105.04663`), `PartIR`, & `openxla/shardy`;
     `llvm/llvm-project/polly` & `isl`; `imperial/gpuverify` (DOI
     `10.1145/2384616.2384625`) & `umb-svl/faial` (DOI
     `10.1007/978-3-030-81685-8_19`); `uwplse/tensat` (MLSys 2021) &
     `mirage-project/mirage` (OSDI 2025, arXiv `2405.05751`).
   - **Domain 9:** `TimelyDataflow/timely-dataflow` (DOI
     `10.1145/2517349.2522738`); `StreamBox` (USENIX ATC 2017); `Flink ABS`
     (arXiv `1506.08603`); `Coqlex/coqlex` (arXiv `2301.10479`) & `VeriLex`;
     `Isabelle AFP: Posix-Lexing` (DOI `10.1007/978-3-319-43144-4_5`) &
     `pandaman64/lean-regex`; `slasser/CoStar` (DOI `10.1145/3453483.3454053`)
     & `TRX` (DOI `10.2168/LMCS-7(2:18)2011`).
   - **Domain 10:** `project-everest/everparse` (USENIX Security 2019);
     `Narcissus` (DOI `10.1145/3290389`); `secure-foundations/vest` (USENIX
     Security 2025) & `google/zerocopy`; `inkandswitch/cambria-project` &
     `boomerang-lang/boomerang` (DOI `10.1145/1328438.1328487`); `bufbuild/buf`;
     `temporalio/temporal` & `restatedev/restate`; `p-org/P` (DOI
     `10.1145/2491956.2462184`).

### Part II — Historical Verification Failure Postmortem Evidence

All technical claims in this report are grounded in the following primary
sources and repository revisions (observed and cross-checked on `2026-10-31`):

1. **Anneal Trusted Core and Companion Mechanizations (`joshlf/anneal`):**
   - `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`:
     `trusted/lean/Trusted/Refinement.lean` (lines 1–466: `Partial`, `Language`,
     `BehaviorCodec`, `Compiles`, `Abstracts`, `Compiler.SoundOn`,
     `Compiler.Verified`, `TrustedAssumption`, `TrustPolicy`,
     `VerificationResultOn`) and `trusted/lean/Trusted/StepResult.lean` (lines
     1–220: `StepResult`, `PrefixOutcome`, `ExecQuery`, `ExecOut`,
     `SmallStepMachine`, `ReachesPrefix`, `BehaviorOf`).
   - `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457`:
     `trusted/lean/Trusted/X86Semantics.lean` and
     `theory/Anneal/Compiler/Peephole.lean`.
   - Companion corpus packages on `refs/heads/reference`
     (`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`):
     - `support/BehaviorCodecExpressiveness.lean`
       (`PartialBehaviorCodec`, `EventualBehaviorOf`, `ProductiveOn`,
       `InhabitedPre`, `CertifiedOptimizationPass`),
     - `support/BehaviorCodecExpressiveness.lean`
       (`π_dilated k` step-dilated refinement),
     - `support/StructuralExternalCallAndCanaries.lean`
       (`StepResult.externalCall` and `BoundaryCanarySuite`), and
     - `support/ProofGatedCompilationAndTrustPolicy.lean`
       (`TCBModel`, proof-gated compilation cut elimination, and
       `ScopedVerificationResult`).

2. **Database Query Optimizers, SQL Equivalence, and Incremental View
   Maintenance:**
   - Manuel Rigger and Zhendong Su, *"Detecting Optimization Bugs in Database
     Engines via Non-Optimizing Reference Engine Construction"* (`NoREC`),
     ESEC/FSE 2020, DOI `10.1145/3368089.3409710`.
   - Manuel Rigger and Zhendong Su, *"Finding Bugs in Database Systems via
     Query Partitioning"* (`TLP`), OOPSLA 2020, PACMPL 4(OOPSLA):211, DOI
     `10.1145/3428279`.
   - Manuel Rigger and Zhendong Su, *"Testing Database Engines via Pivoted Query
     Synthesis"* (`PQS`), USENIX OSDI 2020, pp. 667–682.
   - Shumo Chu, Chenglong Wang, Konstantin Weitz, and Alvin Cheung, *"Cosette:
     An Automated Prover for SQL"*, CIDR 2017; and Shumo Chu, Konstantin Weitz,
     Alvin Cheung, and Dan Suciu, *"HoTTSQL: Proving Query Rewrites with
     Univalent SQL Semantics"*, PLDI 2017, DOI `10.1145/3062341.3062348`.
   - Shumo Chu, Brendan Murphy, Jared Roesch, Alvin Cheung, and Dan Suciu,
     *"Axiomatic Foundations and Algorithms for Deciding Semantic Equivalences
     of SQL Queries"* (`UDP`), PVLDB 11(11):1482–1495, 2018, DOI
     `10.14778/3192965.3192971`.
   - Zhaoguo Wang, Zhou Zhou, Yiren Jiang, Haoran Ding, Gansen Hu, Ding Ding,
     Chuzhe Tang, Haibo Chen, and Jinyang Li, *"WeTune: Automatic Discovery and
     Verification of Query Rewrite Rules"*, SIGMOD 2022, pp. 94–107, DOI
     `10.1145/3514221.3526125`.
   - Thomas Neumann and Alfons Kemper, *"Unnesting Arbitrary Queries"*, BTW
     2015, LNI P-241, pp. 383–402.
   - Mihai Budiu, Tej Chajed, Frank McSherry, Leonid Ryzhyk, and Val Tannen,
     *"DBSP: Automatic Incremental View Maintenance for Rich Query Languages"*,
     PVLDB 16(7):1601–1614, 2023 (VLDB 2023 Best Paper), DOI
     `10.14778/3587136.3587137`.

3. **Storage Engines, Distributed Consensus, and Kubernetes Controllers:**
   - Haogang Chen, Daniel Ziegler, Tej Chajed, Adam Chlipala, M. Frans
     Kaashoek, and Nickolai Zeldovich, *"Using Crash Hoare Logic for Certifying
     the FSCQ File System"*, SOSP 2015, pp. 18–37, DOI
     `10.1145/2815400.2815402`.
   - Helgi Sigurbjarnarson, James Bornholt, Emina Torlak, and Xi Wang,
     *"Push-Button Verification of File Systems via Crash Refinement"*
     (`Yggdrasil`), USENIX OSDI 2016, pp. 1–16.
   - Tej Chajed, Joseph Tassarotti, M. Frans Kaashoek, and Nickolai Zeldovich,
     *"Verifying Concurrent, Crash-Safe Systems with Perennial"*, SOSP 2019,
     pp. 243–258, DOI `10.1145/3341301.3359632`.
   - Pandian Raju, Rohan Kadekodi, Vijay Chidambaram, and Ittai Abraham,
     *"PebblesDB: Building Key-Value Stores using Fragmented Log-Structured
     Merge Trees"*, SOSP 2017, DOI `10.1145/3132747.3132765`.
   - `facebook/rocksdb` issue tracker and commits for `DeleteRange` compaction
     and snapshot bugs (`#4747`, `#4760`, `#5616`, `#7703`, `#10250`) and the
     official RocksDB *"DeleteRange: A New Native RocksDB Operation"*
     engineering retrospective.
   - Diego Ongaro and John Ousterhout, *"In Search of an Understandable
     Consensus Algorithm"*, USENIX ATC 2014 (Figure 8 commitment invariant); and
     Diego Ongaro, *"Consensus: Bridging Theory and Practice"*, Stanford PhD
     Dissertation, 2014 (plus 2015 single-server membership change erratum).
   - Kyle Kingsbury and Peter Alvaro, *"Elle: Inferring Isolation Anomalies from
     Experimental Observations"*, PVLDB 14(3):268–280, 2020, DOI
     `10.14778/3457390.3457396`.
   - Xudong Sun, Wenqing Luo, Jiawei Tyler Gu, Aishwarya Ganesan, Ramnatthan
     Alagappan, Michael Gasch, Lalith Suresh, and Tianyin Xu, *"Automatic
     Reliability Testing for Cluster Management Controllers"* (`Sieve`), USENIX
     OSDI 2022, pp. 143–159.
   - Xudong Sun, Wenjie Ma, Jiawei Tyler Gu, Zicheng Ma, et al. (UIUC,
     UW-Madison, VMware Research), *"Anvil: Verifying Liveness of Cluster
     Management Controllers"*, USENIX OSDI 2024, pp. 649–666.

4. **Networking, Cloud IAM Authorization, and Differential Privacy:**
   - Fabian Ruffy, Tao Wang, and Anirudh Sivaraman, *"Gauntlet: Finding Bugs in
     Compilers for Programmable Packet Processing"*, USENIX OSDI 2020, pp.
     683–699, `arXiv:2006.01074`.
   - Ryan Doenges, Mina Tahmasbi Arashloo, Santiago Bautista, Alexander Chang,
     Newton Ni, Samwise Parkinson, Rudy Peterson, Alaia Solko-Breslin, Amanda
     Xu, and Nate Foster, *"Petr4: Formal Foundations for P4 Data Planes"*,
     PACMPL 5(POPL):1–32, 2021, DOI `10.1145/3434304`.
   - Timothy G. Griffin, F. Bruce Shepherd, and Gordon Wilfong, *"The Stable
     Paths Problem and Interdomain Routing"*, IEEE/ACM Transactions on
     Networking 10(2):232–243, 2002 (preliminary versions in ICNP 1999 and
     SIGCOMM 1999).
   - Danny McPherson, Vijay Gill, Daniel Walton, and Alvaro Retana, *"Border
     Gateway Protocol (BGP) Persistent Route Oscillation Condition"*, IETF
     `RFC 3345`, August 2002.
   - Joseph W. Cutler et al., *"Cedar: A New Language for Expressive, Fast,
     Safe, and Analyzable Authorization"*, PACMPL 8(OOPSLA1):Article 118, 2024,
     DOI `10.1145/3649835`, `arXiv:2403.04651`.
   - Ilya Mironov, *"On Significance of the Least Significant Bits for
     Differential Privacy"*, ACM CCS 2012, pp. 650–661, DOI
     `10.1145/2382196.2382264`.
   - Sílvia Casacuberta, Michael Shoemate, Salil Vadhan, and Connor Wagaman,
     *"Widespread Underestimation of Sensitivity in Differentially Private
     Libraries and How to Fix It"*, ACM CCS 2022, pp. 471–484, DOI
     `10.1145/3548606.3560708`, `arXiv:2207.10635`.

5. **Hermetic Build Systems, Tensor/ML Compilers, and Catastrophic Backtracking:**
   - Sebastian Erdweg, Moritz Lichter, and Manuel Weiel, *"A Sound and Optimal
     Incremental Build System with Dynamic Dependencies"* (`Pluto`), OOPSLA
     2015, pp. 89–106, DOI `10.1145/2814270.2814316`.
   - Andrey Mokhov, Neil Mitchell, and Simon Peyton Jones, *"Build Systems à la
     Carte"*, PACMPL 2(ICFP):Article 79, 2018, DOI `10.1145/3236774`.
   - Yuanzhong Xu et al., *"GSPMD: General and Scalable Parallelization for ML
     Computation Graphs"*, `arXiv:2105.04663`, 2021.
   - Jiawei Liu, Yiming Lin, Lukasz Ziarek, et al., *"Coverage-Guided Tensor
     Compiler Fuzzing with Joint IR-Pass Mutation"* (`Tzer`), ISSTA 2022, pp.
     400–412, DOI `10.1145/3533767.3534388`.
   - Jiawei Liu, Jinkun Lin, Fabian Ruffy, Cheng Tan, Jinyang Li, Aurojit Panda,
     and Lingming Zhang, *"NNSmith: Generating Diverse and Valid Test Cases for
     Deep Learning Compilers"*, ASPLOS 2023, Vol. 2, pp. 530–543, DOI
     `10.1145/3575693.3575707`.
   - Stack Exchange Status Blog, *"Outage Postmortem — July 20, 2016"* (20,000
     spaces catastrophic backtracking in `^[\s\u200c]+|[\s\u200c]+$`).
   - John Graham-Cumming (Cloudflare), *"Details of the Cloudflare outage on
     July 2, 2019"*, Cloudflare Technical Postmortem, July 12, 2019 (`WAF`
     `.*(?:.*=.*)` CPU exhaustion and migration to the Rust `regex` engine).

## Revalidation

### Part I — Real-World Tool Survey Revalidation

To revalidate the structural mappings and Anneal primitive correspondences in
this report after changes to `trusted/lean/` or the `reference` hardening
packages:

1. **Check the Anneal trusted core definitions (`Trusted/Refinement.lean` and
   `Trusted/StepResult.lean`):**
   Diff `trusted/lean/Trusted/Refinement.lean` and
   `trusted/lean/Trusted/StepResult.lean` against
   `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` to confirm that
   `Partial`, `Language`, `Compiles`, `Abstracts`, `VerificationResultOn`,
   `StepResult`, `ReachesPrefix`, and `BehaviorOf` retain their definitions and
   polarity.
2. **Rerun the mechanized Lean 4 support modules in the sibling hardening
   reports (`joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`):**
   Execute the Lean 4.34.1 kernel checks on:
   - `support/BehaviorCodecExpressiveness.lean`
     (verifying `PartialBehaviorCodec`, `EventualBehaviorOf`, and
     `eventual_wellFormed_iff_prefix_wellFormed`),
   - `support/StructuralExternalCallAndCanaries.lean`
     (verifying `StepResult.externalCall` and `open_world_callback_composition_sound`),
     and
   - `support/ProofGatedCompilationAndTrustPolicy.lean`
     (verifying `ScopedVerificationResult` and `BoundaryCodec`).
3. **Validate the report package metadata and structure:**
   Run `python3 tools/reference.py check` from the root of the `reference`
   worktree.

### Part II — Historical Verification Failure Postmortem Revalidation

To revalidate the architectural bindings between these historical failure modes
and Anneal's `trusted/lean/` primitives when `Trusted/Refinement.lean` or
`Trusted/StepResult.lean` evolves:

1. **Check the four `trusted/lean/` primitive signatures and companion Lean 4
   proofs:**
   Verify that the standalone Lean 4 modules in the companion packages—
   `support/BehaviorCodecExpressiveness.lean`,
   `support/AntiDegeneracyAndCallbackFraming.lean`,
   `support/StructuralExternalCallAndCanaries.lean`,
   and
   `support/ProofGatedCompilationAndTrustPolicy.lean`—
   continue to typecheck with zero kernel axioms (`lean -DElab.async=false
   -Ddebug.skipKernelTC=false`).
2. **Verify each failure-to-primitive discriminator when modifying `trusted/`:**
   - If `Partial` or `Compiles` is modified, confirm that `defined = False`
     remains at $\top$ so target programs cannot introduce new traps (SQL
     division-by-zero pushdowns, P4 invalid header reads, `Halide`/`Triton`
     out-of-bounds accesses) on queries where the source specification is
     defined.
   - If `BehaviorCodec` / `PartialBehaviorCodec` is modified, confirm that
     `decodeOut : L₂.Out → Option L₁.Out`, `decode_encode_out`, and
     `obs_decodeOut` remain intact so non-surjective target states (diverged
     `GSPMD` device shards, unbalanced `DBSP`/`Flink` changelog retractions,
     corrupted SSTable checksums) map to `none` and fail `Compiles`.
   - If `StepResult.externalCall`, `EventualBehaviorOf`, or `ProductiveOn` is
     modified, confirm that `boundaryInv = false` steps to `.failed`, that
     `EventualBehaviorOf` quantifies `defined` over all finite prefixes while
     rejecting `.diverges` (BGP Dispute Wheels, Kubernetes livelocks), and that
     `ProductiveOn` paired with `InhabitedPre` rejects vacuous "abort-all /
     drop-all / deny-all / hold-watermark" implementations.
   - If `VerificationResult` or `TrustPolicy` is modified, confirm that waived
     obligations remain positively scoped on the consequent (`ob.id ∈ waived ∨
     ob.prop`) so an edge-case defect in a waived rewrite rule or hardware model
     cannot discharge unwaived obligations via `False.elim`.
