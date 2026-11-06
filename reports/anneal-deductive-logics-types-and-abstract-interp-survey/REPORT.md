# Deductive Verification, Program Logics, Type Systems, and Abstract Interpretation: Real-World Tools, Historical Failures, and Anneal Refinement Mapping

## Summary

### Part I — Real-World Verification Tools and Refinement Architecture Mapping

Every major deductive verifier, separation-logic framework, borrow-and-aliasing
model, refinement or typestate checker, sound abstract interpreter, and
verification-condition generator (VCGen) across the Rust, C, LLVM, and
interactive-theorem-proving ecosystems reduces to constructing, composing, or
discharging edges in Anneal's four-primitive `trusted/lean/` foundation—without
adding separation logic, predicate transformers, borrow trees, or abstract
domains to the Trusted Computing Base (TCB):

1. **`Language (SemObs : Type)` and `BehaviorCodec L₁ L₂`
   (`Trusted/Refinement.lean`):**
   - `Language SemObs` packages `Prog : Type`, `Query : Type`, `Out : Type`, an
     observation classifier `obs : Out → SemObs`, and a semantic function
     `sem : Prog → Behavior Query Out` where
     `Behavior Query Out := Query → Partial (Out → Prop)`.
   - `BehaviorCodec L₁ L₂` pairs a query retraction
     (`decodeQuery (encodeQuery q₁) = q₁`) with a partial outcome bijection
     (`decodeOut (encodeOut o₁) = some o₁` and
     `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`) that preserves the
     observable spine (`obs_decodeOut : decodeOut o₂ = some o₁ →
     L₂.obs o₂ = L₁.obs o₁`).
   - Downward/horizontal compilation (`Compiles L₁ L₂ codec s t`) and upward
     abstraction (`Abstracts L_v L_src codec v s`) are dual instances of the
     single behavioral refinement inequality
     `L_low.sem t ≤ codec.toMorphism (L_high.sem s)`.

2. **`Language.ProductiveOn` and `InhabitedPre` (`Trusted/Refinement.lean`):**
   - `InhabitedPre pre := ∃ q, pre q`.
   - `L.ProductiveOn pre prog := ∀ q, pre q → ∃ h : (L.sem prog q).defined,
     ∃ o : L.Out, (L.sem prog q).val h o`.
   - Under the order isomorphism between `Behavior Query Out` and monotonic
     predicate transformers, `ProductiveOn` is exactly Dijkstra's Law of the
     Excluded Miracle ($\neg \text{wp}(p, \text{False})$). It blocks
     unsatisfiable prophecy constraints in functional translators (`RustHorn`,
     `Creusot`), prevents contradictory refinement preconditions (`Flux`,
     `Liquid Haskell`) via `InhabitedPre`, and yields **exact determinism as a
     free theorem** whenever composed with a singleton specification.

3. **Positive per-obligation `VerificationResult`
   (`Trusted/Refinement.lean`):**
   - `VerificationResult policy waived obligations :=
     AllHold (waived.map policy.isAllowed) ∧
     AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))`.
   - Replaces antecedent `hTcb → ...` implications so an omitted or waived
     obligation (`ob.id ∈ waived`) cannot discharge other obligations by the
     Principle of Explosion, and allows independent analyzers (e.g., intervals
     in `UC-5.1` and `KnownBits` in `UC-5.2`) to discharge disjoint obligations
     within the same function.

4. **`SmallStepMachine` with `EventualBehaviorOf` and
   `StepResult.externalCall` (`Trusted/StepResult.lean`):**
   - `EventualBehaviorOf` sets `Query := State`, `Out := EventualOut Obs Val`
     (`.terminated (trace : List Obs) (term : Terminal Val)` or `.diverges`),
     and `SemObs := EventualOut Obs Unit`. Because `.failed .ub` and `.stuck`
     make `defined = False` while `.diverges` is a defined outcome in
     `EventualOut`, prefix safety is cleanly decoupled from termination—matching
     step-indexed Iris adequacy (`UC-2.1`) and 1-step abstract-interpretation
     invariants (`UC-5.1`).
   - `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop) :=
     if boundaryInv then .choice .demonic branches else .failed .ub` enforces
     open-world call-site invariants (`AdtInv` re-entrancy guards in `UC-6.4`,
     Tree Borrows protectors in `UC-3.1`, MMIO/DMA typestates in `UC-4.2`, and
     library safety preconditions in `UC-5.4`) at the exact transition of an
     external call.

Five cross-cutting constraints govern how tools in `theory/` instantiate these
four primitives:

- **The `BehaviorCodec` query-retraction and partial-bijection laws:** Because
  `decodeQuery (encodeQuery q₁) = q₁` requires $|L_1.\text{Query}| \le
  |L_2.\text{Query}|$, upward abstractions (`Abstracts L_v L_mir`) cannot add
  unconstrained ghost state to `L_v.Query`; ghost state (`Fractional`
  permissions, `BorrowTree` tags) must either be initialized deterministically
  inside `L_v.sem`, quantified internally via demonic/angelic choice, or framed
  horizontally via `Compiles L_mir L_ghost`. Similarly, because
  `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂` forbids many-to-one outcome
  maps, uninitialized struct padding bytes (`MiniRust`, `CompCert Memdata`) or
  erased ghost metadata must either be projected out of `L_mir.Out` before the
  codec boundary or retained in `L_v.Out` and quotiented in `L_v.obs`.
- **Fuel exhaustion Polarity (`Abstracts` vs. `Compiles`):** In upward
  abstraction (`Abstracts L_loop L_mir`), exhausting loop fuel in `L_loop` must
  map to demonic universal choice (`defined := True`, `val := fun _ => True` or
  `.diverges`), never `.stuck` (`defined := False`), whereas bounded model
  checkers (`Kani`, `crux-mir`) restrict `Query` to bounded-unroll inputs.
- **Angelic vs. demonic provenance (`with_exposed_provenance`):** Because
  `Behavior Query Out` orders nondeterminism demonically, modeling C/Rust
  exposed provenance (`PNVI-ae-udi`, `Cerberus`, `MiniRust`) as a demonic choice
  over all exposed `AllocId`s would falsify `defined` whenever two allocations
  are exposed; `L_mir` must resolve exposed provenance deterministically from
  the unique live allocation covering the target address.
- **Trace safety on diverging loops without coinductive streams:** Although
  `EventualOut.diverges` omits `List Obs`, encoding temporal protocol guards
  (`DMA` pinning, `MMIO` sequencing, `AdtInv`) into `boundaryInv` of
  `StepResult.externalCall` converts any finite-prefix protocol violation on a
  diverging loop into `.failed .ub` (`defined = False`).
- **Diverging external callees in total-correctness proofs:** For termination
  verifiers (`UC-6.3`) to remain sound across `StepResult.externalCall`, any
  external callee that may diverge must either include a diverging transition in
  `branches` or carry an explicit termination obligation in
  `VerificationResult`.

### Part II — Historical Verification Failures, Postmortems, and Architectural Defenses

Across three decades of deductive program verifiers (`Dafny`, `Verus`,
`Creusot`, `Prusti`, `Kani`, `Frama-C WP`, `Why3`, `Boogie`, `Viper`, `F*`,
`KeY`, `ESC/Java2`), separation logics and aliasing models (`RustBelt`,
`Stacked Borrows`, `Tree Borrows`, `Polonius`, LLVM/C pointer provenance), and
static abstract interpreters (the Linux kernel eBPF verifier, `Astrée`,
`Frama-C Eva`, `IKOS`, `MIRAI`), verification failures cluster into six
recurring structural root causes rather than isolated coding mistakes:

1. **Vacuous refinement via over-constrained prophecies, false assumptions, or
   demonic miracles:** A translation pass or intermediate verification language
   (IVL) emits an unsatisfiable assumption (`assume false`, an inconsistent
   prophecy resolution equation in `RustHorn`/`Creusot`, or an broken inhale
   encoding in `Viper`/`Boogie`), collapsing the post-state set to $\emptyset$
   and allowing any postcondition—including `ensures false`—to pass.
2. **Inconsistent prelude axioms and uninhabited refinement domains:** Background
   SMT preludes (`Dafny` `#6534`, `#6537`), VC simplifiers (`F*` `#4485`), or
   liquid refinement signatures (`x > 10 && x < 5`) make the entry precondition
   unsatisfiable, discharging universal safety claims over an empty domain.
3. **Antecedent waiver and trusted-boundary contamination:** Unverified helper
   specifications (`#[trusted]`, `admit()`, `external_body`, or waived
   obligations) injected as logical hypotheses in an implication antecedent
   ($H_{\text{waived}} \to G_{\text{verified}}$) silently discharge unrelated
   safety obligations whenever a waived hypothesis is inconsistent.
4. **Open-world callback re-entrancy and exceptional/unwind control-flow
   omissions:** Verifiers check representation invariants (`AdtInv`) only at
   normal function return while ignoring mid-method state during external
   closure callbacks (`Vec::dedup_by`, `RefCell`, `MutexGuard::map` in
   `rust-lang/rust#25760`) or along stack-unwinding edges (`Charon`
   `reconstruct_fallible_operations`, `KeY`/`ESC/Java2` abrupt termination).
5. **Operational aliasing and pointer-provenance mismatches:** Overly rigid
   aliasing models (`Stacked Borrows` rejecting valid two-phase borrows,
   `addr_of!`, and `Pin` patterns) cause false-positive UB rejections that force
   users into `#[trusted]` bypasses, while overly permissive flat-memory or
   round-trip cast folds (`llvm#34548`, `llvm#35229`, `PNVI` GVN+AA
   interactions) miscompile valid low-level pointer arithmetic.
6. **Unsound abstract transformers, state pruning, and SMT quantifier
   instability:** Hand-written abstract transfer functions (`Linux eBPF` `tnum`
   and 32/64-bit subregister bounds in `CVE-2020-8835`, `CVE-2021-3490`,
   `CVE-2021-31440`, `CVE-2022-23222`, and state-pruning taint omissions in
   `CVE-2023-2163`) violate concretization soundness, while heuristic E-matching
   in SMT-backed verifiers (`IronFleet`, `Dafny`, `Verus`, `Viper`) causes
   non-deterministic proof collapse ("the butterfly effect") under minor code
   edits.

Anneal's four orthogonal `trusted/lean/` primitives are specifically shaped to
block these six failure modes at the Lean 4 kernel boundary without expanding
the trusted computing base (TCB):

- **`Language SemObs` + `BehaviorCodec` (`Compiles` / `Abstracts`):** Separates
  downward compilation from upward abstraction via a partial-bijection codec
  whose left-inverse query law (`decodeQuery (encodeQuery q₁) = q₁`) and
  observable spine alignment (`obs_decodeOut`) prevent unverified frontend
  rewrites or ghost-state erasure from silently dropping failure behaviors.
- **`ProductiveOn` + `InhabitedPre`:** Enforces Dijkstra's Law of the Excluded
  Miracle ($\forall q,\, \text{pre}(q) \to \exists h\,o,\, (L.\text{sem}\,p\,q).\text{val}\,h\,o$)
  together with domain non-emptiness ($\exists q,\, \text{pre}(q)$), ruling out
  both empty-outcome prophecy miracles and contradictory refinement domains.
- **Positive per-obligation `VerificationResult`:** Formulates obligation
  tracking as a positive conjunction of disjunctions
  `AllHold (waived.map policy.isAllowed) ∧ AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))`,
  eliminating antecedent Principle-of-Explosion contamination across obligations.
- **`SmallStepMachine` with `EventualBehaviorOf` + `StepResult.externalCall`:**
  Separates finite-prefix undefinedness (`.failed .ub` / `.stuck`, mapped to
  `defined = False` in `Partial`) from non-termination (`.diverges`, mapped to a
  defined `EventualOut` outcome), preserves explicit normal vs. unwind termination
  in `Terminal Val`, and checks `boundaryInv : Bool` at every `externalCall`
  step so broken `AdtInv` or active Tree Borrows protectors fail immediately
  upon callback invocation.

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

This report applies to the design of verification engines, specification
languages, and certificate checkers in Anneal's `theory/` layer targeting
Anneal's `trusted/lean/` boundary (`joshlf/anneal` repository revision
`24367bd1a8c784f2578535954f9915e24894a56f`, baseline refinement definitions in
worktree revision `24367bd1a8c784f2578535954f9915e24894a56f` at
`trusted/lean/Trusted/Refinement.lean` and
`trusted/lean/Trusted/StepResult.lean`, and the four-primitive model-refined
architecture in `Trusted/Refinement.lean` and `Trusted/StepResult.lean`
synthesized in `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`
and `anneal-structural-external-calls-and-tcb-mutation-testing-2026`).

The 28 external tool-family subjects in `REPORT.json` are examined as
comparative architectural specimens and source-of-truth implementations across
six verification families (`UC-1.1` through `UC-6.4`):

1. **Category A (`UC-1.1`–`UC-1.4`):** Functional translators and symbolic
   evaluators (`Aeneas`, `Charon`, `RustHorn`, `RustHornBelt`, `Creusot`/`Coma`,
   `coq-of-rust`/`rocq-of-rust`, `Electrolysis`, `hacspec`/`hax`,
   `AutoCorres`/`AutoCorres2`, `Interaction Trees`/`Vellvm`,
   `FreeSpec`/`DimSum`, `Lean 4 bv_decide`, `SAW`/`Crucible`/`crux-mir`, `Kani`,
   `Rosette`/`Serval`, `HolBA`/`Islaris`/`Sail`).
2. **Category B (`UC-2.1`–`UC-2.4`):** Separation logics and spatial resource
   engines (`Iris`/`MoSeL`, `iris-lean`, `RustBelt`, `RefinedC`/`Caesium`,
   `RefinedRust`, `VST`, `CN`/`Fulminate`, `VeriFast`, `Viper`/`Prusti`,
   `Gillian`/`Gillian-Rust`, `Smallfoot`/`Infer`/`Pulse`, `VerCors`,
   `Steel`/`Pulse` in F\*, `GhostCell`/`qcell`, `Verus` `Tracked<PointsTo<T>>`
   and `PCell`).
3. **Category C (`UC-3.1`–`UC-3.4`):** Aliasing and borrow models (`Miri`,
   `Stacked Borrows`, `Tree Borrows`, `BorrowSanitizer`, `Polonius`,
   `Oxide`/`Patina`, `Aquascope`, `Strict/Exposed Provenance`, `VIP`,
   `CompCertS`/`Quasi-Concrete`, `CHERI`/`Morello`, `MiniRust`, `Cerberus`,
   `CompCert Memdata`).
4. **Category D (`UC-4.1`–`UC-4.4`):** Type systems, typestates, and effect
   checkers (`Flux`, `Liquid Haskell`, `Stainless`, `embedded-hal`/`embassy`,
   `Verus tokenized_state_machine!`, `Austral`/`Vale`, `no-panic`,
   `rtsan`/`cargo-call-stack`, `F*`/`Low*`/`KaRaMeL`, `Koka`/`Effekt`).
5. **Category E (`UC-5.1`–`UC-5.4`):** Sound static analyzers and abstract
   interpreters (`Verasco`, `Astrée`, `Crab`/`SeaHorn`, `IKOS`, `MIRAI`,
   `eBPF tnum`/`Agni`/`PREVAIL`, `LLVM KnownBits`, `Frama-C Eva`, `Goblint`,
   `Mopsa`, `Rudra`/`SafeDrop`/`Lockbud`, `TVLA`/`Forester`, `MemCAD`/`Xisa`).
6. **Category F (`UC-6.1`–`UC-6.4`):** VCGens, characteristic formulae,
   termination engines, and modular object invariants (`F*`/`DM4All`, `Why3`,
   `Boogie`, `Lean 4 MPL`/`Std.Do`, `CFML 2.0`/`SPLean`, `CakeML CF`,
   `AProVE`/`Ultimate Automizer`, `CeTA`/`IsaFoR`, `Foetus`,
   `Terminator`/`RankFinder`, `Dafny`/`VCC`).

Claims about each external tool apply to its pinned repository revision or
published paper in `REPORT.json`; architectural mappings onto Anneal's four
primitives are `derived` engineering designs for `theory/` verified against the
definitions in `Trusted/Refinement.lean` and `Trusted/StepResult.lean`.

### Part II Applicability — Historical Verification Failures and Postmortems

This report synthesizes primary historical failure records, CVE root-cause
commits, upstream issue trackers, and published postmortems across four families
of formal verification systems, and evaluates their architectural implications
for the Anneal verification platform at
`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`:

- **Deductive verifiers and IVL pipelines:** `Dafny` (`dafny-lang/dafny` issues
  `#4053`, `#6534`, `#6537`), `Verus`
  (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c` and arXiv
  `2303.05491v2`), `Creusot` and `RustHornBelt` (`creusot-rs/creusot`, DOI
  `10.1145/3519939.3523704`), `Prusti` and `Viper`/`Boogie`
  (`viperproject/prusti-dev`, DOI `10.1007/978-3-030-81688-9_33`, DOI
  `10.1145/3656438`), `Kani` (`model-checking/kani` `[F] Soundness` corpus),
  `F*` (`FStarLang/FStar` issues `#4478`, `#4485`, `#4487`), `Frama-C WP` /
  `Why3`, and `KeY` / `ESC/Java2`.
- **Separation logics, borrow checkers, and aliasing/provenance models:**
  `RustBelt` (DOI `10.1145/3158154`, `rust-lang/rust#25760`), `RustBelt Meets
  Relaxed Memory` (DOI `10.1145/3371102`, `rust-lang/rust#51780`), `Stacked
  Borrows` (DOI `10.1145/3371109`), `Tree Borrows` (DOI `10.1145/3729338`),
  `rustc` NLL/Polonius and trait-solver soundness issues (`rust-lang/rust#25860`,
  `#84591`, `#100013`), and LLVM/C/Rust pointer-integer provenance bugs
  (`llvm#34548`, `llvm#35229`, DOI `10.1145/3062341.3062343`, DOI
  `10.1145/3276495`).
- **Abstract interpreters and static analyzers:** Linux kernel eBPF verifier
  (`torvalds/linux` commits `581738a681b6`, `049c4e13714e`, `10bf4e83167c`,
  `64620e0a1e71`, `71b547f56124` for `CVE-2020-8835`, `CVE-2021-3490`,
  `CVE-2021-31440`, `CVE-2022-23222`, `CVE-2023-2163`), `Agni` range-analysis
  verification (DOI `10.1109/CGO53902.2022.9741267`, DOI
  `10.1007/978-3-031-37709-9_12`), `Astrée`, `Frama-C Eva`, `IKOS`, and `MIRAI`.
- **Functional translators and SMT proof-stability studies:** `Electrolysis`
  (Ullrich 2016), `Aeneas` and `Charon`
  (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, DOI
  `10.1145/3547647`), `IronFleet` (DOI `10.1145/2815400.2815428`), Dafny trigger
  selection (DOI `10.1007/978-3-319-41528-4_20`), and `Mariposa` (DOI
  `10.1145/3622852`).

"Failure" is construed broadly to encompass (a) confirmed soundness bugs and
CVEs where a verifier or static analyzer accepted unsafe code or allowed proving
`false`, (b) vacuity bugs where inconsistent axioms or preconditions rendered a
theorem empty, (c) expressiveness and semantic-model mismatches where valid
idiomatic systems code was rejected, and (d) proof-maintenance collapses where
verification became intractable or brittle at scale.

## Findings

### Part I — Real-World Verification Tools Mapped to Anneal's Refinement Primitives

### 1. Cross-cutting mathematical foundations of the four-primitive mapping

#### 1.1 The `BehaviorCodec` query-retraction and partial-bijection laws

In `Trusted/Refinement.lean`, `Language (SemObs : Type)` equips a language's
outcome type `Out` with an observation projection `obs : Out → SemObs`, and
`BehaviorCodec L₁ L₂` links two languages over the same `SemObs` via four laws:

- `decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁`
- `decodeOut_encodeOut : ∀ o₁, decodeOut (encodeOut o₁) = some o₁`
- `encodeOut_of_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`
- `obs_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁`

Theinduced monotone behavior morphism `codec.toMorphism : L₁.Behavior →
L₂.Behavior` maps a behavior `b₁ : L₁.Query → Partial (L₁.Out → Prop)` to:

```lean
fun q₂ =>
  let p₁ := b₁ (codec.decodeQuery q₂)
  { defined := p₁.defined
    val := fun h o₂ =>
      ∃ o₁, codec.decodeOut o₂ = some o₁ ∧ p₁.val h o₁ }
```

Two immediate cardinal constraints follow from these laws:

1. **Query Retraction ($|L_1.\text{Query}| \le |L_2.\text{Query}|$):** Because
   `decodeQuery` is a left inverse to `encodeQuery`, `encodeQuery` is injective.
   In upward abstraction `Abstracts L_v L_mir codec v s`
   (`L_mir.sem s ≤ codec.toMorphism (L_v.sem v)`), `L_v.Query` must be a
   coarser or projected query space (such as mathematical input values `PureIn`
   paired with a layout witness) that `encodeQuery` embeds into a canonical
   initial `MirState`. When a verifier instead augments `MirState` with ghost
   state (e.g., fractional permissions `Addr → Rat` in `UC-2.3` or Tree Borrows
   shadow trees in `UC-3.1`), `MirState × GhostState` is strictly larger than
   `MirState` and cannot serve as `L_v.Query` with `decodeQuery : MirState →
   MirState × GhostState`. Instead, `theory/` has three sound options:
   - keep `L_v.Query := MirState` and initialize the ghost state
     deterministically inside `L_v.sem` via `initGhost : MirState → GhostState`
     (or quantify over valid initial ghost states inside `L_v.sem`);
   - formulate the ghost instrumentation horizontally as
     `Compiles L_mir L_ghost codec s v`, where
     `encodeQuery : MirState → MirState × GhostState` injects initial ghost
     state and `decodeQuery := Prod.fst` satisfies
     `decodeQuery (encodeQuery s) = s`; or
   - discharge `L_mir.sem s ≤ L_mir.SpecOn pre post` directly inside `theory/`
     via a relational simulation invariant
     $\mathcal{R} : \text{MirState} \to \text{GhostState} \to \text{Prop}$
     (as in Iris adequacy, `UC-2.1`).

2. **Outcome Partial Bijection (`encodeOut_of_decodeOut`):** The law
   `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂` forces `decodeOut` to be
   injective on its `some` domain, preventing a rogue codec from collapsing
   distinct concrete outcomes onto a single abstract value. Consequently, if two
   concrete outcomes $o_2 \neq o_2'$ in `L_mir.Out` differ only in uninitialized
   struct padding bytes (`UC-3.4`, `UC-5.3`) or erased ghost state, `decodeOut`
   cannot map both to `some o₁`. Either `L_mir.Out` must project out
   non-observable heap padding before constructing `EventualOut Obs ReturnVal`,
   or `L_v.Out` must retain the representation choice and quotient it in
   `L_v.obs : L_v.Out → SemObs`.

Basis: **source** — `Trusted/Refinement.lean:234-385` in
`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` and
`anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`;
**derived** — cardinal constraints on ghost state and padding bytes.

#### 1.2 Predicate-transformer isomorphism and `ProductiveOn` as the Law of the Excluded Miracle

Every `b : Behavior Query Out` (`Query → Partial (Out → Prop)`) corresponds
bijectively to a monotonic predicate transformer
$\text{toWP}(b) : (\text{Out} \to \text{Prop}) \to (\text{Query} \to \text{Prop})$:

$$\text{toWP}(b)(Q)(q) :=\; \exists h : (b\,q).\text{defined},\; \forall o,\, (b\,q).\text{val}\,h\,o \to Q(o)$$

Under this isomorphism, `b ≤ L.SpecOn pre post` is equivalent to
$\forall q,\, \text{pre}(q) \to \text{toWP}(b)(\text{post}\,q)(q)$. However, if
$(b\,q).\text{defined} = \text{True}$ and $(b\,q).\text{val}\,h = \lambda \_.\,
\text{False}$ (an empty outcome set), then $\text{toWP}(b)(Q)(q)$ holds for
*every* postcondition $Q$, including $Q = \lambda \_.\,\text{False}$—a demonic
miracle in Dijkstra's sense. Pairing `SpecOn` or `Abstracts` with:

$$\text{L.ProductiveOn}\,\text{pre}\,p :=\; \forall q,\, \text{pre}(q) \to \exists h : (L.\text{sem}\,p\,q).\text{defined},\; \exists o,\, (L.\text{sem}\,p\,q).\text{val}\,h\,o$$

and `InhabitedPre pre := ∃ q, pre q` enforces $\neg \text{toWP}(L.\text{sem}\,p)
(\lambda \_.\,\text{False})(q)$ on a non-empty domain `pre`. Furthermore, when a
concrete program `s` satisfies both `Abstracts L_det L_mir codec v_det s`
against a deterministic singleton model `(L_det.sem v_det q).val h =
fun o => o = f q` and `L_mir.ProductiveOn pre s`, every concrete outcome set is
a non-empty subset of a singleton ($\emptyset \subsetneq S \subseteq
\{\text{encodeOut}(f(\text{decodeQuery}\,q))\}$), establishing exact
determinism without a dedicated determinism primitive in `trusted/`.

Basis: **source** — `Trusted/Refinement.lean:260-358`; **derived** — Dijkstra
predicate-transformer bijection and singleton determinism theorem.

---

### 2. Category A: Functional translators and symbolic evaluators (`UC-1.1`–`UC-1.4`)

#### 2.1 `UC-1.1`: Lens and prophecy functional translators (`Aeneas`, `Charon`, `RustHorn`, `RustHornBelt`, `Creusot`/`Coma`, `coq-of-rust`, `Electrolysis`, `hacspec`/`hax`)

##### Goals, problem domain, and target users

Functional translators eliminate mutable memory and pointer aliasing from safe
(and borrow-disciplined) Rust programs by translating them into pure functional
specifications in interactive theorem provers (Lean 4, Rocq/Coq, F\*, HOL4) or
SMT-backed deductive verifiers (Why3/Coma, CHC solvers). Their target users are
verification engineers proving rich algorithmic invariants—such as B-tree
balancing, cryptographic protocols (TLS, MLS, post-quantum Kyber/ML-KEM), and
zero-copy parsers—who want to reason by induction over algebraic datatypes
rather than spatial heap separation (`*`).

##### Development history, lineage, and evolution

- **`Electrolysis` (`Kha/electrolysis`, Sebastian Ullrich, MSc Thesis 2016):**
  Pioneered translating safe Rust MIR into Lean 2 by interpreting nested mutable
  borrows (`&mut (*x).field`) as compositional functional **lenses** (`get : S →
  A`, `set : S → A → S`) whenever borrow lifetimes follow a strict stack
  discipline.
- **`RustHorn` (Matsushita, Tsukada, Kobayashi, ESOP 2020 / TOPLAS 2021, DOI
  `10.1145/3462205`) and `RustHornBelt` (Matsushita, Denis, Jourdan, Dreyer,
  PLDI 2022, DOI `10.1145/3519939.3523704`):** Replaced lenses with **prophecy
  variables**: a mutable borrow `&'a mut T` is represented as a pair
  $(v_{\text{cur}}, v_{\text{final}}) : T \times T$, where $v_{\text{final}}$
  prophesies the value stored in the referent when lifetime `'a` ends.
  `RustHorn` compiles safe Rust directly into Constrained Horn Clauses (CHCs);
  `RustHornBelt` proved this prophetic translation sound inside Iris (`lambda-rust`)
  and extended it with parametric separation-logic specifications (`RustBelt`)
  at `unsafe` abstraction boundaries.
- **`Creusot` and `Coma` (`creusot-rs/creusot@c4e9770ac1371ac4274bfe02145266d315c2fb86`,
  Denis, Jourdan, Marché ICFEM 2022; Patault, Pereira, Why3/Coma ESOP 2025):**
  Builds on `RustHornBelt`'s prophetic mutable-borrow semantics (`^x` for final
  prophetic value, `*x` for current value) in its first-order specification
  language **Pearlite**, compiling Rust MIR to the **Coma** continuation-passing
  intermediate verification language and discharging VCs through Why3 to Z3,
  cvc5, and Alt-Ergo.
- **`Charon` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
  v0.1.210) and `Aeneas` (`AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`,
  Ho & Protzenko ICFP 2022 DOI `10.1145/3547647`; Ho, Ayoun, Protzenko ICFP 2024
  DOI `10.1145/3674640`):** `Charon` hooks into `rustc` to extract unstructured
  (`ULLBC`) and structured (`LLBC`) Low-Level Borrow Calculus ASTs. `Aeneas`
  symbolically executes `LLBC` using a borrow-aware symbolic loan environment,
  translating functions that take/return mutable borrows into pure functions
  returning **backward functions** (which compute updated borrowed inputs when
  outer region lifetimes end) in Lean 4, F\*, Rocq, and HOL4.
- **`hacspec` and `hax` (`cryspen/hax@1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`,
  Bhargavan et al. / Cryspen):** Evolved from the executable cryptographic
  specification subset `hacspec` into the general `rustc` frontend `hax`, which
  extracts THIR into pure functional ASTs for F\*, Rocq, ProVerif, and Lean 4
  (where `hax`'s Lean 4 backend `Hax/Tactic/HaxMvcgen.lean` now interoperates
  with Lean's `Std.Do` / `mvcgen` infrastructure and Aeneas).
- **`coq-of-rust` / `rocq-of-rust`
  (`formal-land/rocq-of-rust@ca1374ae2fdeb28b069fe77ba412db5604525261`):**
  Translates `rustc` THIR into a shallow monadic embedding in Rocq (`M` monad
  with `M.alloc`, `M.read`, `M.write`, and trait-hierarchy typeclasses), used
  to verify `revm` and `core`/`alloc` slices via manual user-written simulation
  relations linking the `M` monad to purely functional Rocq models.

##### Design philosophy, architectural tradeoffs, and ecosystem comparisons

| Tool | Extraction Hook | Mutable-Borrow Elimination Mechanism | Loop Handling | `unsafe` Code Strategy | TCB / Soundness Basis |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`Electrolysis`** | `rustc` MIR | Stack-disciplined lenses (`get`/`set`) | Structural recursion | Axiom stubs | Untrusted Rust-to-Lean translator |
| **`RustHorn` / `Creusot`** | `rustc` MIR | First-order prophecy variables (`*x`, `^x`) | Loop invariants in Pearlite / Coma handlers | Trusted `#[trusted]` axioms justified on paper by `RustHornBelt` | Trusts `rustc`, `Creusot` MIR-to-Coma translator, Why3, and SMT solvers |
| **`Aeneas` + `Charon`** | `rustc` MIR $\to$ LLBC | Symbolic borrow graphs $\to$ pure backward functions | Fixed-point `loop` combinator + `Std/WP.lean` (`loop.spec_decr_nat`) | Assumed external models (`Std/Primitives.lean`); ongoing spatial PR1352 | Paper soundness theorem (`ICFP 2022`/`2024`); `Charon` + `Aeneas` OCamls in TCB |
| **`hax`** | `rustc` THIR | Pure functional value updates (in-place mutation without returned `&mut`) | Functional fold/recursion | Assumed backend primitives | Trusts `hax` THIR extractor and printer |
| **`rocq-of-rust`** | `rustc` THIR | None at extraction (kept in state/address monad `M`, proved away interactively) | Fuel-indexed monadic recursion | Monadic memory simulation | Trusts `rocq-of-rust` THIR translator |

**Prophecies (`RustHorn`/`Creusot`) vs. Backward Functions (`Aeneas`):**
Prophecies collapse forward execution and future borrow updates into a single
first-order relation by guessing $v_{\text{final}}$ upfront and asserting
$v_{\text{actual}} = v_{\text{final}}$ when the borrow expires. This suits
automated first-order SMT/CHC solvers (`Z3`, `Spacer`) because it avoids
higher-order continuations, but in an interactive proof assistant (Lean 4, Rocq)
it forces users to thread existential prophecy witnesses through definitions.
Conversely, `Aeneas`'s backward functions (`f_fwd` / `f_back` or combined tuple
returns in `Std/Primitives.lean` with `Result α`) produce executable,
deterministic functional definitions in Lean 4 (`@[step]` / `StepStar` in
`Tactic/Step/`), at the cost of requiring region-hierarchy splitting when a
function returns a mutable borrow aliased to multiple input regions.

##### Formal theory, specification methodology, proof automation, and TCB

In `Aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`, translated Lean 4 functions
live in the error monad `Result α` (`ok : α → Result α`, `fail : Error →
Result α`, `div : Result α` in `backends/lean/Aeneas/Std/Primitives.lean`).
Verification uses a syntax-directed weakest-precondition calculus (`Std/WP.lean`
and `Tactic/Step/`) coupled with domain-specific arithmetic automation
(`scalar_tac` in `Tactic/Solver/ScalarTac.lean` and `bv_tac` in
`Tactic/Solver/BvTac.lean`). However, in standalone `Aeneas`, `Creusot`, and
`hax`, the OCaml/Rust translation pipeline from `rustc` MIR/THIR to the target
prover AST is **unverified and inside the TCB**: a bug in `Charon`'s borrow
reconstruction or `Creusot`'s prophecy resolution silently produces a Lean/Coma
model that diverges from actual `rustc` MIR semantics.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal, the functional translator is **removed from the TCB** by formulating
each translated pure Lean function `f_pure` in `theory/` as an upward
abstraction of the captured `Runtime(PostCleanup)` MIR body `f_mir`:

1. **`Abstracts L_pure L_mir codec f_pure f_mir` (`Language SemObs` +
   `BehaviorCodec`):**
   - `L_pure.Query := PureIn × LayoutWitness` (algebraic input values plus
     disjoint heap layout coordinates).
   - `L_pure.Out := EventualOut Obs PureOut` and
     `L_pure.SemObs := EventualOut Obs Unit` (identical to `L_mir.SemObs`).
   - `codec.encodeQuery` materializes `PureIn` into disjoint allocations in
     `MirState`; `codec.decodeQuery` reads them back (`decodeQuery (encodeQuery q) = q`).
   - `codec.decodeOut : L_mir.Out → Option L_pure.Out` checks that the final
     `MirState` satisfies the backward-function or prophecy equations and that
     all non-borrowed memory frames are preserved, returning `none` on any frame
     violation. Because `Abstracts` requires every concrete outcome of `f_mir`
     to lie in the `some` domain of `decodeOut`, proving `Abstracts`
     automatically certifies memory framing.
2. **`L_pure.ProductiveOn pre_pure f_pure` and `InhabitedPre pre_pure`:**
   - In a `RustHorn`/`Creusot`-style prophetic translation, an over-constrained
     or buggy prophecy resolution equation $v_{\text{actual}} = v_{\text{final}}$
     would make the outcome predicate `(L_pure.sem f_pure q).val h` empty
     (`fun _ => False`), vacuously satisfying every postcondition.
     `L_pure.ProductiveOn pre_pure f_pure` forces `theory/` to exhibit a valid
     execution outcome `o` for every `q` satisfying `pre_pure`, mathematically
     ruling out prophetic miracles.

Basis: **source** — `AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`,
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
`creusot-rs/creusot@c4e9770ac1371ac4274bfe02145266d315c2fb86`,
`cryspen/hax@1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`,
`formal-land/rocq-of-rust@ca1374ae2fdeb28b069fe77ba412db5604525261`, and
`rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026`;
**derived** — `Abstracts` + `ProductiveOn` bridge in `theory/`.

---

#### 2.2 `UC-1.2`: Loop-fuel and cut-point invariant functional extractors (`AutoCorres`/`AutoCorres2`, `Aeneas` `CCPO`/`loop`)

##### Goals, problem domain, and target users

Low-level systems languages (`Runtime(PostCleanup)` MIR, C SIMPL) represent
arbitrary control flow (`while`, `for`, `loop`, `break`, `continue`, `?` early
returns, and unwinding cleanup ladders) as cyclic basic-block control-flow
graphs (CFGs). Interactive theorem provers (Lean 4, Isabelle/HOL, Rocq) require
pure definitions to be total—either by well-founded recursion, fuel indexing,
or complete partial order (`CCPO`) least fixed points.

##### Development history, lineage, and evolution

- **`AutoCorres` (Greenaway, Lim, Andronick, Klein, PLDI 2014, DOI
  `10.1145/2594291.2594296`) and `AutoCorres2` (Isabelle/HOL Archive of Formal
  Proofs):** Built on Norrish's C-to-Isabelle parser (`SIMPL`) for the seL4
  microkernel proof. `AutoCorres` translates deeply embedded C `SIMPL`
  statements into shallowly embedded monadic Isabelle/HOL functions through a
  staged pipeline (`L1` control-flow exception elimination $\to$ `L2` local
  variable lifting to SSA-like monadic bindings $\to$ `HL` heap abstraction
  splitting typed pointers $\to$ `WA` word abstraction from `word32` to `nat`/`int`
  with overflow guards $\to$ `TS` type strengthening into `option`/pure
  functions), generating an end-to-end Isabelle/HOL refinement proof for every
  translated function.
- **`Aeneas` `CCPO` Fixed-Point Loop Combinator
  (`AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`,
  `backends/lean/Aeneas/Std/Primitives.lean` and `Std/WP.lean`):** Uses
  Bourdoncle's weak topological ordering (WTO) in OCaml (`charon` / `aeneas`) to
  reconstruct structured loops from MIR CFGs, emitting recursive body
  definitions tied by a partial-order fixed point `loop` in `Result α` and
  providing both partial-correctness and total-correctness (`loop.spec_decr_nat`)
  WP rules.

##### Design philosophy, architectural tradeoffs, and formal theory

`AutoCorres` is **certifying** (proof-producing): its ML tactic constructs an
Isabelle kernel proof that the shallow monadic function refines the deeply
embedded `SIMPL` AST. By contrast, `Aeneas`'s WTO loop reconstruction happens
outside Lean in OCaml. When reconstructing loops from arbitrary MIR CFGs in
Anneal's `theory/`, a cut-point invariant or fuel-unrolling combinator must
handle diverging executions soundly.

##### Exact mapping onto Anneal's four `trusted/` primitives

In `Abstracts L_loop L_mir codec f_loop f_mir`
(`L_mir.sem f_mir ≤ codec.toMorphism (L_loop.sem f_loop)`):

- **Total correctness via well-founded measure $\mu : \text{CutState} \to
  \mathbb{N}$:** `f_loop` is defined by well-founded recursion on $\mu(q)$, and
  `(L_loop.sem f_loop q).val h .diverges` is `False`. By `Abstracts`,
  `L_mir.sem f_mir ≤ codec.toMorphism (L_loop.sem f_loop)` immediately proves
  `¬ (L_mir.sem f_mir q).val h .diverges` (termination of the concrete MIR
  CFG).
- **Partial correctness / fuel unrolling (`Fuel : Nat`):** If a fuel-indexed
  abstract evaluator `L_loop` mapped fuel exhaustion ($k = 0$) to `.stuck` or
  `.failed` (`defined := False`), then `Abstracts` would require `L_loop` to be
  `defined` whenever `L_mir` is `defined`—which is **false** if the concrete
  loop executes $k + 1$ iterations! Therefore, in upward `Abstracts`, unverified
  or fuel-exhausted cut-off paths in `L_loop` must map to **demonic universal
  choice** (`defined := True`, `val := fun _ => True` or `.diverges`), whereas
  bounded model checking restricts `Query` to inputs that terminate within $k$
  iterations.

Basis: **source** — `autocorres-guarded-model-certificates-pldi-2014`,
`AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`, and
`Trusted/Refinement.lean:380-385`; **derived** — opposite polarity of fuel
exhaustion in `Abstracts` vs. `Compiles`.

---

#### 2.3 `UC-1.3`: Higher-order closures, `dyn Trait`, and interaction trees (`Interaction Trees`/`Vellvm`, `FreeSpec`/`DimSum`)

##### Goals, problem domain, and target users

Systems and library code in Rust and LLVM invokes unknown callbacks (`FnMut`,
`&mut dyn Write`), FFI routines, and cross-language modules, interleaving
internal state transitions with observable external events and nondeterminism.

##### Development history, lineage, and evolution

- **`Interaction Trees` (`DeepSpec/InteractionTrees@a2bc2c38ad998dccadb932559c922139dd957c4f`,
  Xia et al., POPL 2020, DOI `10.1145/3371119`) and `Vellvm`
  (`vellvm/vellvm@506f1eb0be542611521985719b971fbce8498dc9`, Zakowski et al.,
  ICFP 2021):** `ITree E R` is a coinductive free monad with three constructors:
  `Ret (r : R)`, `Tau (t : ITree E R)` (silent internal step), and
  `Vis {A : Type} (e : E A) (k : A → ITree E R)` (visible external event with
  answer continuation $k$). `Vellvm` layers an algebraic handler stack (`L0`
  syntactic VIR $\to$ `L1` global environment $\to$ `L2` local stack $\to$ `L3`
  byte/poison memory `DTYPE_B` $\to$ `L4` angelic/demonic nondeterminism `PropT`)
  and reasons via weak bisimulation (`eutt`, equivalence up to tau).
- **`FreeSpec` and `DimSum` (Sammler et al., POPL 2023, DOI `10.1145/3571220`):**
  `DimSum` models open multi-language modules (Rec, Asm, C) as transition
  systems over explicit incoming and outgoing call/return events, enabling
  horizontal and vertical linking of mutually recursive callbacks across
  language boundaries.

##### Design philosophy, architectural tradeoffs, and ecosystem comparisons

Coinductive `ITree` weak bisimulation (`eutt`) in Rocq requires extensive PACO
(parameterized coinduction) machinery, struggles when composing with relational
set-of-traces (`PropT`) nondeterminism (`eutt` is not a congruence under
unbounded demonic choice without carefully stratified monad transformers), and
cannot be natively defined as a primitive `coinductive` type in Lean 4's kernel
without quotient polynomial functors (`alexkeizer/QpfTypes@5b5dd4f83121662838b99d129b92f632f263c508`).

##### Exact mapping onto Anneal's four `trusted/` primitives

Anneal achieves the full compositional power of `ITrees` and `DimSum` inside
`trusted/lean/` **without coinduction or `Classical.choice`**:

1. **Tau-Insensitive Step Elasticity via `EventualBehaviorOf`:**
   `EventualBehaviorOf` defines `Out := EventualOut Obs Val` with inductive
   reachability `.terminated (trace : List Obs) (term : Terminal Val)` and
   universal non-termination `.diverges`. Silent internal transitions (`Tau` /
   `.choice .demonic`) do not append to `trace : List Obs` and are existentially
   quantified over step count $n : \mathbb{N}$ in `.terminated`, giving `eutt`'s
   finite-tau erasure (`1 → 0`, `1 → k`, `k → 1`) by ordinary inductive
   reachability.
2. **External Call Effects via `StepResult.externalCall` and Shared `SemObs`:**
   When `SmallStepMachine` executes an unresolved indirect call (`dyn Trait`
   vtable or external symbol), it steps via
   `StepResult.externalCall boundaryInv branches` and emits `Obs.extCall`. Both
   an abstract interaction-tree model `L_itree` in `theory/` and `L_mir` share
   `SemObs := EventualOut Obs Unit`, so `codec.obs_decodeOut` holds by `rfl` on
   `trace : List Obs`.

Basis: **source** — `DeepSpec/InteractionTrees@a2bc2c38ad998dccadb932559c922139dd957c4f`,
`vellvm/vellvm@506f1eb0be542611521985719b971fbce8498dc9`, DimSum POPL 2023 DOI
`10.1145/3571220`, and `Trusted/StepResult.lean`; **derived** — coinduction-free
`EventualBehaviorOf` + `StepResult.externalCall` correspondence.

---

#### 2.4 `UC-1.4`: Bit-precise symbolic evaluators (`Lean 4 bv_decide`, `SAW`/`Crucible`/`crux-mir`, `Kani`, `Rosette`/`Serval`, `HolBA`/`Islaris`/`Sail`)

##### Goals, problem domain, and target users

Cryptographic primitives (AES, SHA-256, ChaCha20, Curve25519), binary wire
parsers, `zerocopy` byte transmutations, SIMD routines, and OS kernel/firmware
handlers require bit-exact reasoning over fixed-width two's-complement integers
(`UInt8`..`UInt128`), bitshifts, endianness, and byte arrays without interactive
arithmetic proofs.

##### Development history, lineage, and evolution

- **`SAW`, `Crucible`, and `crux-mir`
  (`GaloisInc/saw-script@27a7ae98256544b55a7a3ce4ce620c1a7889713b`,
  `GaloisInc/crucible@7f49dac06c656f7b92c8b6cc054f47c63b60abe4`):** Galois's
  Software Analysis Workbench (`SAW`) symbolically executes LLVM, JVM, and Rust
  MIR (`crux-mir`) through the `Crucible` SSA symbolic simulator, merging paths
  into shared And-Inverter Graphs (AIGs) / `What4` terms and discharging
  equivalence against Cryptol specifications via ABC, Yices, or Z3 (used to
  verify `AWS-LC` / `s2n-bignum`).
- **`Kani` (`model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`):**
  Compiles Rust MIR into CBMC `GOTO` programs (`codegen_cprover_gotoc`) with
  shadow-memory object tables tracking pointer allocation validity and byte
  initialization, unrolling loops to a bound $k$ (or using `#[kani::loop_invariant]`)
  and bit-blasting to Kissat/CaDiCaL.
- **`Rosette` (`emina/rosette@373c8c35e4a7667f38fce10cf0b74ae17de07f1d`, Torlak
  & Bodik, PLDI 2014, DOI `10.1145/2594291.2594340`) and `Serval`
  (`uw-unsat/serval@72adc4952a1e62330aea527214a26bd0c09cbd05`, Nelson et al.,
  SOSP 2019, DOI `10.1145/3341301.3359641`):** `Rosette` lifts a host language
  interpreter into a symbolic evaluator by merging symbolic states at control
  joins (`ite` value merging) rather than forking paths. `Serval` applies
  `Rosette` to verify RISC-V (`CertiKOS`/`Komodo`) and x86-32 (`cks`) monitors by
  requiring finite state-machine structures without unbounded loops.
- **`Sail` (`rems-project/sail@0f51056900af85d0b18928d6ea2d2271d18184e8`),
  `Islaris` (`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`,
  Sammler et al., PLDI 2022, DOI `10.1145/3519939.3523434`), and `HolBA`
  (`kth-step/HolBA@ef22c1fd8da612c57f2e7f273cb14594a7e529d3`):** `Islaris` uses
  the `Isla` symbolic evaluator over authoritative `Sail` Armv8-A/Morello/RISC-V
  specifications to emit simplified per-instruction symbolic traces that are
  verified foundationally inside Rocq/Iris (`Lithium`). `HolBA` lifts Armv8/RISC-V
  machine code to the `BIR` intermediate representation in HOL4 with
  proof-producing bitvector steps.
- **`Lean 4 bv_decide` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
  v4.34.1, `src/Lean/Elab/Tactic/BVDecide/`, Böving et al., CAV 2025):**
  Normalizes Lean `BitVec w` goals by rewrite lemmas, bit-blasts to a verified
  AIG (`Std.Sat.AIG`), invokes an external CDCL SAT solver (`CaDiCaL`) to
  produce an `LRAT` unsatisfiability certificate, and checks the `LRAT`
  certificate inside Lean's kernel via computational reflection (`decide` /
  `ofReduceBool`).

##### Design philosophy, architectural tradeoffs, and TCB comparisons

`SAW`/`crux-mir`, `Kani`, and `Serval` achieve push-button automation on
fixed-bound bitvector code, but their symbolic execution engines (`Crucible`,
`CBMC`, `Rosette`) and external solvers (`Z3`, `Yices`, `CaDiCaL`) sit entirely
inside their TCB. Conversely, `Islaris` and `Lean 4 bv_decide` decouple search
from checking: `Islaris` re-checks `Isla`'s symbolic traces in Rocq/Iris, and
`bv_decide` checks `CaDiCaL`'s `LRAT` proof inside the Lean 4 kernel (note that
in Anneal, `TrustedBoundary.lean` forbids `native_decide`, so `bv_decide` must
use kernel Whnf reduction `decide` as characterized in
`lean4-core-tactics-kernel-bvdecide-stddo-and-containers-2026`).

##### Exact mapping onto Anneal's four `trusted/` primitives

A verified symbolic evaluator `symEval : Fuel → SymState → SymResult` in
`theory/` steps `L_mir` symbolically and emits each path's UB checks (shift
width $< w$, division by non-zero, aligned pointer access, in-bounds slice
indexing) and postcondition clauses as fine-grained `Obligation` entries in
`VerificationResult`:

- Each `Obligation` has `prop : Prop` expressed as a closed `BitVec` formula
  discharged by kernel-checked `LRAT` (`bv_decide` without `native_decide`).
- A once-and-for-all theorem `symEval_sound` in `theory/` proves that
  `AllHold (obligations.map (·.prop))` implies
  `L_mir.sem f ≤ L_mir.SpecOn pre post ∧ L_mir.ProductiveOn pre f`.

Basis: **source** — `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
`GaloisInc/crucible@7f49dac06c656f7b92c8b6cc054f47c63b60abe4`,
`model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`,
`emina/rosette@373c8c35e4a7667f38fce10cf0b74ae17de07f1d`,
`uw-unsat/serval@72adc4952a1e62330aea527214a26bd0c09cbd05`,
`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`, and
`lean4-core-tactics-kernel-bvdecide-stddo-and-containers-2026`;
**derived** — `VerificationResult` decomposition of symbolic path obligations.

---

### 3. Category B: Separation logics and spatial resource engines (`UC-2.1`–`UC-2.4`)

#### 3.1 `UC-2.1`: Higher-order concurrent separation logics (`Iris`/`MoSeL`, `iris-lean`, `RustBelt`, `RefinedC`/`Caesium`, `RefinedRust`, `VST`)

##### Goals, problem domain, and target users

Unsafe Rust standard-library abstractions (`Arc<T>`, `Mutex<T>`, `RwLock<T>`,
`Cell<T>`, `RefCell<T>`, `OnceLock<T>`, futures, intrusive linked lists) and C
systems components violate tree-shaped borrow discipline intentionally: they
use raw pointers, `UnsafeCell` interior mutability, atomic CAS loops, and custom
ownership-sharing protocols. Higher-order separation logics provide a
foundational proof theory inside an interactive theorem prover (Rocq or Lean 4)
to verify that these unsafe primitives satisfy safe public API contracts.

##### Development history, lineage, and evolution

- **`VST` (`PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e`,
  Appel et al., 2014):** Verified Software Toolchain for CompCert `Clight` in
  Rocq, constructing step-indexed separation algebras (`msl/`) and tactic
  automation (`forward`, `entailer!`) directly over CompCert's operational
  semantics so proofs compose end-to-end with CompCert's verified assembly
  backend.
- **`Iris` and `MoSeL` (`rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088`,
  Jung et al., JFP 2018, DOI `10.1017/S0956796818000151`; Krebbers et al., ICFP
  2018, DOI `10.1145/3236772`) and `iris-lean`
  (`leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`):**
  Unifies step-indexed higher-order ghost state into a single algebraic
  primitive—partial Commutative Monoids with Frame-Preserving Updates (**CMRAs /
  Cameras**)—combined with impredicative invariants ($\boxed{P}^{\mathcal{N}}$)
  and the tactical proof mode (`MoSeL` / `IPM`, ported to Lean 4 in `iris-lean`
  via `BI` interface classes and custom spatial context metaprogramming).
- **`RustBelt` (`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
  Jung et al., POPL 2018, DOI `10.1145/3158154`; Dang et al., POPL 2020, DOI
  `10.1145/3371102`):** Built the **Lifetime Logic** on top of Iris to give a
  semantic model of Rust's type system over $\lambda_{\text{Rust}}$, defining
  mutable and shared borrows via temporal lifetime tokens (`[κ]_q`) and semantic
  type interpretations $\llbracket \tau \rrbracket(\text{tid}, \vec{v})$ to
  prove soundness of `Send`, `Sync`, `Arc`, `Mutex`, `RefCell`, and `Cell`.
- **`RefinedC` and `Caesium`
  (`iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`, Sammler et al.,
  PLDI 2021, DOI `10.1145/3453483.3454036`) and `RefinedRust`
  (`lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`, Gäher et
  al., PLDI 2024, DOI `10.1145/3656423`):** Automate foundational Iris proofs by
  introducing **refinement ownership types** (`r @ ty`) checked by the
  goal-directed **Lithium** separation-logic interpreter (`theories/lithium/`).
  In `RefinedC`, Lithium checks C code over the `Caesium` operational C
  semantics; in `RefinedRust`, the `radium` rustc frontend extracts MIR into
  Rocq, and Lithium automates both safe borrow checking (subsuming prophetic
  functional updates) and unsafe raw-pointer reasoning in a single Iris type
  system.

##### Design philosophy, architectural tradeoffs, and formal theory

Foundational separation logics (`Iris`, `VST`, `RefinedC`, `RefinedRust`) have a
**minimal TCB**: the separation logic itself (`iProp Σ`, cameras, lifetime
tokens, Lithium's goal-directed proof search) is 100% untrusted by the kernel
because an **Adequacy Theorem** erases the logic down to a statement about the
underlying operational semantics (`Caesium`, $\lambda_{\text{Rust}}$, or
`CompCert Clight`). The primary tradeoff is interactive proof latency when
Lithium's syntax-directed subsumption rules hit non-deterministic spatial
quantifier instantiations.

##### Exact mapping onto Anneal's four `trusted/` primitives

Anneal's `trusted/lean/` boundary is designed so that **`iris-lean` and all
spatial/camera machinery live 100% in `theory/`**:

1. **Step-Indexed Adequacy via `EventualBehaviorOf`:**
   In Iris, the weakest precondition `wp ⊤ f_mir Φ` proves by induction on step
   index $n : \mathbb{N}$ that every $n$-step execution prefix of
   `SmallStepMachine` is safe (never reaches `.failed .ub` or `.stuck`) and
   satisfies $\Phi$ upon `.terminated`. Because `EventualBehaviorOf` defines
   `(L_mir.sem f_mir q).defined` as universal safety over all finite reachable
   prefixes (`∀ n tr out, ReachesPrefix ... → out.isSafe`) while mapping
   infinite execution to `.diverges : EventualOut Obs Val` (which is a
   *defined* outcome inside `val`), the Iris Adequacy Theorem (`iris_adequacy`)
   in `theory/` directly discharges:
   $$(\vdash \text{wp}\;\top\;f_{\text{mir}}\;\Phi) \implies L_{\text{mir}}.\text{sem}\,f_{\text{mir}} \le L_{\text{mir}}.\text{SpecOn}\,\text{pre}\,\Phi \;\wedge\; L_{\text{mir}}.\text{ProductiveOn}\,\text{pre}\,f_{\text{mir}}$$
   (given `TotalStep` / `InhabitedDemonic` for `L_mir`).
2. **No Separation Logic in `trusted/lean/`:** Neither `CMRA`, `iProp`, nor
   step-indices appear in `Trusted/Refinement.lean` or `Trusted/StepResult.lean`.

Basis: **source** — `rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088`,
`leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`,
`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
`iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`,
`lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`,
`PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e`, and
`lean4-separation-logics-iris-lean-iprop-and-choicekind-adequacy-2026`;
**derived** — adequacy bridge to `EventualBehaviorOf`.

---

#### 3.2 `UC-2.2`: Automated symbolic-heap frame-inference engines (`CN`/`Fulminate`, `VeriFast`, `Viper`/`Prusti`, `Gillian`/`Gillian-Rust`, `Smallfoot`/`Infer`/`Pulse`)

##### Goals, problem domain, and target users

Systems programmers writing OS kernels (`pKVM`), allocators, and C/Rust data
structures often want fast, predictable separation-logic verification without
interactive Rocq/Lean proof scripts. Automated symbolic-heap engines restrict
assertions to the **Symbolic Heap (`SymHeap`)** fragment—a pair $(\Pi \mid
\Sigma)$ of a pure first-order constraint $\Pi$ and a spatial conjunction
$\Sigma = p_1 \mapsto v_1 * \dots * p_k \mapsto v_k * P_1(\vec{x}_1) * \dots$—where
frame inference (subtracting a callee's precondition footprint from the caller's
heap) is decidable or syntax-directed.

##### Development history, lineage, and evolution

- **`Smallfoot` (Berdine, Calcagno, O'Hearn, FMCO 2005) and `Infer` / `Pulse`
  (`facebook/infer@5aac32c06952a2f3a6b7043e91457920f065833b`, Calcagno et al.
  JACM 2011; Le et al. 2022):** `Smallfoot` introduced decidable symbolic
  execution and frame inference over symbolic heaps with hard-coded linked-list
  and tree predicates. `Infer` added **bi-abduction** ($H * \text{?anti-frame}
  \vdash P * \text{?frame}$) to synthesize procedure summaries bottom-up without
  user annotations; `Pulse` reformulated bi-abduction as an incorrectness/under-approximate
  separation logic engine for C++, Java, and Rust MIR.
- **`VeriFast` (`verifast/verifast@0a83dba42db7ce0b445034ece5298afe980e57dc`,
  Jacobs et al., NFM 2011; Foundational VeriFast, Jacobs et al., 2026,
  `arXiv:2601.13727v1`):** Achieves sub-second symbolic execution of C, Java,
  and Rust by requiring explicit ghost statements (`open`, `close`, lemma
  function calls) whenever inductive predicates are folded/unfolded, avoiding
  backtracking search. In 2026, *Foundational VeriFast* added **hinted
  mirroring**, emitting execution hints from `VeriFast` that are replayed inside
  Rocq against an axiomatic semantics to produce a kernel-checked proof.
- **`Viper` (`viperproject/silver@da1c8993b66feb39976e3609e2580a4661137a0f`,
  Müller et al., VMCAI 2016) and `Prusti`
  (`prusti/prusti@0d4a8d497ac1e540d48ef50a031d53b4e3ae36e2`, Astrauskas et al.,
  OOPSLA 2019, DOI `10.1145/3360573`):** `Viper` is an intermediate verification
  language based on **Implicit Dynamic Frames (IDF)** (`acc(x.f, p)`), with two
  backends: `Silicon` (symbolic execution) and `Carbon` (verification-condition
  generation via Boogie/Z3). `Prusti` lowers safe Rust MIR borrow checking into
  Viper permissions using *magic wands* (`P --* Q`) to represent expiring
  mutable borrows (pledges).
- **`CN` and `Fulminate`
  (`rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`, Pulte et
  al., POPL 2023, DOI `10.1145/3571194`; Banerjee et al., POPL 2025, DOI
  `10.1145/3704879`):** `CN` builds a decidable refinement-type and separation-logic
  system over `Cerberus` `Core` IR for C (`pKVM` hypervisor buddy allocator),
  restricting resource predicates to syntax-directed guarded conditionals so SMT
  queries remain strictly quantifier-free. `Fulminate` compiles `CN` separation-logic
  specifications into executable C runtime-testing ownership shadow checks.
- **`Gillian` and `Gillian-Rust`
  (`GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`,
  Ayoun et al., PLDI 2025, DOI `10.1145/3729289`):** Parametric compositional
  symbolic execution platform in OCaml. `Gillian-Rust` uses a **hybrid memory
  model** combining fast tree-structured algebraic state for safe Rust places
  with a byte-level flat memory block fallback when pointers are cast to raw
  byte offsets, plus prophecy servers for mutable borrows.

##### Design philosophy, architectural tradeoffs, and TCB comparisons

Standalone `Viper`/`Prusti`, `CN`, and `Gillian-Rust` achieve high automation by
keeping the symbolic heap engine and Z3/cvc5 inside the TCB. *Foundational
VeriFast* (`arXiv:2601.13727v1`) and *Boogie/Viper Certificate Generation*
(Parthasarathy et al., CAV 2021, DOI `10.1007/978-3-030-81688-9_33`; OOPSLA 2024)
demonstrate that an automated symbolic-heap or IDF verifier can emit a compact
**fold/unfold and frame-matching witness certificate** (`SymHeapCert`) that a
simple kernel-verified checker replays without search.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal's `theory/`, a verified boolean certificate checker
`checkSymHeapCert : MirBody → SymHeapSpec → SymHeapCert → Bool` interprets a
`SymHeap` as a predicate `interpSH : SymHeap → MirState → Prop` over disjoint
sub-heaps (`Heaplet.Disjoint h_active h_frame`) and checks explicit predicate
`open`/`close` hints and frame-matching permutations at each MIR basic block:

1. **Soundness via `L_mir.SpecOn` and `ProductiveOn`:**
   `checkSymHeapCert_sound` proves that when `checkSymHeapCert body spec cert = true`
   and the pure side conditions (`VerificationResult` obligations) hold,
   `L_mir.sem body ≤ L_mir.SpecOn spec.pre spec.post ∧ L_mir.ProductiveOn spec.pre body`.
2. **Framing Across `StepResult.externalCall`:**
   When a function holds a spatial frame $R$ disjoint from the arguments passed
   to an external call (`StepResult.externalCall boundaryInv branches`), the
   external call's `branches : MirState → Prop` transition relation in `L_mir`
   must preserve all unescaped/unexposed heap allocations in $R$. This surfaces
   a concrete requirement on `L_mir`: `StepResult.externalCall` branches must
   constrain modifications to allocations reachable from exposed provenance or
   passed arguments.

Basis: **source** — `rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`,
`verifast/verifast@0a83dba42db7ce0b445034ece5298afe980e57dc`,
`viperproject/silver@da1c8993b66feb39976e3609e2580a4661137a0f`,
`prusti/prusti@0d4a8d497ac1e540d48ef50a031d53b4e3ae36e2`,
`GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`, and
`facebook/infer@5aac32c06952a2f3a6b7043e91457920f065833b`;
**derived** — certifying `SymHeapCert` checker and `externalCall` frame condition.

---

#### 3.3 `UC-2.3`: Fractional and counting permission verifiers (`VerCors`, `Steel`/`Pulse` in F\*, Boyland fractional permissions)

##### Goals, problem domain, and target users

Rust code routinely splits mutable slices into disjoint sub-slices
(`slice::split_at_mut`), shares immutable buffers across concurrent readers
(`Arc<[u8]>`, `RwLockReadGuard<T>`, zero-copy network views), and recombines
exclusive write access once all readers finish. Boyland's **fractional
permissions** $q \in (0, 1]_{\mathbb{Q}}$ (where $q = 1$ grants read/write access
and $0 < q < 1$ grants read-only shared access, with $p_1 \stackrel{q_1}{\mapsto} v *
p_1 \stackrel{q_2}{\mapsto} v \iff p_1 \stackrel{q_1 + q_2}{\mapsto} v$) and
Bornat's **counting permissions** model shared read/write recombines cleanly.

##### Development history, lineage, and evolution

- **`VerCors` (`utwente-fmt/vercors@3300d5b007286225a33c17a233bda77db9471213`,
  Blom & Huisman, FM 2014):** Verifies concurrent Java, C, OpenCL, and Halide
  programs by lowering fractional-permission annotations (`Perm(loc, q)`) and
  fork/join barriers into Viper.
- **`Steel` and `Pulse` in F\*
  (`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`, Fromherz et al.,
  ICFP 2021):** Embeds a concurrent separation logic DSL (`Pulse`) inside
  dependent type theory (F\*) where `pts_to r #p v` carries a fractional
  permission `#p : perm` manipulated by an automated AC-matching frame solver
  that discharges linear rational arithmetic (`p == p1 +. p2`) via Z3.

##### Exact mapping onto Anneal's four `trusted/` primitives

Modeling fractional permissions as an abstract machine `L_frac` over `L_mir`
directly tests the **`BehaviorCodec` query-retraction law**
(`decodeQuery (encodeQuery q₁) = q₁`):

- In `L_frac`, each state pairs `MirState` with a ghost permission map
  `perm : Addr → Rat` where loads require `perm a > 0`, stores require
  `perm a = 1`, and ghost split/merge steps conserve $\sum \text{perm}(a) \le 1$.
- Because `L_frac` fails *more often* than `L_mir` (a store with $0 < \text{perm}(a)
  < 1$ triggers `.failed .ub` in `L_frac` even when allocated in `L_mir`),
  `L_mir` refines `L_frac` (`Abstracts L_frac L_mir`).
- However, if `L_frac.Query` were `MirState × (Addr → Rat)` while `L_mir.Query =
  MirState`, no `encodeQuery : MirState × (Addr → Rat) → MirState` could have a
  left inverse `decodeQuery`! To satisfy `decodeQuery (encodeQuery q₁) = q₁`,
  `L_frac` sets `L_frac.Query := MirState` and initializes the initial
  permission map deterministically inside `L_frac.sem` from the function's entry
  footprint `initPerm : MirState → (Addr → Rat)` (using `BehaviorCodec.id`), or
  equivalently proves the permission invariant in `theory/` via `Compiles L_mir L_frac`.

Basis: **source** — `utwente-fmt/vercors@3300d5b007286225a33c17a233bda77db9471213`,
`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`, and
`Trusted/Refinement.lean:380-385`; **derived** — deterministic ghost-state
initialization pattern for `BehaviorCodec`.

---

#### 3.4 `UC-2.4`: Branded interior mutability and linear ghost permissions (`GhostCell`/`qcell`, `Verus` `Tracked<PointsTo<T>>` and `PCell`)

##### Goals, problem domain, and target users

Cyclic graphs, intrusive doubly-linked lists, B+trees with sibling pointers,
and slab allocators cannot be written in safe Rust without runtime reference
counting (`Rc<RefCell<T>>`) unless the *data location* (`UnsafeCell<T>`) is
decoupled from the *linear permission token* granting access to it.

##### Development history, lineage, and evolution

- **`GhostCell` (`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
  Yanovski, Dang, Jung, Dreyer, ICFP 2021, DOI `10.1145/3473597`) and `qcell`
  (`jbowers/qcell`, `LCell`):** Uses Hindley-Milner rank-2 polymorphic lifetime
  branding (`GhostToken::new(|mut token: GhostToken<'brand>| ...)`):
  `&'a GhostCell<'brand, T>` can be freely aliased, while borrowing `&'a
  GhostToken<'brand>` yields `&'a T` and borrowing `&'a mut GhostToken<'brand>`
  yields `&'a mut T` at zero runtime cost (`GhostToken<'brand>` is a zero-sized
  type, ZST).
- **`Verus` (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`,
  Lattuada et al., OOPSLA 2023, DOI `10.1145/3586037`; SOSP 2024):** Replaces
  separation logic's spatial conjunction (`*`) with **first-class linear ghost
  types** checked by `rustc`'s own borrow checker across three modes: `exec`
  (compiled code), `tracked` (linear ghost permissions erased at compile time),
  and `spec` (duplicable mathematical specifications). A `PCell<T>` (`exec`) is
  paired with `Tracked<PointsTo<T>>` (`tracked`), so standard SMT (`Z3` via
  `VIR` $\to$ `AIR`) verifies pointer graphs without spatial frame inference!

##### Exact mapping onto Anneal's four `trusted/` primitives

In `Runtime(PostCleanup)` MIR, both `GhostToken<'brand>` and Verus's
`Tracked<PointsTo<T>>` are erased (or compiled to 0-byte ZST locals), and
`'brand` lifetimes do not exist at runtime. In Anneal:

- `anneal-rustc-capture` extracts pre-erasure `'brand` / ghost-type annotations
  as untrusted side-table metadata into `theory/`.
- `theory/` defines a pure arena language `L_arena` where the ZST token is
  reified as a pure finite map `Arena : AllocId → Val`, and proves
  `Abstracts L_arena L_mir codec f_arena f_mir` + `L_arena.ProductiveOn pre f_arena`
  directly over the lifetime-erased `L_mir` operational semantics.

Basis: **source** — `verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`
and GhostCell ICFP 2021 DOI `10.1145/3473597`; **derived** — ZST/lifetime
reification via `Abstracts L_arena L_mir`.

---

### 4. Category C: Aliasing and borrow models (`UC-3.1`–`UC-3.4`)

#### 4.1 `UC-3.1`: Operational borrow shadow-state machines (`Miri`, `Stacked Borrows`, `Tree Borrows`, `BorrowSanitizer`)

##### Goals, problem domain, and target users

Because `rustc` emits LLVM `noalias`, `readonly`, and `dereferenceable`
attributes on reference parameters (`&T`, `&mut T`), unsafe Rust code that mixes
references and raw pointers (`*const T`, `*mut T`) must obey a dynamic aliasing
state machine or risk miscompilation. Operational borrow models define that
exact state machine so interpreters (`Miri`), sanitizers (`BorrowSanitizer`),
and deductive verifiers (`Anneal`) can detect aliasing UB.

##### Development history, lineage, and evolution

- **`Stacked Borrows` (Jung, Dang, Kang, Dreyer, POPL 2020, DOI
  `10.1145/3371109`) and `Miri`
  (`rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`):** Maintains a
  per-byte stack of borrow tags (`Unique(t)`, `SharedReadWrite(t)`,
  `SharedReadOnly(t)`, `Disabled`) in shadow memory. Any access through tag $t$
  pops (or disables) all tags above $t$ on the stack. While sound for basic
  `noalias`, Stacked Borrows eagerly performs a logical read on every `Retag` and
  forbids common two-phase borrow and `container_of!` raw-pointer patterns.
- **`Tree Borrows` (Villani, Hostert, Dreyer, Jung, PLDI 2025, DOI
  `10.1145/3735592`; `rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`):**
  Replaces the per-byte stack with a **per-allocation borrow tree** where each
  node carries a 4-state permission automaton (`Reserved` $\to$ `Active` $\to$
  `Frozen` $\to$ `Disabled`) classified by relative tree position (`Child` vs.
  `Foreign` access). Lazy initialization (`Reserved` tolerating foreign reads
  until the first child write transitions to `Active`) validates two-phase
  borrows and out-of-bounds pointer arithmetic natively. Function-entry
  `RetagKind::FnEntry` attaches a **`Protector`** tied to the active call frame
  `CallId`, making it immediate UB for a protected tag to lose its permission
  before the function returns.
- **`BorrowSanitizer` (`BorrowSanitizer/bsan@a2fd46ab89fc97ba1cf548645dd70acbeaa17d64`):**
  Compiles Tree Borrows shadow-tree tracking directly into LLVM IR
  instrumentation passes, allowing native-speed fuzzing and cross-language
  Rust/C/C++ FFI aliasing checks that `Miri` cannot execute without source.

##### Exact mapping onto Anneal's four `trusted/` primitives

Tree Borrows interacts with Anneal's `trusted/` primitives in three ways:

1. **Tag-Erasure Abstraction (`Abstracts L_untagged L_mir_tb codec f f`):**
   Once a static borrow analysis (`UC-3.2`) or separation-logic proof (`UC-2.1`)
   establishes that a function never triggers a Tree Borrows transition to
   `Disabled` on an accessed or protected tag, `Abstracts L_untagged L_mir_tb`
   erases the `BorrowTree` shadow state so downstream functional proofs in
   `theory/` reason over plain untagged memory `(AllocId, Offset)`.
2. **Cross-Model Refinement (`Compiles L_sb L_tb codec f f`):**
   On the eager-retag fragment without lazy `Reserved` writes, Stacked Borrows
   is stricter than Tree Borrows (more states transition to `.failed .ub`),
   expressed horizontally as `L_tb.sem f ≤ codec.toMorphism (L_sb.sem f)`.
3. **Function-Entry Protectors Across `StepResult.externalCall`:**
   Because a Tree Borrows `Protector` on a reference argument requires the tag
   to remain valid until the enclosing call frame exits, an external callback
   invoked via `StepResult.externalCall boundaryInv branches` must not clobber a
   protected location of an active caller frame—requiring `MirState` in
   `trusted/` to track active `CallFrameId`s and `externalCall` to enforce
   protector survival.

Basis: **source** — `rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`,
Tree Borrows PLDI 2025 DOI `10.1145/3735592`, Stacked Borrows POPL 2020 DOI
`10.1145/3371109`, `BorrowSanitizer/bsan@a2fd46ab89fc97ba1cf548645dd70acbeaa17d64`,
and `anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026`;
**derived** — `Abstracts` tag-erasure theorem and `externalCall` protector
invariant.

---

#### 4.2 `UC-3.2`: Static borrow-checker and loan-reachability models (`Polonius`, `Oxide`/`Patina`, `Aquascope`)

##### Goals, problem domain, and target users

Static borrow models formalize `rustc`'s compile-time borrow checker (`NLL` and
`Polonius`) so that safe Rust programs can be proved free of aliasing violations
statically without per-instruction runtime borrow-tree proofs.

##### Development history, lineage, and evolution

- **`Patina` (Reed, Univ. Washington Tech Report `UW-CSE-15-03-02`, 2015) and
  `Oxide` (Weiss et al., `arXiv:1903.00982v4`, 2019/2021):** Syntactic type
  systems for surface/HIR Rust where lifetimes are modeled directly as concrete
  provenance sets of loans (`{ℓ₁, …, ℓₖ}`) ordered by path prefixes (`x.f`).
- **`Polonius` (`rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df`)
  and `Aquascope`
  (`cognitive-engineering-lab/aquascope@f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`,
  Crichton et al., CHI 2023):** `Polonius` reformulates `rustc`'s borrow checker
  as a Datalog Horn-clause fixpoint over base facts (`loan_issued_at(O, L, P)`,
  `loan_invalidated_at(P, L)`, `loan_killed_at(L, P)`, `subset_base(O1, O2, P)`,
  `cfg_edge(P1, P2)`), computing transitive origin inclusion `subset(O1, O2, P)`
  and `origin_contains_loan_at(O, L, P)` to check that
  `loan_invalidated_at(P, L) ⋈ origin_contains_loan_at(O, L, P) ⋈ origin_live_on_entry(O, P)`
  is empty. `Aquascope` extracts and visualizes these Polonius loan permissions
  (`R`/`W`/`O`) across MIR points.

##### Exact mapping onto Anneal's four `trusted/` primitives

Instead of trusting `rustc`'s borrow checker or computing a slow Datalog
transitive closure inside Lean's kernel, `anneal-rustc-capture` (or an external
solver) emits the pre-computed relation tables `PoloniusCert`, and a verified
boolean checker `checkPolonius : PoloniusInput → PoloniusCert → Bool` in
`theory/` checks in $O(|E| \cdot |\text{Origins}|^2)$ time via `decide` that
`PoloniusCert` contains all base facts, is closed under each Polonius Horn
clause, and has an empty error relation—discharging the aliasing obligations in
`VerificationResult` needed by `UC-3.1` and `UC-1.1`.

Basis: **source** — `rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df`,
`cognitive-engineering-lab/aquascope@f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`,
and Oxide `arXiv:1903.00982v4`; **derived** — certifying Datalog post-fixpoint
checker in `theory/`.

---

#### 4.3 `UC-3.3`: Pointer-integer casts, strict/exposed provenance, and hardware capabilities (`Strict/Exposed Provenance`, `VIP`, `CompCertS`/`Quasi-Concrete`, `CHERI`/`Morello`)

##### Goals, problem domain, and target users

Lock-free data structures, radix trees, NaN-boxed runtimes, and page-table
descriptors pack metadata bits into the low alignment bits of pointers (`ptr.map_addr(|a| a | tag)`),
while FFI and serialization code casts pointers to integers (`expose_provenance`
/ `with_exposed_provenance`). Memory models must support pointer-integer
arithmetic without breaking alias analysis of unexposed allocations.

##### Development history, lineage, and evolution

- **`CompCertS` (Besson, Blazy, Wilke, POPL 2014 / JFP 2019) and
  `Quasi-Concrete Memory` (Kang, Hur, Mansky, Garbuzov, Zdancewic, Vafeiadis,
  POPL 2015, DOI `10.1145/2676726.2676985`):** Extend CompCert's block-offset
  memory `(b, ofs)` (`CompCert Memdata`) so that symbolic bitwise expressions on
  pointers are lazily evaluated (`CompCertS`) or logical blocks receive concrete
  base addresses on first integer cast (`Quasi-Concrete`).
- **`VIP` (Virtual Integer-Pointer Model in `RefinedC`, Lepigre et al., PLDI
  2022, DOI `10.1145/3519939.3523702`):** Replaces angelic provenance guessing
  with deterministic `copy_alloc_id(int_addr, orig_ptr)` operations (`with_addr`
  in Rust), enabling automated separation-logic verification of tagged pointers
  in `RefinedC`/Lithium.
- **`Rust Strict & Exposed Provenance` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`,
  `library/core/src/ptr/`, RFC 3559):** Splits pointer-integer operations into
  deterministic **Strict Provenance** (`ptr.addr()`, `ptr.with_addr(a)`,
  `ptr.map_addr(f)`, preserving `AllocId`) and **Exposed Provenance**
  (`ptr.expose_provenance()`, `ptr::with_exposed_provenance(a)`).
- **`CHERI` and `Arm Morello`
  (`CTSRD-CHERI/sail-morello@2305f656ff84619caf50107f49dae7be52aec72b`,
  `rems-project/coq-cheri-capabilities@b39cd73409d8c2a058ba8065f81dc72d3c84fb11`):**
  Enforce provenance in hardware via 129-bit capabilities (64-bit address +
  compressed bounds + permissions + 1-bit hardware validity tag cleared on
  unaligned or out-of-bounds byte writes).

##### Exact mapping onto Anneal's four `trusted/` primitives

1. **Tagged-Pointer Algebraic Lens (`Abstracts L_tagged L_mir codec f_tagged f_mir`):**
   For Strict Provenance (`map_addr`), `L_tagged` models a $2^k$-aligned tagged
   pointer as `ValidPtr T × BitVec k`, and `codec.encodeQuery` packs it into
   `MirVal.ptr allocId (base + offset ||| tag)` with bitvector obligations
   discharged by `bv_decide` in `VerificationResult`.
2. **Demonic vs. Angelic Nondeterminism in `with_exposed_provenance`:**
   In C's `PNVI-ae-udi` (`Cerberus`) and `MiniRust`, `with_exposed_provenance(addr)`
   is specified via **angelic** choice over all previously exposed `AllocId`s.
   In Anneal's `Behavior Query Out := Query → Partial (Out → Prop)`,
   nondeterminism in `StepResult.choice` is **demonic**: refinement `≤` requires
   *every* branch to be UB-free (`defined`). If `L_mir` modeled
   `with_exposed_provenance(addr)` as a demonic choice over all exposed
   `AllocId`s, exposing two allocations would cause one branch to pick the wrong
   `AllocId` and hit `.failed .ub`, falsifying `(L_mir.sem p q).defined`!
   Therefore, `L_mir` in `trusted/` must resolve `with_exposed_provenance(addr)`
   deterministically by selecting the unique live exposed allocation whose
   concrete range $[\text{base}, \text{base}+\text{size})$ contains `addr` (or
   model one-past-the-end ambiguity in `Query`).

Basis: **source** — `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`,
VIP PLDI 2022 DOI `10.1145/3519939.3523702`, Quasi-Concrete POPL 2015 DOI
`10.1145/2676726.2676985`, `CTSRD-CHERI/sail-morello@2305f656ff84619caf50107f49dae7be52aec72b`,
and `Trusted/StepResult.lean:176-187`; **derived** — demonic-vs.-angelic
provenance resolution constraint on `L_mir`.

---

#### 4.4 `UC-3.4`: Normative byte-level memory models (`MiniRust`, `Cerberus`, `CompCert Memdata`)

##### Goals, problem domain, and target users

Normative operational semantics for Rust (`MiniRust`) and C (`Cerberus`,
`CompCert Memdata`) define memory as flat arrays of abstract bytes carrying
initialization and provenance fragments so that low-level idioms (`memcpy`,
union punning, padding bytes, `zerocopy` transmutations) have an unambiguous
ground truth.

##### Development history, lineage, and evolution

- **`CompCert Memdata`
  (`AbsInt/CompCert@f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03`, `common/Memdata.v`,
  Leroy & Blazy, JAR 2008):** Defines `memval := Undef | Byte (b : byte) |
  Fragment (v : val) (q : quantity) (n : nat)`, where a 64-bit pointer stored in
  memory is split into 8 symbolic `Fragment` bytes that read back as `Vundef` if
  partially overwritten.
- **`Cerberus` (`rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`,
  Memarian et al., POPL 2019):** De facto ISO C-2011/C2X operational reference
  model parameterized by memory models (`PNVI-ae-udi`, `VIP`, symbolic),
  translating C into typed functional `Core` IR.
- **`MiniRust` (`minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):**
  Literate `specr` specification of Rust's operational semantics where memory
  stores `AbstractByte := Uninit | Init (data : UInt8) (provenance : Option Prov)`,
  and every typed load/store converts between structured `Value` trees and
  `List AbstractByte` through type layout descriptors (`Tuple`, `Union`, `Int`,
  `Ptr`), enforcing validity invariants (`bool` $\in \{0,1\}$, non-null references,
  initialized non-padding bytes) on every typed load and return.

##### Exact mapping onto Anneal's four `trusted/` primitives

Establishing bilateral behavioral equivalence between a mechanized MiniRust model
`L_minirust` in `theory/` and Anneal's `L_mir` (`Compiles L_minirust L_mir codec p p ∧
Abstracts L_minirust L_mir codec p p`) surfaces the **Padding-Byte Stress Test**
for `BehaviorCodec.encodeOut_of_decodeOut`:

- In `MiniRust`, a struct `#[repr(C)] struct Padded { a: u8, b: u16 }` occupies
  4 bytes where byte offset 1 is padding. Two distinct final memory states $o_2
  \neq o_2'$ (one with byte 1 = `Uninit`, one with byte 1 = `Init 0xFF none`)
  both decode to the same logical struct value `Padded { a, b }`.
- Under `BehaviorCodec`'s partial-bijection law
  `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`, `decodeOut` cannot map both
  $o_2$ and $o_2'$ to `some (Padded { a, b })`!
- Therefore, `L_mir`'s `SmallStepMachine` terminal step (`.terminated term`) must
  project the return value through the return type's layout decoding before
  constructing `EventualOut Obs Val` (stripping unobservable padding bytes and
  dead stack slots at the machine return boundary), so `decodeOut` operates on
  canonicalized return values.

Basis: **source** — `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`,
`rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`,
`AbsInt/CompCert@f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03`, and
`Trusted/Refinement.lean`; **derived** — return-value canonicalization
requirement for `encodeOut_of_decodeOut`.

---

### 5. Category D: Type systems, typestates, and effect checkers (`UC-4.1`–`UC-4.4`)

#### 5.1 `UC-4.1`: Liquid and index-refinement type checkers (`Flux`, `Liquid Haskell`, `Stainless`)

##### Goals, problem domain, and target users

Most runtime panics and unsafe precondition failures in systems Rust (`slice[i]`,
`get_unchecked(i)`, `NonZeroUsize::new_unchecked(x)`, `Vec` capacity bounds,
matrix stride invariants) reduce to linear integer or bitvector predicates over
scalar values and struct fields. Refinement type systems attach logical
predicates $\{v : B \mid p(v)\}$ to base types so subtyping checks reduce to
decidable SMT Horn clauses without user-written loop invariants or proof
scripts.

##### Development history, lineage, and evolution

- **`Liquid Haskell` (`ucsd-progsys/liquidhaskell@c0cca0b9f92d8cdaae7f8fc604f78c32b534b69d`,
  Vazou, Seidel, Jhala, Vytiniotis, Peyton Jones, ICFP 2014, DOI
  `10.1145/2628136.2628161`):** Combined Rondon, Kawaguchi, and Jhala's Logically
  Qualified Data Types (Liquid Types, predicate abstraction over a finite set of
  qualifiers $\mathbb{Q}$) with GHC Core typing and SMT-backed Refinement
  Reflection (`ple`, Proof by Logical Evaluation).
- **`Stainless` (`EPFL-LARA/stainless@399c34a06df8e88679f0985131e8a59a28ab9b3f`,
  Hamza, Voirol, Kunčak, OOPSLA 2019):** Verifies Scala programs with refinement
  types, `require`/`ensuring` contracts, and termination measures by counterexample-guided
  unfolding of recursive functions (`Inox` solver).
- **`Flux` (`flux-rs/flux@6769bb9cbd1216380f542349494efafafd6104a3`, Lehmann,
  Geller, Vazou, Jhala, PLDI 2023, DOI `10.1145/3591283`):** Adapts Liquid Types
  to Rust MIR by separating pure mathematical **indices** (`int`, `bool`) from
  Rust's mutable locations: `i32[n]` denotes a 32-bit integer equal to index $n$,
  `&strg T` denotes a strong reference whose target index may change across a
  mutation (`fn incr(x: &strg i32[@n]) ensures x: i32[n + 1]`), and existential
  refinements `{v. i32[v] | v > 0}` are inferred at loop headers via
  `liquid-fixpoint` Horn-clause solving.

##### Design philosophy, architectural tradeoffs, and TCB comparisons

`Flux`, `Liquid Haskell`, and `Stainless` keep the refinement typechecker,
Horn-clause generator, and `Z3`/`cvc5` inside their TCB. A critical hazard in
refinement type systems is **precondition inconsistency**: if a function's input
refinement environment $\Gamma$ is unsatisfiable (e.g., `fn bad(x: usize{x > 10
&& x < 5})` or contradictory assumed Refinement Reflection axioms), every
subtyping Horn clause $\llbracket \Gamma \rrbracket \wedge \phi_1 \Rightarrow
\phi_2$ becomes vacuously valid (`False → φ₂`), allowing the function to pass
`unsafe { unreachable_unchecked() }`.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal's `theory/`, `Flux` is realized as a **certifying refinement
typechecker** `checkFluxTypes : MirBody → FluxSig → FluxCert → List Obligation`:

1. **Certifying Horn-Solution Checking (Zero `liquid-fixpoint` in TCB):**
   `Flux` runs outside Lean to infer loop-header refinement environments
   $\Gamma_{\text{bb}}$ and emits them as `FluxCert`. `checkFluxTypes` in
   `theory/` generates one `Obligation` in `VerificationResult` per subtyping
   check $\Gamma \vdash \{v : T \mid \phi_1\} <: \{v : T \mid \phi_2\}$,
   discharged by Lean's `omega` or `bv_decide`.
2. **Blocking Contradictory Refinement Preconditions via `InhabitedPre`:**
   Anneal's mandatory `InhabitedPre pre_flux` (`∃ q, pre_flux q`) in
   `trusted/lean/` forces every function's entry refinement environment to be
   inhabited (or explicitly waived if the input type is `Infallible`),
   preventing inconsistent refinement preconditions from manufacturing vacuous
   UB proofs.
3. **Granular Waivers via `VerificationResult`:**
   If a single nonlinear subtyping obligation `ob_k` in a function is not yet
   proved, `VerificationResult policy waived obligations` allows waiving `ob_k.id`
   without losing verification of all remaining bounds checks in that function.

Basis: **source** — `flux-rs/flux@6769bb9cbd1216380f542349494efafafd6104a3`,
`ucsd-progsys/liquidhaskell@c0cca0b9f92d8cdaae7f8fc604f78c32b534b69d`,
`EPFL-LARA/stainless@399c34a06df8e88679f0985131e8a59a28ab9b3f`, and
`Trusted/Refinement.lean`; **derived** — `InhabitedPre` non-vacuity guard and
per-subtyping `VerificationResult` obligations.

---

#### 5.2 `UC-4.2`: Typestates and protocol state-machine verifiers (`embedded-hal`/`embassy`, `Verus tokenized_state_machine!`)

##### Goals, problem domain, and target users

Device drivers, DMA controllers, MMIO peripheral configurations, and
cryptographic state machines must obey temporal transition protocols (e.g., a
DMA buffer must transition `Allocated → Pinned → Submitted → Completed →
Unpinned` and must never be mutated or dropped by the CPU while `Submitted` to
hardware).

##### Development history, lineage, and evolution

- **`embedded-hal` (`rust-embedded/embedded-hal@41f29f6bfced1cae0cbe712ba96ee32c075b3125`)
  and `embassy` (`embassy-rs/embassy@14cf6a68ec0bfd0ecf873f7e3dbb2eb69013fa29`):**
  Encode hardware peripheral typestates in safe Rust using phantom type
  parameters (`GpioPin<Input<PullUp>>` consumed by value in `into_push_pull_output(self) -> GpioPin<Output<PushPull>>`).
  While zero-cost, Rust's affine type system alone cannot verify the `unsafe`
  MMIO register writes inside the transition methods or prevent `mem::forget`
  of an in-flight DMA transfer guard.
- **`Verus tokenized_state_machine!`
  (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`,
  `source/state_machines_macros/`):** Compiles a declarative protocol state
  machine (with sharded field strategies `variable`, `map`, `multiset`,
  `storage_option`) into linear `tracked` token types and exchange lemmas,
  proving that local token transitions correspond to valid global state-machine
  steps.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal, a driver or protocol implementation `f_mir` is verified via
`Abstracts L_automaton L_mir codec auto_prog f_mir` using
`StepResult.externalCall boundaryInv branches` at every `read_volatile` /
`write_volatile` / DMA submission boundary:

- **Enforcing Safety on Diverging Reactive Loops without Coinductive Streams:**
  In `Trusted/StepResult.lean`, `EventualOut.terminated (trace : List Obs) term`
  carries `trace : List Obs`, whereas `EventualOut.diverges` carries no trace
  payload. How does Anneal verify that a non-terminating interrupt/polling loop
  (`loop { poll_mmio(); }`) never violates the DMA/MMIO typestate automaton?
- Because every MMIO/DMA call executes `StepResult.externalCall boundaryInv branches`
  where `boundaryInv : Bool` checks that the current typestate permits the
  hardware operation, any protocol violation at finite step $k$ immediately
  transitions to `.failed .ub`—falsifying `(L_mir.sem f_mir q).defined`! Thus,
  `StepResult.externalCall`'s `boundaryInv` enforces safety properties of
  infinite reactive traces online at every step without needing coinductive
  streams in `EventualOut.diverges`.

Basis: **source** — `rust-embedded/embedded-hal@41f29f6bfced1cae0cbe712ba96ee32c075b3125`,
`embassy-rs/embassy@14cf6a68ec0bfd0ecf873f7e3dbb2eb69013fa29`,
`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`, and
`Trusted/StepResult.lean`; **derived** — `boundaryInv` trace-safety enforcement
on `.diverges` loops.

---

#### 5.3 `UC-4.3`: Strict linear, must-consume, and unwind drop-obligation verifiers (`Austral`, `Vale`)

##### Goals, problem domain, and target users

Rust's ownership system is **affine**, not **linear**: `core::mem::forget(x)`,
`ManuallyDrop::new(x)`, `Rc` cycles, or early panic unwinding while a container
is temporarily disassembled (`Vec::drain`, `BTreeMap` node splits, spinlock
guards, DMA in-flight guards) can skip cleanup and leak linear obligations or
leave broken invariants exposed.

##### Development history, lineage, and evolution

- **`Austral` (`austral/austral@0962d2a8a5d77f7daacd7f696819520733f4897d`,
  Borretti, 2022):** A systems language with a strict **linear type system**
  (`Linear` universe distinct from `Free`) where linear values cannot be
  implicitly dropped or forgotten along any control path, and capability-based
  borrowing (`&[R, W]`) is scoped lexically without lifetime inference.
- **`Vale` (`project-everest/vale@bbae0eb89143734363b14a77642dbf8dec36e288`,
  Bond et al., USENIX Security 2017):** Verified Assembly Language for Everest
  (F\* / Dafny), using linear ghost state and register/memory framing to ensure
  cryptographic secrets and stack capabilities are consumed and scrubbed along
  every exit path.

##### Exact mapping onto Anneal's four `trusted/` primitives

In `Runtime(PostCleanup)` MIR, `rustc` has already run drop elaboration,
lowering normal drops and stack-unwinding cleanup ladders into explicit CFG
edges terminating at `Return` (`TerminationKind.normal`) or `UnwindResume` /
`UnwindTerminate` (`TerminationKind.unwind`). A certifying linear dataflow
checker in `theory/` verifies `L_mir.sem f ≤ L_mir.SpecOn pre post_linear` where
`post_linear` inspects `EventualOut.terminated trace term` across **both**
`term = .normal v` and `term = .unwind`, proving that every linear resource
token acquired during execution is consumed before normal return or panic
unwind.

Basis: **source** — `austral/austral@0962d2a8a5d77f7daacd7f696819520733f4897d`,
`project-everest/vale@bbae0eb89143734363b14a77642dbf8dec36e288`, and
`Trusted/StepResult.lean:58-60`; **derived** — dual `.normal`/`.unwind` terminal
inspection in `SpecOn`.

---

#### 5.4 `UC-4.4`: Capability and algebraic effect checkers (`no-panic`, `rtsan`/`cargo-call-stack`, `F*`/`Low*`/`KaRaMeL`, `Koka`/`Effekt`)

##### Goals, problem domain, and target users

Kernel interrupt service routines (ISRs), real-time audio/control threads,
bare-metal firmware, and deterministic consensus/cryptography modules require
transitive effect absence guarantees: `#[no_panic]` (never unwinds or aborts),
`#[no_alloc]` (never calls heap allocator), `#[no_blocking]` (never sleeps),
bounded stack usage, and exact input-to-output determinism.

##### Development history, lineage, and evolution

- **`no-panic` (`dtolnay/no-panic@9a0b1097f77dfd5ee4352b6ff060f68d791730f7`),
  `cargo-call-stack` (`japaric/cargo-call-stack@49080d56b827573f1e19ff127401e312d08f138c`),
  and LLVM `rtsan` (`llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1`,
  `compiler-rt/lib/rtsan`):** `no-panic` inserts a linker symbol call inside a
  drop guard on the unwind path and relies on LLVM `-O2`/`-O3` dead-code
  elimination to delete it—an optimization-dependent heuristic that breaks across
  compiler versions and gives no formal guarantee at the MIR level.
  `cargo-call-stack` analyzes LLVM call graphs and DWARF frame sizes; `rtsan`
  detects real-time violations (`malloc`, `pthread_mutex_lock`) dynamically or
  via clang `[[clang::nonblocking]]` effect attributes.
- **`F*`, `Low*`, and `KaRaMeL`
  (`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`,
  `FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`, Protzenko et
  al., ICFP 2017, DOI `10.1145/3110261`):** `F*` indexes computations by an
  effect lattice (`Tot`, `GTot`, `DIV`, `ST`, `Exn`, `Stack` in `Low*`). `Low*`
  uses the `Stack` effect (`Stack a (requires h0 => ...) (ensures (h0, x, h1) => ...)`)
  to guarantee statically that a function performs zero heap allocations and
  never leaks stack frames, extracting to allocation-free C via `KaRaMeL`.
- **`Koka` (`koka-lang/koka@d23ee7cd73737c1da7a7a5fa837a2806facc3d6b`, Leijen,
  EPTCS 2014, DOI `10.4204/EPTCS.153.8`) and `Effekt`
  (`effekt-lang/effekt@91c540b1067721bdd1bb5d463e42827f8316a1da`, Brachthäuser
  et al., OOPSLA 2020, DOI `10.1145/3428194`):** Track algebraic effects via
  row-polymorphic effect types (`total`, `exn`, `div`, `st<h>`, `io`) or
  lexical capability passing (`Effekt`).

##### Exact mapping onto Anneal's four `trusted/` primitives

Every effect in the `F*`/`Low*`/`Koka` lattice corresponds directly to a subset
specification `L_mir.SpecOn` or `Abstracts` edge in Anneal:

- **`no_panic` (`Exn`-free):** `L_mir.sem f ≤ SpecNoPanic`, where `SpecNoPanic`
  assigns `False` to `EventualOut.terminated _ .unwind`. Unlike `dtolnay/no-panic`,
  this is proved over `L_mir` (and preserved down to assembly via `Compiles`)
  independent of LLVM dead-code heuristics.
- **`no_alloc` / `no_blocking` (`Stack` / capability restriction):**
  `L_mir.sem f ≤ SpecTraceFree isForbiddenEffect`, requiring every event `e ∈
  trace` emitted by `StepResult.externalCall` to satisfy `¬ isForbiddenEffect e`.
- **Exact Determinism (`Tot`):** Proving `Abstracts L_det L_mir codec f_det f_mir`
  (where `L_det` has singleton outcome sets `{f_det q}`) together with
  `L_mir.ProductiveOn pre f_mir` forces every execution of `f_mir` to produce
  the exact singleton outcome `{encodeOut (f_det (decodeQuery q))}`.

Basis: **source** — `dtolnay/no-panic@9a0b1097f77dfd5ee4352b6ff060f68d791730f7`,
`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`,
`FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`,
`koka-lang/koka@d23ee7cd73737c1da7a7a5fa837a2806facc3d6b`,
`effekt-lang/effekt@91c540b1067721bdd1bb5d463e42827f8316a1da`, and
`Trusted/Refinement.lean`; **derived** — effect-lattice mapping onto `SpecOn`
and `ProductiveOn`.

---

### 6. Category E: Sound static analyzers and abstract interpreters (`UC-5.1`–`UC-5.4`)

#### 6.1 `UC-5.1`: Certifying numerical abstract interpreters (`Verasco`, `Astrée`, `Crab`/`SeaHorn`, `IKOS`, `MIRAI`)

##### Goals, problem domain, and target users

Routine arithmetic overflow, division/remainder by zero, and array/slice bounds
checks inside loops can often be discharged automatically without user-written
loop invariants by computing an inductive post-fixpoint in a numerical abstract
domain: **Intervals** ($a \le x \le b$), **Zones / Difference-Bound Matrices**
($x - y \le c$), **Octagons** ($\pm x \pm y \le c$), or **Convex Polyhedra**
($A\vec{x} \le \vec{b}$).

##### Development history, lineage, and evolution

- **`Astrée` (Cousot, Cousot, Feret, Mauborgne, Miné, Monniaux, Rival, ESOP
  2005, DOI `10.1007/978-3-540-31987-0_3`):** Proved absence of runtime errors in
  Airbus A340/A380 fly-by-wire C code by combining intervals, octagons, digital
  filter ellipsoid domains, and trace partitioning with widening ($\nabla$) and
  narrowing ($\Delta$).
- **`Verasco` (Jourdan, Laporte, Blazy, Leroy, Pichardie, POPL 2015, DOI
  `10.1145/2676726.2676966`):** Foundational static analyzer for CompCert `Csharpminor`
  verified in Rocq. `Verasco` decouples **untrusted fixpoint iteration** (using
  widening/narrowing to compute candidate loop invariants) from **verified
  post-fixpoint checking**, and uses **Farkas Lemma non-negative linear
  combination certificates** ($\vec{\lambda} \ge 0$ such that $\vec{\lambda}^T A =
  \vec{c}^T$ and $\vec{\lambda}^T \vec{b} \le d$) to verify polyhedral inclusion
  $P \sqsubseteq^{\#} Q$ inside Rocq without trusting an external simplex/PPL
  library.
- **`IKOS` (`NASA-SW-VnV/ikos@ac7f7c1738976cabc58c6a53413df6e458995c38`, Brat
  et al., NFM 2014), `Crab`, and `SeaHorn`
  (`seahorn/crab@b1eeb1a9402ab0664e962f26f89d923f8514284c`,
  `seahorn/seahorn@892780176731ec8e97bbb9f6b172fcacd77a8ff4`, Gurfinkel et
  al., CAV 2015):** LLVM-based C++/C abstract interpreters (`Crab` supplies
  Zones/Octagons invariants to `SeaHorn`'s `Spacer` CHC solver).
- **`MIRAI` (`endorlabs/MIRAI@aae0a56f91d9a0a62073bb86e7b2c9793cefc24b`):**
  Abstract interpreter over Rust MIR combining symbolic summaries with Z3 path
  queries and taint/tag propagation.

##### Exact mapping onto Anneal's four `trusted/` primitives

Anneal directly adopts `Verasco`'s **untrusted fixpoint finder + verified
post-fixpoint checker** architecture inside `theory/`:

1. An external analyzer (`Crab`-style Rust tool) computes a candidate invariant
   map `inv : BasicBlockId → AbstractVal` and Farkas multiplier certificates
   `NumFixpointCert`.
2. In `theory/`, `checkNumFixpoint : MirBody → NumFixpointCert → Bool` verifies
   $F^{\#}(\text{inv}[\text{bb}]) \sqsubseteq^{\#} \text{inv}[\text{bb}']$ on
   every CFG edge and checks that $\text{inv}[\text{bb}]$ implies safety of each
   arithmetic/bounds check in block $\text{bb}$.
3. A generic 1-step inductive invariant lemma `SmallStepMachine.invariant_defined`
   proved once in `theory/` lifts the 1-step concretization soundness
   ($s \in \gamma(a) \to \text{step}(s) \neq \text{.failed .ub} \wedge s' \in
   \gamma(F^{\#}(a))$) directly to `EventualBehaviorOf` (`(L_mir.sem f q).defined`),
   discharging the numerical obligations in `VerificationResult`.

Basis: **source** — Verasco POPL 2015 DOI `10.1145/2676726.2676966`, Astrée ESOP
2005 DOI `10.1007/978-3-540-31987-0_3`, `seahorn/crab@b1eeb1a9402ab0664e962f26f89d923f8514284c`,
`NASA-SW-VnV/ikos@ac7f7c1738976cabc58c6a53413df6e458995c38`,
`endorlabs/MIRAI@aae0a56f91d9a0a62073bb86e7b2c9793cefc24b`, and
`Trusted/StepResult.lean`; **derived** — 1-step `SmallStepMachine` to
`EventualBehaviorOf` lifting theorem.

---

#### 6.2 `UC-5.2`: Bitfield, alignment, and `tnum` / `KnownBits` abstract domains (`eBPF tnum`/`Agni`/`PREVAIL`, `LLVM KnownBits`)

##### Goals, problem domain, and target users

Low-level systems code masks pointer alignment bits (`addr & !(align - 1)`),
manipulates page-table flags, and extracts packet bitfields where interval
domains $[l, u]$ lose all precision across bitwise `&`, `|`, `^`, and shifts.
The **tristate / `tnum` (`KnownBits`)** domain represents each bit of a $w$-bit
word as $\{0, 1, ?\}$ via a pair of masks `(value, mask)` (in Linux eBPF `tnum`,
where `value & mask == 0`) or `(known_zeros, known_ones)` (in LLVM `KnownBits`,
where `known_zeros & known_ones == 0`).

##### Development history, lineage, and evolution

- **`Linux eBPF tnum` and `Agni` (Vishwanathan, Shachnai, Narayana, Nagarakatte,
  PLDI 2022 DOI `10.1145/3519939.3523440`; CAV 2023 DOI
  `10.1007/978-3-031-37709-9_12`):** Formalized the Linux kernel eBPF verifier's
  `tnum` bitwise transfer functions (`tnum_add`, `tnum_sub`, `tnum_mul`,
  `tnum_and`, `tnum_or`, `tnum_xor`, `tnum_rshift`) and reduced product with
  signed/unsigned 64-bit and 32-bit intervals (`reg_bounds_sync`), finding real
  soundness bugs in kernel range-synchronization logic.
- **`PREVAIL` (`vbpf/prevail@cefe6a799f8b8f37aa2560e196f223802717c1e7`, Gershuni
  et al., PLDI 2019, DOI `10.1145/3314221.3314590`):** Polynomial-time eBPF
  abstract interpreter using the Zone domain (`SplitDBM`) over register and
  stack-slot types/offsets.
- **`LLVM KnownBits`
  (`llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1`,
  `llvm/include/llvm/Support/KnownBits.h`):** Core LLVM bit-tracking analysis
  whose optimality and soundness have been mechanized in Lean 4 via `bv_decide`
  (`opencompl/lean-mlir@b8c4a77131919c8e18cf8bc7fdde40ef3cf87924`).

##### Exact mapping onto Anneal's four `trusted/` primitives

In `theory/`, the soundness of every 64-bit `tnum` / `KnownBits` abstract
transfer operator (`and#`, `or#`, `xor#`, `add#`, `shl#`, `lshr#`) is proved
**once and for all using `bv_decide`**. A per-function fixpoint certificate
`KnownBitsCert` is then checked by `checkKnownBits : MirBody → KnownBitsCert →
Bool` in `theory/`, discharging pointer-alignment UB obligations (`addr & (align - 1) == 0`)
and shift-bound obligations in `VerificationResult` alongside `checkNumFixpoint`
(`UC-5.1`) on the same function.

Basis: **source** — Agni CAV 2023 DOI `10.1007/978-3-031-37709-9_12`,
`vbpf/prevail@cefe6a799f8b8f37aa2560e196f223802717c1e7`,
`llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1`, and
`opencompl/lean-mlir@b8c4a77131919c8e18cf8bc7fdde40ef3cf87924`;
**derived** — multi-analyzer composition in `VerificationResult`.

---

#### 6.3 `UC-5.3`: Byte-level initialization (`MaybeUninit`) and stack-escape analyzers (`Frama-C Eva`, `Goblint`, `Mopsa`, `Rudra`/`SafeDrop`/`Lockbud`)

##### Goals, problem domain, and target users

Unsafe Rust uses `MaybeUninit<T>`, `[MaybeUninit<u8>; N]`, and manual `ptr::write`
loops to initialize buffers incrementally before calling `assume_init()`.
Reading uninitialized non-padding bytes at a typed load or allowing a pointer to
a stack local to escape past `StorageDead` causes immediate UB.

##### Development history, lineage, and evolution

- **`Frama-C Eva` (`git.frama-c.com/pub/frama-c@ce0648c726122d4a7b5e8614a1a5b97777d9d226`,
  Bühler et al.; Kirchner et al., FAC 2015):** Evolved Value Analysis plug-in
  for Frama-C that tracks byte-level initialization bitmaps, escaping stack
  addresses (`\dangling`), and base-offset pointer maps (`cvalue`) across C
  code.
- **`Mopsa` (`mopsa/mopsa-analyzer@f168a9c025738d4940cfb6a281dde258c871da73`,
  Journault, Miné, Ouadjaout, NFM 2019) and `Goblint`
  (`goblint/analyzer@1463f411ce87edd49198033856b2946fc3366fb2`):** Modular
  abstract interpreters where cell-splitting memory domains (`Mopsa`) dynamically
  split and merge byte ranges upon type punning or partial initialization, while
  `Goblint` tracks multi-threaded points-to and escape sets.
- **`Rudra` (`sslab-gatech/Rudra@fc9add2c4721c77490680462c7f0ad791af7cec7`, Bae
  et al., SOSP 2021, DOI `10.1145/3477132.3483570`), `SafeDrop` (Cui et al.,
  TOSEM 2023), and `Lockbud`
  (`BurtonQin/lockbud@a1b5303cdbb1d4d0ad886359cc71418570e7c5fd`):** Rust MIR
  static bug finders targeting `unsafe` initialization bypasses (`Vec::set_len`
  before element writes, causing drop/read of uninitialized memory on panic),
  dangling pointers across drop glue, and double locks.

##### Exact mapping onto Anneal's four `trusted/` primitives

A certifying byte-initialization and escape checker `checkInitEscape : MirBody →
InitEscapeCert → Bool` in `theory/` tracks initialized byte ranges $[0, i)$ (for
example, coupled with loop induction variable $i$ from `UC-5.1`) and points-to sets
across `StorageLive` and `StorageDead`, discharging typed-load validity and
stack-escape UB obligations in `VerificationResult`. Across
`StepResult.externalCall` (such as an external I/O read initializing `0..ret`
bytes of a passed `MaybeUninit<u8>` slice), `branches` updates the
byte-initialization state of the slice according to the external function's
contract.

Basis: **source** — `git.frama-c.com/pub/frama-c@ce0648c726122d4a7b5e8614a1a5b97777d9d226`,
`mopsa/mopsa-analyzer@f168a9c025738d4940cfb6a281dde258c871da73`,
`goblint/analyzer@1463f411ce87edd49198033856b2946fc3366fb2`,
`sslab-gatech/Rudra@fc9add2c4721c77490680462c7f0ad791af7cec7`, and
`BurtonQin/lockbud@a1b5303cdbb1d4d0ad886359cc71418570e7c5fd`;
**derived** — byte-level `Uninit` + `StorageDead` requirement in `L_mir`.

---

#### 6.4 `UC-5.4`: Shape analysis and string/UTF-8 automaton domains (`TVLA`/`Forester`, `MemCAD`/`Xisa`)

##### Goals, problem domain, and target users

Pointer algorithms on lists/trees and byte-slice string routines calling
`core::str::from_utf8_unchecked` or `CStr::from_bytes_with_nul_unchecked`
require inductive shape invariants or regular-language (DFA) byte invariants.

##### Development history, lineage, and evolution

- **`TVLA` (Sagiv, Reps, Wilhelm, TOPLAS 2002, DOI `10.1145/514188.514190`) and
  `Forester` (Holík et al., CAV 2013):** `TVLA` abstracts unbounded heap graphs
  into finite 3-valued structures ($\{0, 1, 1/2\}$) using instrumentation
  predicates (reachability, cyclicity, sharing) and `Focus`/`Coerce` materialization.
  `Forester` represents heap shapes via forest automata.
- **`MemCAD` and `Xisa` (`Antique-team/memcad@d95caa514f2b66b8c43c015799084d281944f028`,
  Chang & Rival, POPL 2008, DOI `10.1145/1328438.1328469`):** Combine
  separation-logic inductive shape checkers (`Xisa`) with numerical abstract
  domains (`Apron`) to infer combined shape-and-data invariants automatically.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Rust, violating the safety precondition of `core::str::from_utf8_unchecked(v)`
is **library UB** (producing an invalid `&str` that later causes safe UTF-8
iterators to execute out-of-bounds `get_unchecked`). In Anneal, `unsafe` library
contracts are modeled via `StepResult.externalCall (boundaryInv := isValidUtf8 v)
branches` (or a `SpecOn` precondition on the callee). A certifying UTF-8 DFA /
shape fixpoint checker in `theory/` proves `isValidUtf8 v = true` at the call
site, discharging `boundaryInv` and unifying language UB with library-contract
UB under a single `trusted/` primitive.

Basis: **source** — TVLA TOPLAS 2002 DOI `10.1145/514188.514190`,
`Antique-team/memcad@d95caa514f2b66b8c43c015799084d281944f028`, and
`Trusted/StepResult.lean`; **derived** — unifying library UB and language UB via
`StepResult.externalCall`.

---

### 7. Category F: VCGens, characteristic formulae, termination, and modular invariants (`UC-6.1`–`UC-6.4`)

#### 7.1 `UC-6.1`: Dijkstra monad and predicate-transformer weakest-precondition VCGens (`F*`/`DM4All`, `Why3`, `Boogie`, `Lean 4 MPL`/`Std.Do`)

##### Goals, problem domain, and target users

Deductive verification environments compile imperative or monadic programs into
backward **Weakest Precondition (`WP`)** predicate transformers
$\text{wp}(p, Q)(q)$ so that sequential composition becomes function composition
($\text{wp}(p_1 ; p_2, Q) = \text{wp}(p_1, \text{wp}(p_2, Q))$) and the resulting
verification conditions can be simplified by `simp`, `omega`, `grind`, or SMT
solvers.

##### Development history, lineage, and evolution

- **`Boogie` (`boogie-org/boogie@751228a2cf2c78177f9a0d040904022294aea1b2`,
  Barnett et al., FMCO 2005; Parthasarathy et al., CAV 2021, DOI
  `10.1007/978-3-030-81688-9_33`):** Passifies unstructured CFGs into acyclic
  SSA DAGs via `havoc` + `assume` statements and computes linear-size weakest
  preconditions (avoiding exponential path blowup via block-level auxiliary
  variables). Parthasarathy et al. (CAV 2021) mechanized a Rocq certificate
  checker that validates Boogie's CFG-to-DAG passification and WP generation per
  run.
- **`Why3` (`why3/why3@d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`, Filliâtre &
  Paskevich, ESOP 2013):** ML-With-Regions intermediate verification platform
  using Fast WP over region-typed mutable values (`Creusot`'s original backend,
  now superseded by `Coma`).
- **`F*` and `Dijkstra Monads for All (DM4All)`
  (`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`, Swamy et al.,
  POPL 2016, DOI `10.1145/2837614.2837655`; Maillard et al., ICFP 2019, DOI
  `10.1145/3341708`):** Indexes a computational monad $M\,A$ by a specification
  monad $W\,A$ (a monotonic predicate transformer satisfying the Law of the
  Excluded Miracle) linked by a monad morphism $\theta : M \to W$.
- **`Lean 4 MPL` / `Std.Do` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
  v4.34.1, `src/Std/Do/`, Sebastian Graf et al.):** Provides `PredTrans ps α`,
  `WP m ps`, `WPMonad m ps`, and the `@[spec]`-driven `mvcgen` tactic inside
  Lean 4's standard library, automatically discharging monadic `do`-block
  verification conditions over `StateT`, `ExceptT`, and `forIn` loops.

##### Exact mapping onto Anneal's four `trusted/` primitives

As established in Section 1.2, Anneal's `Behavior Query Out := Query →
Partial (Out → Prop)` is order-isomorphic in `theory/` to a monotonic predicate
transformer `toWP(b)(Q)(q) := ∃ h : (b q).defined, ∀ o, (b q).val h o → Q o`.
In `theory/`, the **Dijkstra Monad Bridge Theorem** proves:

$$\bigl(L.\text{sem}\,p \le L.\text{SpecOn}\,\text{pre}\,\text{post} \;\wedge\; L.\text{ProductiveOn}\,\text{pre}\,p\bigr) \iff \forall q,\, \text{pre}(q) \to \text{toWP}(L.\text{sem}\,p)(\text{post}\,q)(q) \wedge \neg \text{toWP}(L.\text{sem}\,p)(\lambda \_.\,\text{False})(q)$$

Thus, `Lean 4`'s `Std.Do` / `mvcgen` tactic suite and `Boogie`-style linear-size
DAG WP generators sit entirely in `theory/` and discharge `SpecOn` +
`ProductiveOn` directly.

Basis: **source** — `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`
(`src/Std/Do/`), `boogie-org/boogie@751228a2cf2c78177f9a0d040904022294aea1b2`,
`why3/why3@d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`, DM4All ICFP 2019 DOI
`10.1145/3341708`, and `Trusted/Refinement.lean`; **derived** — `toWP` bridge
theorem.

---

#### 7.2 `UC-6.2`: Characteristic formulae (`CF`) interactive verification engines (`CFML 2.0`/`SPLean`, `CakeML CF`)

##### Goals, problem domain, and target users

When verifying intricate pointer or array algorithms interactively (e.g.,
Tarjan's SCC, union-find, suffix arrays, or garbage collectors), users prefer
tactic proofs (`xapp`, `xlet`, `xif`, `xwhile`) that follow the program's AST
structure without unfolding small-step operational semantics or program
counters.

##### Development history, lineage, and evolution

- **`CFML` and `CFML 2.0` (Charguéraud, ICFP 2011; Guéneau, Jourdan,
  Charguéraud, Pottier, ESOP 2018) and `SPLean`
  (`verse-lab/splean@e24286f51bd9ee207197d47ec587d592cdfb0ddc`):** Generates a
  syntax-directed **Characteristic Formula** $\llbracket e \rrbracket_{\text{CF}} :
  \text{HProp} \to (\text{Val} \to \text{HProp}) \to \text{Prop}$ for each
  expression $e$ such that $\llbracket e \rrbracket_{\text{CF}}\,H\,Q \implies
  \{H\}\,e\,\{Q\}$. `SPLean` ports CFML's `HProp` and `x`-tactics (`XSimp`,
  `WP1`) to Lean 4.
- **`CakeML CF` (`CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`,
  Guéneau, Myreen, Kumar, Norrish, ICFP 2017, DOI `10.1145/3110263`):** Replaces
  `CFML`'s external unverified OCaml formula generator with a **foundational,
  sound-by-construction characteristic formula combinator library** in HOL4,
  proved sound directly against CakeML's big-step operational semantics and I/O
  streams.

##### Exact mapping onto Anneal's four `trusted/` primitives

A characteristic formula has higher-order type `cf : Query → (Out → Prop) →
Prop`. Anneal embeds any monotonic characteristic formula `cf` into the
first-order `Behavior Query Out` in `trusted/` via the **principal-filter
(Dedekind-MacNeille) hull** in `theory/`:

```lean
def cfToBehavior (cf : Query → (Out → Prop) → Prop) : Behavior Query Out :=
  fun q =>
    { defined := cf q (fun _ => True)
      val := fun _ o => ∀ Φ : Out → Prop, cf q Φ → Φ o }
```

Proving `Abstracts L_cf L_mir idCodec cf_f f_mir` by syntax-directed induction
(matching `CakeML CF`) lets users verify Rust functions in Lean 4 using
`CFML`/`SPLean` tactics (`xlet`, `xapp`, `xif`) with zero small-step unfolding
and zero higher-order types in `trusted/lean/`.

Basis: **source** — `CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`
(ICFP 2017 DOI `10.1145/3110263`),
`verse-lab/splean@e24286f51bd9ee207197d47ec587d592cdfb0ddc`, and
`Trusted/Refinement.lean`; **derived** — `cfToBehavior` principal-filter
embedding.

---

#### 7.3 `UC-6.3`: Lexicographic ranking-function and size-change termination (`SCT`) verifiers (`AProVE`/`Ultimate Automizer`, `CeTA`/`IsaFoR`, `Foetus`, `Terminator`/`RankFinder`)

##### Goals, problem domain, and target users

Total-correctness specifications for kernel routines, bootloaders, and parsers
must prove that no input can trigger an infinite loop or mutually recursive
divergence.

##### Development history, lineage, and evolution

- **`Foetus` and Size-Change Termination (`SCT`) (Abel, 1998; Lee, Jones,
  Ben-Amram, POPL 2001, DOI `10.1145/360204.360210`):** Proves termination of
  mutually recursive programs by tracking parameter decreases ($\xrightarrow{\downarrow}$,
  $\xrightarrow{\le}$) in bipartite size-change graphs $G_{f \to g}$ and checking
  that every idempotent composition $G ; G = G$ in the transitive closure
  contains a strictly decreasing thread $x \xrightarrow{\downarrow} x$.
- **`RankFinder` and `Terminator` (Podelski & Rybalchenko, VMCAI 2004, DOI
  `10.1007/978-3-540-24622-0_20`; Cook, Podelski, Rybalchenko, PLDI 2006, DOI
  `10.1145/1133981.1134029`):** `RankFinder` uses Farkas's Lemma to synthesize
  linear ranking functions completely for single-path loops; `Terminator` proves
  general transition invariants are included in a disjunctive union of
  well-founded relations $R^+ \subseteq T_1 \cup \dots \cup T_k$ by
  counterexample-guided abstraction refinement.
- **`AProVE` (Giesl et al., JAR 2017), `Ultimate Automizer`
  (`ultimate-pa/ultimate@82f536df1bea812c74d70a91d8e67c1770c3fefe`, Heizmann et
  al., CAV 2013, DOI `10.1007/978-3-642-39799-8_42`), and `CeTA`/`IsaFoR`
  (Thiemann & Sternagel, TPHOLs 2009, DOI `10.1007/978-3-642-03359-9_31`):**
  `AProVE` and `Ultimate Automizer` synthesize lexicographic ranking functions
  and Buchi automata decompositions; `CeTA` (`IsaFoR`) is an Isabelle/HOL
  verified certificate checker (`CPF`, Certification Problem Format) that
  validates termination proofs emitted by untrusted termination provers.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal, a certifying termination checker `checkTermination : CrateMir →
TermCert → Bool` in `theory/` (`CeTA`-style, checking either lexicographic
ranking Farkas witnesses or idempotent size-change graphs) proves
`L_mir.sem f ≤ SpecTerminatesOn pre`, where `SpecTerminatesOn` maps
`EventualOut.diverges` to `False`:

- **Critical Stress Test on `StepResult.externalCall` and Divergence:**
  In `Trusted/StepResult.lean`, `StepResult.externalCall boundaryInv branches`
  transitions in a single step $s \to s'$ (`s' ∈ branches`). If an external FFI
  callee or callback may itself **diverge** without returning, a 1-step
  `branches : State → Prop` transition to normal return states would falsely
  treat the external call as terminating in 1 step!
- Therefore, to keep total-correctness proofs (`SpecTerminatesOn`) sound across
  external calls, either (a) `L_mir.State` includes a designated diverging sink
  state `State.externalDiverged` (with a self-loop `step p .externalDiverged
  (.choice (· = .externalDiverged))`) that belongs to `branches` whenever the
  callee is not proved terminating, or (b) `VerificationResult` requires every
  callee invoked by a total-correctness function to carry its own
  `SpecTerminatesOn` obligation.

Basis: **source** — SCT POPL 2001 DOI `10.1145/360204.360210`, Terminator PLDI
2006 DOI `10.1145/1133981.1134029`, CeTA TPHOLs 2009 DOI
`10.1007/978-3-642-03359-9_31`, `ultimate-pa/ultimate@82f536df1bea812c74d70a91d8e67c1770c3fefe`,
and `Trusted/StepResult.lean`; **derived** — diverging-callee soundness
condition on `StepResult.externalCall`.

---

#### 7.4 `UC-6.4`: Modular `AdtInv` representation invariants and safe public boundaries (`Dafny`/`VCC` `pack`/`unpack`, `RustBelt` semantic soundness)

##### Goals, problem domain, and target users

Safe encapsulation of `unsafe` code is the foundational contract of Rust libraries
(`Vec<T>`, `String`, `RefCell<T>`, `zerocopy` wrappers): a module maintains a
private representation invariant `AdtInv(v, heap)` across all public safe
methods (`pub fn`), ensuring no external safe caller—even one passing malicious
re-entrant callbacks `f: impl FnMut(&T)`—can trigger UB.

##### Development history, lineage, and evolution

- **`Boogie`/`Spec#` and `VCC` Ownership Methodology (Barnett, DeLine,
  Fähndrich, Leino, Schulte, JOT 2004; Cohen et al., TPHOLs 2009, DOI
  `10.1007/978-3-642-03359-9_2`) and `Dafny`
  (`dafny-lang/dafny@5f717bf447b19d38cad1b69b1bf9a9f102feccfb`, Leino, LPAR
  2010):** Introduced a ghost boolean field `o.inv` (`closed` vs. `mutable`) on
  every object with explicit ghost statements `unpack o` (opening the invariant
  to permit field mutations) and `pack o` (proving `Inv(o)` holds and closing
  the object). Crucially, `Spec#`/`VCC` developed this methodology to defeat the
  **re-entrancy callback vulnerability**: if a method mutates `o`'s fields while
  `o` is unpacked and invokes an external method/callback that re-enters `o`,
  any method preconditioned only on `closed(o)` detects that `o` is unpacked!
- **`RustBelt` (`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
  Jung et al., POPL 2018, DOI `10.1145/3158154`):** Formulated semantic type
  soundness for Rust ADTs where every safe `pub fn` must preserve the semantic
  interpretation $\llbracket \tau \rrbracket$ at function entry, function exit
  (normal and unwind), and across every call to an unknown closure or trait
  method.

##### Exact mapping onto Anneal's four `trusted/` primitives

`UC-6.4` exercises **all four of Anneal's `trusted/` primitives simultaneously**
and demonstrates why `StepResult.externalCall` is indispensable:

1. **Non-Vacuous Invariant (`InhabitedPre (AdtInv ty)`):** Proves that the
   module's representation invariant `AdtInv` is satisfiable (e.g., witnessed by
   `MyVec::new()`).
2. **Entry/Exit Preservation (`L_mir.SpecOn pre_AdtInv post_AdtInv` +
   `L_mir.ProductiveOn pre_AdtInv m`):** Every safe `pub fn m` assumes `AdtInv`
   on input arguments (`pre_AdtInv`) and re-establishes `AdtInv` on all
   surviving mutable borrows and return values (`post_AdtInv`).
3. **Defeating Re-Entrancy Exploits via `StepResult.externalCall`:**
   As mechanized in `anneal-structural-external-calls-and-tcb-mutation-testing-2026`
   (`naive_reentrancy_exploit_triggers_ub` vs. `canary_reentrant_callback_rejected`
   in `support/StructuralExternalCallAndCanaries.lean`), checking `AdtInv` only
   at function entry and return (`post_AdtInv`) is **unsound** when a method
   temporarily breaks `AdtInv` (corresponding to `VCC`'s `unpacked` state),
   invokes a caller-supplied closure `f(&elem)` (e.g., `Vec::retain` or
   `Vec::drain`), and plans to restore `AdtInv` after `f` returns: `f` can
   re-enter the module or panic while `AdtInv` is broken! Because
   `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop)`
   checks `boundaryInv := AdtInv(self, s.heap)` **at the exact call step to `f`**
   and immediately transitions to `.failed .ub` (`defined = False`) if
   `boundaryInv = false`, Anneal structurally forces `AdtInv` to be packed
   (`closed`) before any external callback is invoked.

Basis: **source** — VCC TPHOLs 2009 DOI `10.1007/978-3-642-03359-9_2`,
`dafny-lang/dafny@5f717bf447b19d38cad1b69b1bf9a9f102feccfb`,
`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`, and
`anneal-structural-external-calls-and-tcb-mutation-testing-2026`;
**derived** — equivalence between `VCC` `pack` before callbacks and
`StepResult.externalCall` `boundaryInv`.

---

### 8. Master crosswalk across all 24 use cases (`UC-1.1`–`UC-6.4`)

| Use Case | Representative Real-World Tools | Primary `trusted/` Direction | `Query` / `Out` / `SemObs` Instantiation | Execution / Proof Mode in `theory/` | Key `trusted/` Invariant or Stress Test |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`UC-1.1`** | `Aeneas`, `Charon`, `RustHorn`, `RustHornBelt`, `Creusot`/`Coma`, `rocq-of-rust`, `Electrolysis`, `hax` | `Abstracts L_pure L_mir` + `ProductiveOn` | `L_pure.Query` = pure vals + layout; `decodeOut` checks backward/prophecy eqs | Certifying per-fn simulation / tactic | `ProductiveOn` blocks empty-prophecy miracles; partial `decodeOut` enforces framing |
| **`UC-1.2`** | `AutoCorres`/`AutoCorres2`, `Aeneas` `CCPO`/`loop` | `Abstracts L_loop L_mir` | `.diverges` mapped to `False` (total) or `True` (partial) | Constructive loop combinator + WTO cert | Fuel exhaustion in `Abstracts` must be demonic choice, never `.stuck` |
| **`UC-1.3`** | `Interaction Trees`/`Vellvm`, `FreeSpec`/`DimSum` | `Abstracts L_itree L_mir` + `externalCall` | `SemObs = EventualOut Obs Unit` aligns `ITree` `Vis` events with `L_mir` | Constructive trace handler in `theory/` | `EventualBehaviorOf` gives tau-insensitivity (`eutt`) without coinduction |
| **`UC-1.4`** | `Lean 4 bv_decide`, `SAW`/`Crucible`/`crux-mir`, `Kani`, `Rosette`/`Serval`, `HolBA`/`Islaris`/`Sail` | `L_mir.sem ≤ SpecOn` + `VerificationResult` | Symbolic path tree leaves emitted as `BitVec` obligations | Constructive `symEval` + kernel `LRAT` (`decide`) | Fine-grained per-check `Obligation` reporting in `VerificationResult` |
| **`UC-2.1`** | `Iris`/`MoSeL`, `iris-lean`, `RustBelt`, `RefinedC`/`Caesium`, `RefinedRust`, `VST` | Adequacy $\to$ `SpecOn` + `ProductiveOn` | All `CMRA`/`iProp`/step-indices erased by `iris_adequacy` in `theory/` | Constructive adequacy meta-theorem + tactics | `EventualBehaviorOf` separates finite-prefix `.failed .ub` from `.diverges` |
| **`UC-2.2`** | `CN`/`Fulminate`, `VeriFast`, `Viper`/`Prusti`, `Gillian`/`Gillian-Rust`, `Smallfoot`/`Infer`/`Pulse` | Certifying `checkSymHeapCert` $\to$ `SpecOn` | `SymHeap` interpreted over disjoint `MirState` sub-heaps | Certifying (`decide` over fold/unfold hints) | `StepResult.externalCall` `branches` must preserve unescaped caller heap frames |
| **`UC-2.3`** | `VerCors`, `Steel`/`Pulse` (F\*), fractional permissions | `Abstracts L_frac L_mir` (with `initPerm`) | `L_frac.Query := MirState`; ghost `Addr → Rat` initialized inside `sem` | Certifying rational conservation checker | `decodeQuery (encodeQuery q) = q` forbids adding ghost state to `L_v.Query` |
| **`UC-2.4`** | `GhostCell`/`qcell`, `Verus` `Tracked<PointsTo<T>>` & `PCell` | `Abstracts L_arena L_mir` + `ProductiveOn` | Erased 0-byte ZST `GhostToken<'brand>` reified as pure `ArenaMap` | Constructive API proofs + `UC-1.1` lens | Verifying erased ZST tokens and `'brand` lifetimes over `Runtime(PostCleanup)` MIR |
| **`UC-3.1`** | `Miri`, `Stacked Borrows`, `Tree Borrows`, `BorrowSanitizer` | `Abstracts L_untagged L_mir_tb` & `Compiles L_sb L_tb` | Strips `BorrowTree` shadow state after proving tag safety | Constructive for safe MIR; certifying for `unsafe` | Tree Borrows `Protector` survival across `StepResult.externalCall` |
| **`UC-3.2`** | `Polonius`, `Oxide`/`Patina`, `Aquascope` | Certifying `checkPolonius` $\to$ `VerificationResult` | Datalog Horn closure over `(Origin, Loan, Point)` | Certifying $O(|E|\cdot|O|^2)$ relation check (`decide`) | Decouples Datalog fixpoint search from fast kernel post-fixpoint checking |
| **`UC-3.3`** | `Strict/Exposed Provenance`, `VIP`, `CompCertS`/`Quasi-Concrete`, `CHERI`/`Morello` | `Abstracts L_tagged L_mir` | `TaggedPtr T k := ValidPtr T × BitVec k` packed via `map_addr` | Constructive lens + `bv_decide` | `with_exposed_provenance` cannot be demonic choice over all exposed `AllocId`s |
| **`UC-3.4`** | `MiniRust`, `Cerberus`, `CompCert Memdata` | Bilateral `Compiles` $\wedge$ `Abstracts` | Bridges `AbstractByte` arrays to structured `MirVal` via `SemObs` | Constructive bisimulation in `theory/` | `encodeOut_of_decodeOut` requires projecting out uninit struct padding at return |
| **`UC-4.1`** | `Flux`, `Liquid Haskell`, `Stainless` | Certifying `checkFluxTypes` $\to$ `VerificationResult` + `InhabitedPre` | Emits per-subtyping Horn VCs into `VerificationResult` | Certifying typechecker + `omega`/`bv_decide` | `InhabitedPre` blocks contradictory refinement preconditions (`x > 10 ∧ x < 5`) |
| **`UC-4.2`** | `embedded-hal`/`embassy`, `Verus tokenized_state_machine!` | `Abstracts L_automaton L_mir` + `externalCall` | Protocol transitions checked via `boundaryInv` and `trace : List Obs` | Certifying typestate checker in `theory/` | `StepResult.externalCall` `boundaryInv` enforces trace safety on `.diverges` loops |
| **`UC-4.3`** | `Austral`, `Vale` | `L_mir.sem ≤ SpecOn pre post_linear` | Inspects both `TerminationKind.normal` and `TerminationKind.unwind` | Certifying CFG dataflow checker | Verifies linear obligation consumption across `Runtime(PostCleanup)` unwind paths |
| **`UC-4.4`** | `no-panic`, `rtsan`/`cargo-call-stack`, `F*`/`Low*`/`KaRaMeL`, `Koka`/`Effekt` | `SpecOn` + `Abstracts L_det L_mir` + `ProductiveOn` | Singleton outcome in `L_det` + `ProductiveOn` proves determinism | Certifying call-graph & trace effect checker | Demonic `Abstracts` + `ProductiveOn` yields exact determinism for free |
| **`UC-5.1`** | `Verasco`, `Astrée`, `Crab`/`SeaHorn`, `IKOS`, `MIRAI` | Certifying `checkNumFixpoint` + Farkas witnesses $\to$ `VerificationResult` | 1-step `SmallStepMachine` inductive invariant lifts to `EventualBehaviorOf` | Certifying (`decide` over Farkas multipliers) | Generic 1-step invariant lifting from `SmallStepMachine` to `EventualBehaviorOf` |
| **`UC-5.2`** | `eBPF tnum`/`Agni`/`PREVAIL`, `LLVM KnownBits` | Certifying `checkKnownBits` $\to$ `VerificationResult` | Abstract `(known_zeros, known_ones, align)` proved sound via `bv_decide` | Constructive domain (`bv_decide`) + certifying CFG | Composing multiple analyzers on disjoint `Obligation` IDs in `VerificationResult` |
| **`UC-5.3`** | `Frama-C Eva`, `Goblint`, `Mopsa`, `Rudra`/`SafeDrop`/`Lockbud` | Certifying `checkInitEscape` $\to$ `VerificationResult` | Tracks byte-level `Init`/`Uninit` bitmaps and `StorageDead` escape sets | Certifying abstract interpreter in `theory/` | Requires byte-accurate `Uninit` and `StorageDead` semantics in `L_mir` |
| **`UC-5.4`** | `TVLA`/`Forester`, `MemCAD`/`Xisa` | Certifying DFA/shape checker $\to$ `externalCall boundaryInv` | Discharges `isValidUtf8` at `from_utf8_unchecked` boundaries | Certifying fixpoint checker in `theory/` | Unifies library-contract UB with language UB via `StepResult.externalCall` |
| **`UC-6.1`** | `F*`/`DM4All`, `Why3`, `Boogie`, `Lean 4 MPL`/`Std.Do` | `toWP` isomorphism $\leftrightarrow$ `SpecOn` + `ProductiveOn` | `Partial (Out → Prop)` $\cong$ monotonic predicate transformer | Constructive VCGen / `mvcgen` in `theory/` | Proves `ProductiveOn` is exactly Dijkstra's Law of the Excluded Miracle |
| **`UC-6.2`** | `CFML 2.0`/`SPLean`, `CakeML CF` | `Abstracts L_cf L_mir` | Principal-filter hull embeds higher-order `CF` into `Behavior` | Constructive `CF` generator + `x`-tactics | Embeds higher-order `(Out → Prop) → Prop` into first-order `trusted/` `Behavior` |
| **`UC-6.3`** | `AProVE`/`Ultimate Automizer`, `CeTA`/`IsaFoR`, `Foetus`/`SCT`, `Terminator`/`RankFinder` | `L_mir.sem ≤ SpecTerminatesOn pre` | Maps `EventualOut.diverges` to `False` via well-founded measure | Certifying (`RankCert` / `SctCert` via `decide`) | Requires `StepResult.externalCall` to model potentially diverging external callees |
| **`UC-6.4`** | `Dafny`/`VCC` (`pack`/`unpack`), `RustBelt` `AdtInv` | `SpecOn` + `ProductiveOn` + `InhabitedPre` + `externalCall` | Checks `AdtInv` at entry, exit, and `externalCall` callback boundaries | Modular deductive verification pattern | Catches re-entrancy soundness bugs (`Vec::drain` / `RefCell`) via `boundaryInv` |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **Loom, Velvet, and Veil (`verse-lab/loom`, Sergey et al. 2024-2026):** Multi-
  modal Lean 4 program verification framework using Monad Transformer Algebras
  for weakest-precondition generation over demonic/angelic nondeterminism; maps
  onto `Language.Behavior` and `ProductiveOn`.
- **Strata (`strata-org/strata`, AWS 2025-2026) and LNSym
  (`leanprover/LNSym`):** Lean 4 dialect/IR semantics and symbolic simulator
  (`sym_n` + `bv_decide`) for small-step operational models; maps onto
  `SmallStepMachine` and `Compiles`.
- **KMIR / KRust (`runtimeverification/kmir`) and CTrees (`vellvm/ctrees`, POPL
  2023):** Executable operational semantics for `rustc` MIR in K and Choice
  Trees in Rocq extending `ITree` with explicit stepping and demonic/angelic
  branching (`StepResult.externalCall`).
- **ArkLib (`Verified-zkEVM/ArkLib`), zkLean (`GaloisInc/zkLean`), and Clean
  (2024-2026):** Lean 4 verification libraries targeted by
  `Charon`/`Aeneas`/`hax` functional extraction pipelines.
- **Corten / CortenMM (Gaher et al. 2024-2025), Diaframe (`iris/diaframe`),
  Lithium (`iris/refinedc`), and Katamaran (`katamaran-project/katamaran`):**
  Foundational Rocq/Iris separation-logic and symbolic-heap frame-inference
  engines automating bi-abduction and contract checking.
- **`a-mir-formality` (`rust-lang/a-mir-formality`) and Flowistry
  (`willcrichton/flowistry`, OOPSLA 2022):** Authoritative executable
  specification of Rust's trait/Polonius borrow checker and MIR information-flow
  analyzer.
- **Vostd (`asterinas/vostd`), Atmosphere, VeriSMo, Anvil (OSDI/SOSP 2024-2025),
  and `klint` (`Darksonn/klint`):** Verified Rust OS kernels/controllers using
  Verus tokenized state machines and `rustc` atomic-context preemption tracking
  (`Partial.ub` on sleeping while atomic).
- **Pagai, Clam (`seahorn/clam`), Apron, ELINA (`eth-sri/elina`), and LiSA
  (`lisa-analyzer/lisa`):** Numerical (`Polyhedra`/`Zonotope`) and FSA string
  abstract-interpretation domains (`Abstracts`).
- **Lean 4 `Std.Do` / `mvcgen` (`sgraf812/mpl`, 2024-2026), Gospel/Cameleer
  (`ocaml-gospel/cameleer`), and Lean 4 `guessLex`:** Monadic weakest-
  precondition VCGens and size-change lexicographic termination synthesizers.

---

### Part II — Historical Verification Failures, Root-Cause Postmortems, and Architectural Defenses

### 1. Cross-Cutting Failure Taxonomy and Mapping to Anneal's Four Primitives

Basis: **derived** synthesis from the primary source, bug-tracker, CVE, and
execution evidence in §§2–6.

Every historical failure mode examined in §§2–5 exploits a specific gap between
the artifact a user believes they verified and the semantic proposition actually
checked by the tool. The table below indexes all 28 historical failure
postmortems in this report against the exact Anneal `trusted/lean/` primitive
that closes the corresponding vulnerability class:

| Failure ID | System(s) & Primary Coordinates | Failure Category | Root-Cause Mechanism | Anneal `trusted/` Defense Primitive & Architectural Mechanism |
| :--- | :--- | :--- | :--- | :--- |
| **F-1.1** | `Dafny` (`#6534`, `#6537`) | Prelude Axiom Soundness | Unguarded `$Box($Unbox(x): T) == x` and `Map#Items` prelude axioms admit ill-typed terms and derive `false` via E-matching | Zero background SMT prelude in `trusted/`; all domain lemmas live in `theory/` and must be proved constructively in Lean 4's kernel |
| **F-1.2** | `Dafny` (`#4053`), `Verus` (`air/smt_verify.rs`), `Why3` | Unchecked Solver Backend | Z3 `/proverOpt:O:smt.arith.solver=6` bug or solver bug returns `unsat` without proof certificate reconstruction | `trusted/audit/` inspects `.olean` kernel environment directly; external solvers must emit `LRAT`/`Alethe`/Farkas certificates checked in `theory/` |
| **F-1.3** | `Verus` (`verus@0141ebc`, `erasure.md`, `Tracked::assume_new`) | Ghost Erasure & Mode-Boundary Mismatch | Conditional compilation (`cfg(verus_only)`) or unverified callers forging zero-sized `Tracked<T>` wrappers break erased guarantees | Anneal captures post-macro `Runtime(PostCleanup)` MIR directly from `rustc`; `BehaviorCodec` binds pure ghost state to concrete `MirState` bytes |
| **F-1.4** | `Creusot`, `RustHorn`, `RustHornBelt` (PLDI 2022) | Prophetic Borrow Resolution Vacuity | Over-constrained prophecy variables $(v_{\text{cur}}, v_{\text{final}})$ yield empty outcome set ($\text{wp}(p, \text{False}) = \text{True}$) | `L.ProductiveOn pre prog` enforces Dijkstra's Law of the Excluded Miracle ($\exists h\,o,\, (L.\text{sem}\,p\,q).\text{val}\,h\,o$) |
| **F-1.5** | `Prusti` / `Viper` / `Boogie` (CAV 2021, PLDI 2024) | Frontend-to-IVL Inhale/Exhale Desugaring Bug | Flawed permission-mask exhale or shared-borrow encoding silently turns source failure into IVL `assume false` (magic) | `Abstracts L_v L_mir codec v s` (`L_mir.sem s ≤ codec.toMorphism (L_v.sem v)`) reflects `L_v` safety back to source `L_mir` failure freedom |
| **F-1.6** | `Kani` (`[F] Soundness` label) | Uninit Padding, Provenance & Stub Vacuity | CBMC translation omits byte-level `Uninit` padding checks, pointer provenance tags, or replaces functions with under-approximating stubs | `L_mir` models byte-accurate `AbstractByte` (`Uninit \| Init`) and provenance; `ProductiveOn` blocks under-approximating empty stubs |
| **F-1.7** | `F*` (`#4478`, `#4485`, `#4487`), `Liquid Haskell` / `Flux` | Empty-Domain / Contradictory Refinement Vacuity | VC simplifier assumes uninhabited function/refinement type is inhabited, or contradictory entry refinement proves `False` | `InhabitedPre pre` ($\exists q,\, \text{pre}(q)$) is mandatory alongside `SpecOn` and `ProductiveOn`, rejecting empty precondition domains |
| **F-1.8** | `Frama-C WP` (Vanadium `goto`), `KeY`, `ESC/Java2` | Abrupt Termination, Unstructured CFG & Loop Unrolling | `goto` across statement contracts breaks WP domination assumptions; `ESC/Java2` 1-step loop unrolling misses $k > 1$ bugs | `SmallStepMachine` operates directly on unstructured `Runtime(PostCleanup)` MIR CFGs with `EventualBehaviorOf` unbounded step closure |
| **F-2.1** | `RustBelt` (`MutexGuard::map`, `rust-lang/rust#25760`) | Lifetime Variance / Covariant Guard Soundness | `MutexGuard::map` inherited covariance where `'a: 'b` was not properly bounded for `&mut T` projection, allowing use-after-unlock | `StepResult.externalCall` and `AdtInv` proofs operate over post-monomorphization/post-cleanup MIR memory lifetimes and active protectors |
| **F-2.2** | `RustBelt Meets Relaxed Memory` (`Arc::get_mut`, `rust-lang/rust#51780`) | Sequential-Consistency Adequacy Gap | Original POPL 2018 RustBelt assumed SC memory; under C-2011 weak memory, `Arc::get_mut`'s `Relaxed` weak-count read raced with `Arc::clone`/`drop` | `Language SemObs` allows instantiating weak-memory `SmallStepMachine` models in `theory/` without baking an SC assumption into `trusted/` |
| **F-2.3** | Rust `std` (`Vec::dedup_by`, `BinaryHeap`, `RefCell`) | Callback Re-Entrancy & Panic Unwind Safety | Methods temporarily break `AdtInv` (`len > init`), call user closure `f` that panics or re-enters, and read uninitialized memory on drop | `StepResult.externalCall boundaryInv branches` checks `boundaryInv` (`AdtInv`) at the exact call step; `EventualOut` checks `Terminal.panic` unwind paths |
| **F-2.4** | `Stacked Borrows` (POPL 2020) vs. `Tree Borrows` (PLDI 2025) | Eager Borrow-Stack Pop on Idiomatic Unsafe Rust | Stacked Borrows eagerly pops `Unique` tags on parent reads (breaking two-phase borrows, `addr_of!`, `container_of`) and over-constrains `&mut` | `Tree Borrows` replaces stack pops with lazy `Reserved → Active → Frozen → Disabled` tree transitions; `Compiles L_sb L_tb` relates both in `theory/` |
| **F-2.5** | `Tree Borrows` Function-Entry `Protector` Semantics | Cross-Call Noalias & Interior Mutability Subtlety | `llvm.noalias` requires protected references to stay valid until function exit, even across unknown external callbacks, unless `UnsafeCell` is present | `StepResult.externalCall` checks active call-frame `Protector` invariants via `boundaryInv` and constrains `branches` across opaque calls |
| **F-2.6** | `rustc` Borrow Checker (`#25860`, `#84591`, `#100013`) | Implied Bounds + Variance + HRTB Soundness Hole | `rustc` omits `ImpliedBounds` (`'b: 'a` from `&'a &'b T`) inside higher-ranked trait binders (`for<'a>`), transmuting short lifetimes to `'static` in safe Rust | Anneal does not take `rustc`'s borrow checker as an axiom for memory safety; `L_mir` checks actual dynamic memory and borrow-tag safety on MIR |
| **F-2.7** | LLVM / C / Rust Provenance (`llvm#34548`, `llvm#35229`, `PNVI`) | Pointer-Integer Cast Folding & GVN Miscompilation | Combining `inttoptr(ptrtoint(p)) -> p` with integer equality GVN substitutes pointers of different provenance; angelic `with_exposed_provenance` clashes with demonic choice | `L_mir` tracks deterministic Strict Provenance (`AllocId`) natively and resolves exposed provenance deterministically by disjoint live address range |
| **F-3.1** | Linux eBPF Verifier (`CVE-2020-8835`, `581738a681b6`) | `JMP32` 32-Bit Branch Bounds Refinement Bug | `__reg_bound_offset32` improperly derived 64-bit/tnum bounds after 32-bit conditional jumps (`BPF_JMP32`), yielding OOB kernel R/W | Certifying abstract interpreters in `theory/` must prove 1-step concretization soundness ($\forall s \in \gamma(a),\, \text{step}(s) \subseteq \gamma(F^{\#}(a))$) via `bv_decide` |
| **F-3.2** | Linux eBPF Verifier (`CVE-2021-3490`, `049c4e13714e`) | `tnum` vs. `u32`/`s32` Bitwise `AND`/`OR`/`XOR` Bug | `scalar32_min_max_and`/`or`/`xor` skipped updating 32-bit bounds when `subreg_def` was known constant, leaving `u32_min > u32_max` | In `theory/`, reduced product reductions between `tnum` (`KnownBits`) and intervals are machine-checked on 64-bit bitvectors (`bv_decide`) |
| **F-3.3** | Linux eBPF Verifier (`CVE-2021-31440`, `10bf4e83167c`) | `__reg_combine_64_into_32` Endpoint Truncation Bug | Projecting 64-bit `[0x0_ffffffff, 0x1_00000000]` to 32-bit truncated endpoints without checking `(umin >> 32) == (umax >> 32)` | `bv_decide` immediately refutes the unguarded 64-to-32 interval projection theorem with the exact boundary counterexample |
| **F-3.4** | Linux eBPF Verifier (`CVE-2022-23222`, `64620e0a1e71`) | Nullable Pointer (`*_OR_NULL`) Arithmetic Bypass | `adjust_ptr_min_max_vals` permitted pointer arithmetic on `PTR_TO_MEM_OR_NULL` before null check, retaining false bounds when pointer was `NULL` | `L_mir` separates `Option/Nullable` discriminant tags from valid `AllocId` pointers; pointer arithmetic on `AllocId = none` fails (`defined = False`) |
| **F-3.5** | Linux eBPF Verifier (`CVE-2023-2163`, `71b547f56124`) | Incorrect CFG State-Pruning Precision Backpropagation | `propagate_precision` failed to walk all predecessor frames/branches when marking a register precise, pruning an unsafe path as equivalent to a safe one | Anneal's certifying fixpoint checker (`checkNumFixpoint`) checks inclusion $F^{\#}(\text{inv}[bb]) \sqsubseteq^{\#} \text{inv}[bb']$ at *every* CFG edge independently |
| **F-3.6** | Linux eBPF Abstract Domains (`Agni`, CGO 2022 / CAV 2023) | Unsound Abstract Bitwise & Multiplication Operators | `Agni` discovered latent unsoundness and precision inversions in kernel `tnum` multiplication and bitwise reduction routines | Separating domain transfer soundness (proved once in `theory/`) from per-program post-fixpoint checking eliminates analyzer-engine TCB bugs |
| **F-3.7** | `Frama-C Eva`, `Astrée`, `IKOS`, `MIRAI` | Threshold Widening Collapse & Unmodeled Library Stubs | Aggressive widening ($\nabla$) loses relational loop invariants ($i \le len$); `MIRAI` / `IKOS` missing stdlib stubs silently under-approximate side effects | External analyzers emit Farkas/Octagon fixpoint certificates checked in `theory/`; unverified callees must use `VerificationResult` waivers or `externalCall` |
| **F-4.1** | `Electrolysis` (Ullrich 2016) | Pure Lens Explosion & Interior Mutability Wall | Pure functional lenses (`get`/`set` laws) could not express `UnsafeCell`, `RefCell`, raw pointer aliasing, or borrows stored inside structs | Anneal places `L_mir` (`SmallStepMachine`) at the base of `trusted/` and uses `Abstracts L_pure L_mir` only for functions where functional lenses apply |
| **F-4.2** | `Prusti` (Legacy Encoder vs. Rewrite) | Monolithic Method-Granularity Viper Encoding | Encoding full Rust MIR + borrow lifetimes into one giant Viper method caused nonlinear Z3 timeouts and opaque fold/unfold errors | Fine-grained per-obligation decomposition in `VerificationResult` + modular `Abstracts` bridges allow mixing decidable checkers with interactive Lean proofs |
| **F-4.3** | `Aeneas` & `Charon` (`#583`, `#534`, `OfJson.ml`) | UB-Introducing Frontend Pass & Silent Partial Output | `Charon` `--preset=aeneas` rewrites raw-pointer indexing into reference creation (`#583`), loses quantified lifetimes (`#534`), and `OfJson.ml` drops `has_errors` | `anneal-rustc-capture` extracts unmodified `Runtime(PostCleanup)` MIR directly without reference-synthesizing rewrites and fails closed on errors |
| **F-4.4** | `Aeneas` & `RustHorn` | Functionalization Boundary on Cyclic/Aliased State | Backward functions and prophecies require strict tree-shaped non-aliasing; raw pointers, intrusive lists, and `Arc`/`Mutex` cannot be translated directly | Anneal supports heterogeneous verification in one crate: `Aeneas`-style `Abstracts` for safe callers composed with Iris/SymHeap proofs for `unsafe` leaves |
| **F-4.5** | `IronFleet` (SOSP 2015), `Dafny` (CAV 2016), `Verus`, `Viper` | SMT E-Matching "Butterfly Effect" & Trigger Loops | Unrelated variable renames or assertion additions alter Z3 quantifier instantiation order, turning 1s proofs into timeouts (`Mariposa` OOPSLA 2023) | Anneal freezes deterministic proof artifacts (Lean kernel terms, `LRAT`, `Alethe`, Farkas witnesses) in `theory/` rather than re-running heuristic SMT search in CI |
| **F-4.6** | `F*`, `Why3`, `Verus`, `Creusot` | Cross-Version Proof Session & Toolchain Drift | Upgrading the SMT solver or compiler nightly invalidates thousands of implicit VC obligations with no localized diagnostic | `VerificationResult` binds individual obligations to explicit source spans and deterministic kernel-checked certificates |

---

### 2. Deductive Verifier Soundness Bugs and Vacuity Postmortems

#### F-1.1: Background Prelude Axiom Inconsistencies (`Dafny` `#6534`, `#6537`)

Basis: **documentation** — `dafny-lang/dafny` issues `#6534` and `#6537`.

- **Historical failure:** Deductive verifiers that compile a high-level language
  to Boogie or SMT-LIB prepend a large, hand-authored axiomatic prelude (often
  2,000–5,000 lines of quantified SMT axioms defining boxing/unboxing, type
  tags, heap allocation maps, sequences, sets, and finite maps). In `Dafny`
  issue `#6534` (*"Soundness: unguarded `$Box($Unbox(x): T) == x` axiom"*), the
  Boogie prelude asserted the round-trip identity
  $\forall x : \text{Box}.\, \text{\$Box}(\text{\$Unbox}(x) : T) = x$ without
  guarding on whether $x$'s dynamic type tag actually matched $T$. When $T$ had
  a restricted cardinality or subset constraint (such as `bool` or a finite
  newtype), instantiating the unguarded axiom on boxes of two distinct types
  forced their unboxed values to collide, allowing Z3 to derive `false` and
  verify `ensures false`. Similarly, in `Dafny` issue `#6537` (*"Soundness:
  `Map#Items` membership axiom admits non-pairs"*), the axiomatization of
  `Map#Items` omitted a structural sort guard requiring elements of `m.Items` to
  be 2-tuples, creating a model contradiction with tuple projection axioms.
- **Technical root cause:** Unchecked universal axioms in an SMT prelude bypass
  definitional conservativity. Even a single missing sort/type-tag guard or an
  over-triggered quantifier in a 4,000-line `.bpl` prelude makes the background
  theory $\mathcal{T}_{\text{prelude}}$ unsatisfiable ($\mathcal{T}_{\text{prelude}} \vdash \bot$).
  Because an SMT solver checks validity of $G$ by testing unsatisfiability of
  $\mathcal{T}_{\text{prelude}} \wedge \neg G$, any inconsistency in
  $\mathcal{T}_{\text{prelude}}$ silently makes *every* verification condition
  return `unsat` ("Verified").
- **Architectural lesson for Anneal (`trusted/lean/`):** Anneal's `trusted/lean/`
  contains **zero background SMT prelude axioms** and zero uninterpreted
  function axiomatizations. All data structures (`BitVec`, `Array`, `List`,
  finite maps, and `L_mir` operational semantics) are defined constructively in
  Lean 4 (`trusted/lean/` and `theory/`), where Lean's kernel enforces
  definitional conservativity and `trusted/audit/` (`TrustedBoundary.lean`)
  audits `.olean` files to reject unauthorized `axiom` declarations.

#### F-1.2: SMT Solver Backend Bugs and Flag-Dependent Unsoundness (`Dafny` `#4053`, `Verus`, `Why3`)

Basis: **documentation** + **source** — `dafny-lang/dafny#4053`;
`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`,
`source/air/src/smt_verify.rs:249–364`.

- **Historical failure:** In `Dafny` issue `#4053` (*"Unsound verification with
  `/proverOpt:O:smt.arith.solver=6`"*), passing a non-default Z3 arithmetic
  solver configuration interacted with Dafny's prelude axioms and nonlinear
  arithmetic encoding to return `unsat` on an invalid assertion. More broadly,
  as established in our corpus report `verus-tracked-memory-trust-0141ebc`,
  `Verus`'s AIR backend (`smt_verify.rs:249–275`) sends an SMT-LIB query to Z3
  and treats the textual response `"unsat"` as `ValidityResult::Valid` without
  reconstructing a proof object; `Creusot`/`Why3`, `Prusti`/`Viper`, and
  `Dafny` do the same by default.
- **Technical root cause:** Mainstream SMT solvers (`Z3`, `cvc5`) are complex
  500,000+ line C++ codebases with intricate combinations of Nelson-Oppen theory
  propagation, E-matching, bit-blasting, and linear/nonlinear arithmetic. Trusting
  an uncertified `"unsat"` string places the entire C++ SMT solver and the
  verifier's VC-to-SMT-LIB pretty-printer inside the TCB.
- **Architectural lesson for Anneal (`trusted/lean/` & `trusted/audit/`):**
  Anneal never accepts an external solver's `"unsat"` status as a trusted
  verdict. `trusted/audit/` checks that `Trusted.CrateTheorem` has a complete,
  axiom-free proof term inside the Lean 4 kernel environment. When external SAT
  or SMT solvers are used in Anneal, they act strictly as untrusted certificate
  oracles that emit `LRAT`, `Alethe`, or Farkas linear-combination witnesses
  verified by total reflective checkers in `theory/`.

#### F-1.3: Ghost Erasure, Conditional-Compilation Skew, and Forged Tracked Tokens (`Verus`)

Basis: **source** + **documentation** —
`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`,
`source/builtin/src/lib.rs:546–570`, `source/vir/src/modes.rs`,
`source/docs/guide/src/erasure.md`.

- **Historical failure:** Deductive verifiers that extend Rust syntax with
  inline `spec` and `proof` blocks (`Verus`, `Creusot`, `Prusti`) must erase
  ghost code before invoking `rustc` to produce executable machine code. Three
  distinct failure modes have surfaced in `Verus`'s issue tracker and
  documentation:
  1. **Verification vs. compilation body skew (`erasure.md`):** Conditional
     compilation attributes (`#[cfg(verus_keep_ghost)]` / `verus_only`) can cause
     the VIR verifier to verify one function body while `rustc` compiles a
     different executable body.
  2. **Unhygienic spec/closure and integer-discriminant mismatches
     (`verus-lang/verus` `label:soundness`):** Soundness bugs in `Verus`'s internal
     VIR translator—such as mis-scoped variables in closure capture environments,
     const-generic substitution errors, or enum discriminant integer-width
     mismatches—allowed proving `ensures false` because the VIR encoding
     diverged from `rustc`'s type/layout rules.
  3. **Public API boundary bypass on erased `Tracked<T>` tokens
     (`builtin/src/lib.rs:546–570`):** At runtime, `Tracked<PointsTo<T>>` is a
     zero-sized wrapper (`PhantomData`). If a verified Verus function is called
     by ordinary unverified Rust code (or if macro visibility leaks allow
     calling `Tracked::assume_new`), the caller can pass a forged ZST token
     without owning the underlying memory permission.
- **Technical root cause:** Whenever verification operates on a custom
  pre-erasure AST (`VIR`) rather than the exact artifact compiled to machine
  code, any discrepancy between `VIR` lowering and `rustc` lowering—or any
  assumption carried only by erased ghost parameters at public crate
  boundaries—creates an unverified gap.
- **Architectural lesson for Anneal (`trusted/rustc-capture/` & `BehaviorCodec`):**
  1. `anneal-rustc-capture` extracts `Runtime(PostCleanup)` MIR directly from
     the active `rustc` compilation pass *after* macro expansion, type checking,
     borrow checking, and drop elaboration, ensuring verification and codegen
     see the exact same MIR control-flow graph and monomorphic type layouts.
  2. In `Abstracts L_v L_mir codec v s`, `codec : BehaviorCodec L_v L_mir`
     requires `decodeQuery (encodeQuery q₁) = q₁`. As proved in Sub-Domain 1
     Executive Finding #1, ghost permissions (like fractional maps or
     `GhostToken` arenas) cannot be left as unconstrained phantom arguments in
     `L_mir.Query`; they must be grounded as concrete heap-layout predicates in
     `MirState` (`encodeQuery`) or initialized deterministically from `MirState`.

#### F-1.4: Prophetic Borrow Resolution Vacuity and `#[trusted]` Invariant Gaps (`Creusot` & `RustHornBelt`)

Basis: **documentation** — Matsushita, Denis, Jourdan, and Dreyer, *"RustHornBelt:
A Semantic Foundation for Functional Verification of Rust Programs with Unsafe
Code,"* PLDI 2022, DOI `10.1145/3519939.3523704`; `creusot-rs/creusot`
`label:soundness` tracker.

- **Historical failure:** `RustHorn` and `Creusot` translate a mutable borrow
  `b: &'a mut T` into a pair of pure first-order values $(v_{\text{cur}},
  v_{\text{final}})$, where $v_{\text{final}}$ is a **prophecy variable**
  predicting the value `*b` will hold at the future point when lifetime `'a`
  ends (`Resolve::resolve`). When `'a` ends, the translator emits an assumption
  identifying the current value of `*b` with $v_{\text{final}}$:
  `assume (v_at_end == v_final)`. In `Creusot`'s development, soundness issues
  arose when:
  1. Custom or unsoundly specified `Resolve` implementations, type invariants
     (`creusot_contracts::Invariant`), or cyclic borrow resolutions introduced
     contradictory constraints on $v_{\text{final}}$, turning `assume (v_at_end == v_final)`
     into `assume false`; and
  2. Functions marked `#[trusted]` or external standard-library specifications
     (`Vec`, `HashMap`) omitted implicit type invariants or precondition guards,
     allowing callers to obtain values violating type invariants.
- **Technical root cause:** In predicate-transformer terms, a prophecy assumption
  `assume (P(v_final))` is demonic assumption: $\text{wp}(\texttt{assume } P, Q) = (P \to Q)$.
  If the constraints accumulated on $v_{\text{final}}$ along an execution path
  are unsatisfiable ($\neg \exists v_{\text{final}},\, P(v_{\text{final}})$),
  then $\forall v_{\text{final}},\, P(v_{\text{final}}) \to Q$ holds vacuously
  for *every* postcondition $Q$, including $Q = \text{False}$! That is why
  `RustHornBelt` (PLDI 2022) had to construct a delicate step-indexed semantic
  model of *parametric prophecies* in Iris to prove that well-typed safe Rust
  borrow resolutions always have a realizable prophecy assignment.
- **Architectural lesson for Anneal (`ProductiveOn` & `VerificationResult`):**
  1. Anneal's `L.ProductiveOn pre prog` (`∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o, (L.sem prog q).val h o`)
     directly enforces **non-empty outcome sets** (Dijkstra's Law of the Excluded
     Miracle). As verified in `support/failure_mechanisms_probe.py` (`witness_1`),
     any prophetic or backward-function translation in `theory/` (`L_pure`)
     whose prophecy resolution constraint is unsatisfiable produces an empty
     outcome set `(L_pure.sem f q).val h = ∅`, which is immediately rejected by
     `L_pure.ProductiveOn pre f`!
  2. Any unverified `#[trusted]` specification or waived obligation must be
     explicitly listed in `waived` inside `VerificationResult policy waived obligations`,
     where `policy.isAllowed` gates whether waivers are permitted and positive
     disjunction (`ob.id ∈ waived ∨ ob.prop`) prevents a flawed helper spec from
     contaminating unwaived obligations (`witness_3`).

#### F-1.5: Separation-Logic-to-IVL Inhale/Exhale Desugaring Bugs (`Prusti`, `Viper`, `Boogie`)

Basis: **documentation** — Parthasarathy et al., CAV 2021 (DOI
`10.1007/978-3-030-81688-9_33`) and PLDI 2024 (DOI `10.1145/3656438`);
`viperproject/prusti-dev` `label:unsoundness` tracker.

- **Historical failure:** `Prusti` compiles Rust MIR with specifications into
  `Viper` (an intermediate verification language with implicit dynamic frames),
  and `Viper`'s `Carbon` backend compiles `Viper` `inhale`/`exhale` statements
  into `Boogie` `assume`/`assert` statements over heap and permission-mask maps.
  Both `Prusti` and `Viper` experienced historical soundness bugs in this
  two-stage desugaring:
  1. In `Prusti`, early encodings of shared references (`&T`), specification
     refinements on trait implementations, and loop framing omitted permission
     read-framing checks or inhaled over-strong post-borrow state assumptions,
     allowing `assert!(false)` to verify.
  2. In `Viper` and `Boogie` (analyzed in Parthasarathy et al., CAV 2021 and
     PLDI 2024, and in our corpus report
     `boogie-viper-failure-reflection-certificates-2021-2024`), bugs in map
     encoding, background axiom generation, passification, or well-formedness
     ordering meant that a source program with a reachable failure reduced to a
     target `Boogie` program whose execution reached `assume false` (magic),
     causing `Boogie` to report the buggy program as verified.
- **Technical root cause:** A verifier frontend that lowers source code through
  unverified IVL transformations (`Rust → Viper → Boogie → SMT`) implicitly
  assumes **failure reflection**: every failing execution of the source program
  must correspond to a failing execution of the generated IVL program. If any
  lowering step accidentally turns a bad source state into an empty/magic target
  transition (`assume false`) or drops a branch, target verification succeeds
  while source safety fails.
- **Architectural lesson for Anneal (`Abstracts` in `Trusted/Refinement.lean`):**
  Anneal eliminates unverified IVL lowering from the TCB. In
  `Abstracts L_v L_mir codec v s` (`L_mir.sem s ≤ codec.toMorphism (L_v.sem v)`),
  the behavioral refinement order `b₂ ≤ b₁` on `Partial (Out → Prop)` is defined
  as:
  $$\forall q,\, (b_1\,q).\text{defined} \to \exists h_2 : (b_2\,q).\text{defined},\, \forall o,\, (b_2\,q).\text{val}\,h_2\,o \to (b_1\,q).\text{val}\,h_1\,o$$
  Consequently, proving `(L_v.sem v q₁).defined` (the abstract model `v` has no
  failure) immediately implies `(L_mir.sem s (encodeQuery q₁)).defined` (the
  concrete MIR program `s` has no `.failed .ub` or `.stuck` prefix!). No
  translation into `L_v` is trusted unless accompanied by a kernel-checked proof
  of `Abstracts L_v L_mir codec v s`.

#### F-1.6: Bounded Model Checking Soundness Gaps on Padding, Provenance, and Stubs (`Kani`)

Basis: **documentation** — `model-checking/kani` issues under label
`[F] Soundness`.

- **Historical failure:** `Kani` translates Rust MIR to `Goto-C` programs checked
  by `CBMC`. In `model-checking/kani`'s `[F] Soundness` tracker (which tracks
  false negatives where Kani reports `VERIFICATION:- SUCCESSFUL` on code with UB
  or panics), recurring soundness gaps have included:
  1. **Uninitialized padding bytes:** Copying or transmuting structs with
     uninitialized padding bytes into types requiring initialized bytes (e.g.,
     `zerocopy`-style casts or `transmute`) was not flagged when CBMC's byte
     model initialized local padding to zero or omitted per-byte `Uninit` shadow
     tracking.
  2. **Pointer provenance and aliasing UB:** Because CBMC models pointers as
     `(object_id, offset)` pairs without Stacked/Tree Borrows tags or Rust
     Strict Provenance rules, `unsafe` code that violates mutable aliasing rules
     or casts integers to pointers passes Kani while failing Miri or
     miscompiling under `rustc -O3`.
  3. **Function contract and stub replacement vacuity:** When verifying a caller
     against a stubbed or contracted callee (`#[kani::stub]` /
     `#[kani::requires]`), over-constrained `assume` clauses or incomplete
     havocing of reachable mutable memory allowed callers to pass verification
     while exhibiting UB on real callee behaviors.
- **Technical root cause:** Lowering Rust MIR into a C-level model checker
  (`CBMC`) inherits C's memory abstractions, losing Rust-specific UB conditions
  (uninitialized byte poison, borrow tags, unwind landing pads) and relying on
  unchecked stub instrumentation.
- **Architectural lesson for Anneal (`L_mir` & `StepResult.externalCall`):**
  Anneal's `L_mir` (`SmallStepMachine`) models Rust's byte-level initialization
  (`Uninit` vs. `Init`), pointer provenance (`AllocId`), and borrow tags directly
  in Lean 4, and models stubbed/contracted calls via
  `StepResult.externalCall boundaryInv branches` where `branches : MirState → Prop`
  demonically quantifies over *all* post-states permitted by the callee contract.

#### F-1.7: Dependent Type-Checker and VC Simplifier Empty-Domain Bugs (`F*` `#4478`, `#4485`, `#4487`, `Liquid Haskell` / `Flux`)

Basis: **documentation** — `FStarLang/FStar` issues `#4478`, `#4485`, `#4487`.

- **Historical failure:** Even dependently typed languages and refinement type
  checkers have suffered soundness bugs that prove `False`:
  1. **`F*` VC simplifier uninhabited-type bugs (`FStarLang/FStar#4485`, `#4487`):**
     `F*`'s internal verification-condition simplifier simplified away unused
     quantified variables or function bindings under the implicit assumption that
     every type in the context was inhabited, allowing a user to bind a variable
     of an uninhabited refinement/function type (`squash False` or `unit -> Dv False`)
     and derive `Lemma False`.
  2. **`F*` reflection API round-trip unsoundness (`FStarLang/FStar#4478`):**
     The metaprogramming reflection axiom `inspect_pack_inv` asserted that
     packing and inspecting syntax views was a strict identity even for invalid
     or unsupported universe instantiations (`Tv_UInst` / `Tv_Unsupp`), allowing
     tactics to construct an ill-typed term proving `False`.
  3. **Contradictory refinement preconditions (`Liquid Haskell` / `Flux`):**
     In liquid refinement type systems, if a function's input refinement types
     or assumed measure axioms are mutually contradictory (e.g., `x: usize{x > 10 && x < 5}`),
     every Horn subtyping obligation $\Gamma \wedge \text{pre} \Rightarrow \text{goal}$
     has a false premise and is discharged trivially by the SMT solver.
- **Technical root cause:** Classical first-order logic and SMT solvers assume
  non-empty sorts, whereas dependent and refinement types easily construct empty
  types ($\{x : T \mid \text{False}\}$). Any simplification rule or function
  contract that fails to prove **inhabitation** of its domain risks deriving
  `False` from an empty set.
- **Architectural lesson for Anneal (`InhabitedPre` in `Trusted/Refinement.lean`):**
  Anneal elevates `InhabitedPre pre := ∃ q, pre q` to a first-class primitive in
  `trusted/lean/`. As demonstrated in `support/failure_mechanisms_probe.py`
  (`witness_2`), `L.SpecOn pre post` and `L.ProductiveOn pre prog` both quantify
  universally over `{q | pre q}` and therefore hold vacuously when `pre` is
  contradictory; pairing them with `InhabitedPre pre` forces every verified
  specification to exhibit a concrete input witness $q_0$ satisfying `pre q₀`.

#### F-1.8: Unstructured Control Flow, Abrupt Termination, and Loop Unrolling Gaps (`Frama-C WP`, `KeY`, `ESC/Java2`)

Basis: **documentation** — Frama-C WP Vanadium release notes (`goto` / statement
contract restrictions); Flanagan et al., *ESC/Java2* design documentation.

- **Historical failure:**
  1. **`Frama-C WP` non-natural `goto` loops and statement contracts:** Prior to
     Frama-C 23 (Vanadium), `Frama-C WP`'s weakest-precondition passify/CFG
     reduction assumed natural reducible loops dominated by a single loop header.
     When C programs used `goto` to jump into the middle of a loop or across a
     statement contract, the dominator-tree WP calculation dropped state edges,
     producing unsound verification conditions (forcing Frama-C 23+ to restrict
     non-natural `goto` loops and statement contracts).
  2. **`KeY` and `ESC/Java2` abrupt termination and bounded loop unrolling:**
     `ESC/Java2` intentionally unrolled loops only once ($k = 1.5$ iterations)
     by default, missing any bug that required $\ge 2$ loop iterations, and
     approximated object invariants across exception paths. In `KeY` and early
     JML tools, abrupt termination (`throw`, `break`, `continue`, `return` inside
     `try`/`finally`) repeatedly caused soundness bugs when normal-execution
     postconditions or framing rules were applied to exceptional exit edges.
- **Technical root cause:** Syntax-directed VCGens struggle with unstructured
  control-flow graphs (`goto`, multi-entry loops) and exceptional control flow
  (panics, stack unwinding, `finally` / drop glue) because syntactic substitution
  rules assume structured single-entry/single-exit blocks.
- **Architectural lesson for Anneal (`SmallStepMachine` & `EventualOut`):**
  Anneal's `trusted/lean/` defines program semantics operationally via
  `SmallStepMachine` over `Runtime(PostCleanup)` MIR's unstructured basic-block
  CFG, where `rustc` has already lowered all loops, `break`/`continue`, `?`
  operators, and panic stack unwinding (`UnwindAction` cleanup edges) into
  explicit basic-block transitions, and `EventualOut` distinguishes normal return
  (`Terminal.return`) from panic unwinding (`Terminal.panic`) in its terminal
  outcome type.

---

### 3. Separation Logic, Adequacy, and Aliasing Model Failures

#### F-2.1: Standard-Library Lifetime Variance and Guard Projection Bug (`RustBelt` & `MutexGuard::map`, `rust-lang/rust#25760`)

Basis: **documentation** — Jung, Jourdan, Krebbers, and Dreyer, *"RustBelt:
Securing the Foundations of the Rust Programming Language,"* POPL 2018, DOI
`10.1145/3158154`; `rust-lang/rust#25760`.

- **Historical failure:** While formalizing the semantic type soundness of
  Rust's standard library synchronization primitives in Iris (`RustBelt`, POPL
  2018), Jung et al. discovered a soundness bug in `std::sync::MutexGuard::map`
  (`rust-lang/rust#25760`). `MutexGuard<'a, T>` held a lock on a `Mutex<T>` for
  lifetime `'a`, and `MutexGuard::map` took a closure `F: FnOnce(&mut T) -> &mut U`
  to project the guard to a subfield `MutexGuard<'a, U>`. Because `MutexGuard<'a, T>`
  contained a raw pointer `*mut T` (or `&'a Mutex<T>`) without a phantom
  invariant marker on `T`, `rustc` inferred `MutexGuard<'a, T>` to be
  **covariant** in `T`! A safe caller could therefore obtain a
  `MutexGuard<'a, &'static str>`, coerce it via covariance to
  `MutexGuard<'a, &'short str>`, overwrite the protected reference with a
  short-lived `'short` reference while holding the lock, and unlock the mutex—leaving
  a dangling `'short` reference inside the `'static` `Mutex`!
- **Technical root cause:** Syntactic variance inference in `rustc` inspects
  only the structural field types of an ADT (`*const T` is covariant, `*mut T` /
  `&mut T` is invariant). When an `unsafe` abstraction wraps a shared reference
  `&'a Mutex<T>` or raw pointer to provide mutable access (`DerefMut`), omitting
  `PhantomData<&'a mut T>` silently makes the wrapper covariant in `T`, breaking
  the semantic invariant of exclusive mutable ownership.
- **Architectural lesson for Anneal (`AdtInv` & `VerificationResult`):**
  In Anneal (UC-6.4), a module's representation invariant `AdtInv(ty, val, state)`
  is defined semantically over `L_mir` heap states rather than trusting
  syntactic variance annotations. If a safe public function accepts or returns a
  projected guard after lifetime coercion, the proof of `L_mir.sem m ≤ L_mir.SpecOn pre_AdtInv post_AdtInv`
  must show that `post_AdtInv` holds for all values permitted by the coerced
  type signature, immediately exposing any variance-enabled invariant violation.

#### F-2.2: Sequential-Consistency Adequacy Blind Spot (`RustBelt Meets Relaxed Memory` & `Arc::get_mut`, `rust-lang/rust#51780`)

Basis: **documentation** — Dang, Jourdan, Kaiser, and Dreyer, *"RustBelt Meets
Relaxed Memory,"* POPL 2020, DOI `10.1145/3371102`; `rust-lang/rust#51780`.

- **Historical failure:** The original POPL 2018 `RustBelt` mechanized proof
  verified `std::sync::Arc<T>` under a **sequentially consistent (SC)**
  operational semantics and pronounced `Arc` sound. When Dang et al. (POPL 2020)
  ported the `Arc` proof to `iRC11` (an Iris separation logic over the C++11 /
  Rust relaxed-memory model), the proof of `Arc::get_mut` **failed**, uncovering
  a real data-race soundness bug in the Rust standard library
  (`rust-lang/rust#51780`). Specifically:
  - `Arc::get_mut(&mut self) -> Option<&mut T>` checks that both the strong
    reference count is 1 and the weak reference count is 1 before granting
    exclusive `&mut T` access to the payload.
  - To prevent a concurrent `Weak::upgrade` from racing, `Arc::get_mut` used
    `compare_exchange(..., Acquire, Relaxed)` to lock the strong count, and then
    read the weak count using `Ordering::Relaxed`!
  - Under C-2011 relaxed memory, when another thread dropped the last `Weak<T>`
    pointer, its prior read-only inspections of the `Arc` inner structure were
    only synchronized with `Release` on the weak count decrement. Because
    `Arc::get_mut` read the weak count with `Relaxed` instead of `Acquire`, no
    happens-before edge was established between operations before `Weak::drop`
    and the subsequent mutable write through `Arc::get_mut`—causing a C-2011 data
    race (immediate UB)!
- **Technical root cause:** A formal verification proof is only as strong as the
  operational machine semantics underneath its adequacy theorem. Assuming
  sequential consistency in the operational semantics hid a weak-memory
  synchronization bug (`Relaxed` vs. `Acquire`) in code whose entire purpose is
  concurrent reference counting.
- **Architectural lesson for Anneal (`Language SemObs` & `SmallStepMachine`):**
  Anneal does not hardcode a single sequentially consistent memory model into
  `trusted/lean/`'s core `Language` primitive. Instead, `Language SemObs` and
  `SmallStepMachine` are parameterized over `State`, allowing `theory/` to
  instantiate weak-memory operational models (`C11PromisingAxiomatic` in UC-5.5,
  `X86TSOBufferSim` in UC-5.6, `ArmRiscvPopModel` in UC-5.7) and verify
  concurrent primitives like `Arc` against weak-memory transitions without
  altering `trusted/lean/`.

#### F-2.3: Mid-Method Broken `AdtInv`, Callback Re-Entrancy, and Unwind Safety (`Vec::dedup_by`, `BinaryHeap`, `RefCell`)

Basis: **documentation** + **execution** — Rust standard-library panic-safety
and unwind-safety advisories (`Vec::dedup_by`, `BinaryHeap` hole-filling
patterns, `RustSec` container unwind bugs); `support/failure_mechanisms_probe.py`
(`witness_4`).

- **Historical failure:** A pervasive bug class in unsafe Rust collections
  (`std::vec::Vec::dedup_by`, `Vec::retain`, `BinaryHeap::sift_up` / `rebuild`,
  and third-party arena/vector crates) occurs when a method:
  1. Temporarily moves an element out of an array slot `ptr.add(i).read()`
     (leaving an uninitialized hole inside `0..self.len` and temporarily
     breaking `AdtInv`),
  2. Invokes a user-supplied closure `same_bucket(&mut a, &mut b)` or `Ord::cmp`
     while `self.len` still covers the uninitialized slot, and
  3. Plans to shift the remaining elements and update `self.len` *after* the
     closure returns.
  If the user closure **panics** (triggering stack unwinding), `Vec::drop` runs
  during unwinding while `self.len` still includes the uninitialized hole,
  causing `Drop::drop` to dereference uninitialized/moved memory (double-free /
  UB)! Even without panicking, if the user closure **re-enters** the data
  structure through a shared reference (`RefCell` / global / thread-local), it
  observes the broken `AdtInv` in the middle of the operation.
- **Technical root cause:** Deductive verifiers that check type invariants
  (`AdtInv`) only at function entry and normal function return (`return`
  postconditions) miss two critical intermediate observation points:
  1. **Open-world external call boundaries** where control leaves the current
     module while `AdtInv` is suspended, and
  2. **Exceptional unwind edges** (`UnwindAction::Cleanup`) where destructors
     run on partially mutated state.
- **Architectural lesson for Anneal (`StepResult.externalCall` & `Terminal.panic`):**
  Anneal catches both failure paths structurally (verified in `witness_4` of
  `support/failure_mechanisms_probe.py`):
  1. `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop)`
     evaluates `boundaryInv` **at the exact step the closure/trait call is
     invoked** and transitions immediately to `.failed .ub` (`defined = False`)
     if `boundaryInv = false`. Encoding `AdtInv` into `boundaryInv` forces the
     collection method (e.g., via a `Drop` guard struct that tracks the hole gap
     and sets `self.len = 0` or repairs the gap before calling out) to maintain
     a valid invariant at every callback!
  2. `EventualOut.terminated trace (term : Terminal Val)` explicitly includes
     both normal return (`Terminal.return`) and unwinding panic
     (`Terminal.panic`), so `SpecOn pre post_AdtInv` checks that `AdtInv` holds
     along `Runtime(PostCleanup)` MIR unwind edges as well.

#### F-2.4: Stacked Borrows Incompatibilities with Idiomatic Unsafe Rust vs. Tree Borrows (`POPL 2020` → `PLDI 2025`)

Basis: **documentation** + **execution** — Jung, Dang, Kang, and Dreyer,
*"Stacked Borrows: An Aliasing Model for Rust,"* POPL 2020, DOI
`10.1145/3371109`; Villani, Hostert, Dreyer, and Jung, *"Tree Borrows,"* PLDI
2025, DOI `10.1145/3729338`; `support/failure_mechanisms_probe.py` (`witness_5`).

- **Historical failure:** `Stacked Borrows` (POPL 2020) was the first formal
  operational aliasing model for Rust implemented in Miri. It modeled per-byte
  aliasing permissions as a linear stack of borrow tags (`Unique`,
  `SharedReadWrite`, `SharedReadOnly`), where any read through a parent tag
  `t_parent` popped all `Unique` tags above `t_parent` off the stack, and any
  write popped all tags above `t_parent`. When tested at scale against the
  Crates.io ecosystem and the Rust standard library, Stacked Borrows exhibited
  four severe **model-adequacy failures** (rejecting idiomatic, compiler-intended
  Rust patterns as UB):
  1. **Two-phase borrows and read-before-write on `&mut T`:** In safe Rust,
     `v.push(v.len())` desugars in MIR to creating a two-phase mutable borrow
     `tmp = &two_phase mut v` first, then evaluating `v.len()` via a shared
     reborrow of `v`, and finally activating `tmp` inside `Vec::push`. Under
     pure Stacked Borrows (`Unique` on `Retag`), reading `v` for `v.len()`
     popped `tmp`'s `Unique` tag before `push` could use it (`witness_5`)!
     Stacked Borrows had to fall back to a lossy `SharedReadWrite` hack for
     two-phase borrows that forfeited optimizations.
  2. **Over-eager array/struct subobject over-invalidation (`addr_of!` /
     `container_of`):** In Stacked Borrows, creating a reference `&mut s.field_a`
     and casting it to a raw pointer restricted the tag's spatial range strictly
     to `field_a` (unless `-Zmiri-tag-raw-pointers` compromises were used),
     breaking intrusive linked-list `container_of!` offset patterns where a raw
     pointer derived from a field reference accesses the enclosing struct.
  3. **Eager non-aliasing on untouched `&mut T`:** Passing an unused `&mut T`
     reference alongside a raw pointer that is only *read* invalidated the
     `&mut T` even if the `&mut T` was never written to during the call.
  4. **`Pin<&mut T>` and self-referential futures:** Polling a self-referential
     `async` state machine through `Pin::new_unchecked(&mut fut)` invalidated
     internal self-pointers stored inside `fut` under Stacked Borrows' strict
     stack pop rule.
- **Technical root cause:** A linear stack per byte confuses *temporal creation
  order* with *logical derivation hierarchy*, and treats the mere creation of a
  `&mut T` (`Retag`) as an immediate write rather than a **lazy reservation**
  that becomes exclusive only when first written. That forced Villani et al.
  (PLDI 2025) to replace Stacked Borrows with **Tree Borrows**, which:
  - Organizes tags into a **tree** (where sibling branches can be disabled
    without popping parent/ancestor branches), and
  - Replaces `Unique` with a lazy state machine `Reserved → Active → Frozen → Disabled`
    where a newly created `&mut T` starts in `Reserved` (tolerating foreign
    reads!) and transitions to `Active` only on its first child write (cutting
    ecosystem test rejections by ~54%).
- **Architectural lesson for Anneal (`L_mir` & `Compiles L_sb L_tb`):**
  1. Anneal's `L_mir` aliasing semantics in `trusted/` (or in `theory/` modular
     refinements per UC-3.1) should use `Tree Borrows`'s lazy
     `Reserved → Active → Frozen → Disabled` state machine (or support
     parameterizing the borrow-tag state machine) rather than hardcoding
     Stacked Borrows' eager stack pop into the TCB.
  2. Because `Compiles L_sb L_tb codec f f` is expressible directly in Anneal's
     `Language` refinement calculus, proofs conducted under a stricter aliasing
     discipline (or untagged memory `L_untagged` via `Abstracts L_untagged L_mir_tb`)
     compose cleanly without redoing the TCB.

#### F-2.5: Tree Borrows Function-Entry `Protector` Subtleties Across External Calls and `UnsafeCell`

Basis: **documentation** — Villani et al., *"Tree Borrows,"* PLDI 2025, DOI
`10.1145/3729338`; `simuliris-tree-borrows-selected-kernel-replay-e3abfcdc`
corpus report.

- **Historical failure:** During the design of `Tree Borrows`, making `&mut T`
  start in `Reserved` (tolerating foreign reads before the first write) created
  a subtle **compiler optimization soundness trap**: LLVM's `noalias` attribute
  on a function parameter `x: &mut T` allows the compiler to reorder or delete
  reads and writes through `x` across an opaque function call `opaque_cb()` inside
  the function body, *even if `x` was only `Reserved` (never written) in the
  source program*! If `opaque_cb()` were allowed to write to the memory of `x`
  via a parent pointer and merely transition `x` from `Reserved` to `Disabled`
  (without triggering UB because `x` is never used again), LLVM's upward motion
  of a write or load to `x` across `opaque_cb()` would be unsound! Furthermore,
  if `T` contains an `UnsafeCell`, `Reserved` behaves differently (`ReservedIM`)
  because interior mutability permits shared writes when not protected.
- **Technical root cause:** Function-argument references carry a stronger
  aliasing contract than local reborrows: a function-entry tag must remain valid
  (not `Disabled`) **for the entire duration of the function call**, even if the
  reference is never dereferenced again after an intermediate callback. Tree
  Borrows models this via a call-frame **`Protector`** attached on
  `RetagKind::FnEntry`: transitioning a *protected* tag to `Disabled` is
  **immediate UB** at the moment of the conflicting access!
- **Architectural lesson for Anneal (`StepResult.externalCall` & Call-Frame Protectors):**
  As identified in UC-3.1, when `SmallStepMachine` steps across an external or
  indirect call via `StepResult.externalCall boundaryInv branches`, active
  `Protector` tags from enclosing call frames must be enforced by `boundaryInv`
  and preserved by `branches : State → Prop`. Any external callback branch that
  would transition an active protected tag to `Disabled` must step to `.failed .ub`.

#### F-2.6: `rustc` Borrow Checker Soundness Holes (`#25860` Implied Bounds + Variance + HRTB, `#84591`, `#100013`)

Basis: **documentation** — `rust-lang/rust` issues `#25860`, `#84591`, `#100013`;
Rust Compiler Development Guide (*Implied Bounds* and *Higher-Ranked Trait
Bounds*).

- **Historical failure:** Opened in May 2015 and remaining open for over a
  decade, **`rust-lang/rust#25860`** (*"Implied bounds on nested references +
  variance = soundness hole"*) allows 100% safe Rust code (`#![forbid(unsafe_code)]`)
  to transmute a short-lived reference `&'a T` into `&'static T`, causing a
  use-after-free segfault:
  - In Rust, writing a function signature `fn helper<'a, 'b>(x: &'a &'b (), y: &'b str) -> &'a str { y }`
    requires no explicit `where 'b: 'a` clause because `rustc` assumes the
    **implied bound** `'b: 'a` from the well-formedness of the argument type
    `&'a &'b ()`.
  - Consequently, the function pointer type `for<'a> fn(&'a &'b (), &'b str) -> &'a str`
    is accepted as well-formed without checking `'b: 'a` at the call site until
    the function is called.
  - Using contravariance of function arguments (`fn(T)`) combined with
    higher-ranked lifetime binders (`for<'a>`), safe code can coerce that
    function pointer into a type where the nested reference `&'a &'b ()` is
    abstracted behind a trait projection or contravariant parameter, and then
    call it with `'a = 'static` and a short-lived `'b` **without ever
    constructing a value of type `&'static &'b ()`**!
  - Sibling soundness holes (`rust-lang/rust#84591` on supertrait upcasting with
    HRTBs and `#100013` / Polonius loan-invalidation interactions with HRTBs)
    exploit the same structural flaw: `rustc`'s trait and borrow checkers assume
    implied bounds from binder parameters without proving those bounds at binder
    instantiation sites.
- **Technical root cause:** `rustc`'s static type and borrow checker is **not
  currently sound** in the presence of higher-ranked trait bounds, implied
  bounds, and variance. Any verification tool (`Electrolysis`, `Aeneas`,
  `RustHorn`, `Creusot`, `Verus`) that treats `rustc`'s borrow checker as an
  unquestioned oracle guaranteeing memory disjointness and lifetime validity on
  safe Rust inherits `#25860` and `#84591` as soundness holes!
- **Architectural lesson for Anneal (`L_mir` & Certifying Polonius Checker UC-3.2):**
  Anneal's `trusted/lean/` **does not axiomatize `rustc` type/borrow checking as
  a proof of UB freedom**. Instead, `Trusted.CrateTheorem` is defined over
  `L_mir`'s concrete operational semantics (`SmallStepMachine`), where
  dereferencing a dangling allocation (`StorageDead` / freed `AllocId`) is
  dynamic `.failed .ub`. When a functional translator (UC-1.1) or borrow-erasure
  pass (UC-3.1/UC-3.2) relies on lifetime disjointness, that disjointness must
  be discharged in `theory/` via a kernel-checked Polonius/borrow certificate or
  dynamic region check, which fails closed if an implied bound `'b: 'a` is
  missing!

#### F-2.7: Pointer-Integer Cast Provenance Paradoxes (`llvm#34548`, `llvm#35229`, `PNVI` vs. Strict/Exposed Provenance)

Basis: **documentation** — Lee et al., *"Taming Undefined Behavior in LLVM,"*
PLDI 2017, DOI `10.1145/3062341.3062343`; Kang et al., *"Reconciling High-Level
Optimizations and Low-Level Code in LLVM,"* OOPSLA 2018, DOI `10.1145/3276495`;
LLVM bugs `#34548` and `#35229`.

- **Historical failure:** In C, C++, and Rust (`llvm#34548`, `llvm#35229`), a
  classic three-step optimization sequence in LLVM miscompiled valid programs
  that cast pointers to integers and back:
  1. Suppose allocation $p$ ends at address `0x1000` (one-past-the-end pointer
     `p_end = p + n` has numeric address `0x1000` and provenance `Alloc(p)`) and
     allocation $q$ begins immediately at address `0x1000` (`q` has numeric
     address `0x1000` and provenance `Alloc(q)`).
  2. The program casts both to integers (`ip = (uintptr_t)p_end`,
     `iq = (uintptr_t)q`), branches on `if (ip == iq)`, and inside the branch
     computes `q2 = (int*)iq` and writes `*q2 = 42`.
  3. **Pass 1 (GVN on integers):** Inside `if (ip == iq)`, Global Value
     Numbering replaces `iq` with `ip`, turning `q2 = (int*)iq` into
     `q2 = (int*)((uintptr_t)p_end)`.
  4. **Pass 2 (`InstCombine` round-trip fold `inttoptr(ptrtoint(x)) -> x`):**
     `InstCombine` folds `(int*)((uintptr_t)p_end)` to `p_end`!
  5. **Pass 3 (Alias Analysis + Dead Store Elimination):** Because `p_end` has
     provenance `Alloc(p)` (and is out-of-bounds for writing to $q$), LLVM
     concludes `*p_end = 42` is UB / cannot alias reads from `q`, and deletes
     the store `*q2 = 42`!
- **Technical root cause:** Three seemingly natural rules—(a) integer GVN
  (`ip == iq` allows substituting `ip` for `iq`), (b) round-trip pointer-integer
  cast elimination (`inttoptr(ptrtoint(x)) -> x`), and (c) provenance-based
  alias analysis (`p + n` cannot access `q`)—are **mutually inconsistent**!
  Furthermore, in C/Rust's `PNVI-ae-udi` (Exposed Provenance) model,
  `with_exposed_provenance(addr)` is often specified via *angelic
  nondeterminism* (guessing whether `0x1000` has provenance `Alloc(p)` or
  `Alloc(q)`), which breaks demonic refinement calculi (`Behavior Query Out`).
- **Architectural lesson for Anneal (`L_mir` & Sub-Domain 1 UC-3.3):**
  1. Anneal's `L_mir` keeps pointer provenance (`AllocId`) distinct from pure
     `BitVec` integers (`ptrtoint` strips `AllocId`, so `inttoptr(ptrtoint(x))`
     is *not* definitionally equal to `x`; Strict Provenance `ptr.with_addr` /
     `ptr.map_addr` preserves `AllocId` explicitly).
  2. Because `Behavior Query Out` uses **demonic** nondeterminism (`≤` requires
     all branches to be UB-free), modeling `with_exposed_provenance(addr)` as a
     demonic choice over all exposed `AllocId`s would falsely trigger UB whenever
     $\ge 2$ allocations are exposed! Instead, `L_mir` resolves exposed
     provenance deterministically to the unique live allocation whose interior
     byte range $[base, base + size)$ contains `addr` (or prevents adjacent
     allocations from sharing interior addresses).

---

### 4. Abstract Interpretation and Static Analyzer Soundness Bugs

#### F-3.1: Linux Kernel eBPF Verifier `BPF_JMP32` 32-Bit Branch Bounds Refinement Bug (`CVE-2020-8835`, `torvalds/linux@581738a681b6`)

Basis: **source** + **documentation** — `torvalds/linux` commit
`581738a681b6faae5725c2555439189ca81c0f1f` (and fix commit `3f50f132d840`); NVD
`CVE-2020-8835`.

- **Historical failure:** The Linux kernel eBPF verifier (`kernel/bpf/verifier.c`)
  is an in-kernel abstract interpreter that tracks each 64-bit register `r0..r10`
  using a reduced product of five abstract domains: 64-bit unsigned intervals
  `[umin_value, umax_value]`, 64-bit signed intervals `[smin_value, smax_value]`,
  32-bit unsigned intervals `[u32_min_value, u32_max_value]`, 32-bit signed
  intervals `[s32_min_value, s32_max_value]`, and a 64-bit tristate known-bits
  domain `var_off : tnum` (`(value, mask)` where `value & mask == 0`). In
  `CVE-2020-8835` (exploited at Pwn2Own 2020 for root local privilege
  escalation), commit `581738a681b6` added `__reg_bound_offset32` to synchronize
  32-bit bounds into `var_off` (`tnum`) after 32-bit conditional branches
  (`BPF_JMP32`), but used 64-bit `umin_value`/`umax_value` instead of
  `u32_min_value`/`u32_max_value` when intersecting `tnum` subregister masks. By
  crafting a register whose 64-bit bounds and 32-bit bounds diverged across a
  32-bit branch, an attacker forced the verifier to infer that a register equal
  to `1` at runtime was statically equal to `0`, bypassing array bounds checks
  and achieving arbitrary kernel read/write.
- **Technical root cause:** Hand-written cross-domain reduction routines
  (`__reg_bound_offset32`, `__reg_combine_64_into_32`, `reg_bounds_sync`) that
  mutually refine 5 coupled abstract domains without a mechanized proof of the
  concretization invariant $\gamma_{\text{64}} \cap \gamma_{\text{32}} \cap
  \gamma_{\text{tnum}}$ are extraordinarily error-prone: a single typo mixing a
  64-bit field with a 32-bit field collapses the abstract state to a wrong
  singleton constant.
- **Architectural lesson for Anneal (Certifying Abstract Domains UC-5.1 & UC-5.2):**
  In Anneal, abstract interpretation never runs inside `trusted/`. Instead, the
  concretization function $\gamma : \text{AbstractReg} \to (\text{BitVec 64} \to \text{Prop})$
  and every cross-domain reduction operator `syncBounds# : AbstractReg → AbstractReg`
  reside in `theory/` and must carry a Lean kernel proof (discharged via
  `bv_decide`) that $\forall x : \text{BitVec 64},\, \gamma(a)(x) \to \gamma(\text{syncBounds}^{\#}(a))(x)$.

#### F-3.2: Linux Kernel eBPF Verifier `tnum` Bitwise ALU32 Subregister Bounds Bug (`CVE-2021-3490`, `torvalds/linux@049c4e13714e`)

Basis: **source** + **documentation** — `torvalds/linux` commit
`049c4e13714ea026ddfb62fc726fb0e3f22c2861`; NVD `CVE-2021-3490`.

- **Historical failure:** In `CVE-2021-3490`, the eBPF verifier's 32-bit bitwise
  abstract transfer functions `scalar32_min_max_and`, `scalar32_min_max_or`, and
  `scalar32_min_max_xor` in `kernel/bpf/verifier.c` contained an early return:
  when both operands had known 32-bit constants according to `tnum_subreg_is_const(src_reg->var_off)`
  and `dst_reg->subreg_def`, the functions returned early without updating
  `s32_min_value`, `s32_max_value`, `u32_min_value`, and `u32_max_value` (relying
  on a later `reg_bounds_sync` call to infer the 32-bit bounds from `var_off`).
  However, because the prior `u32_min_value` and `u32_max_value` were left stale
  before `reg_bounds_sync` intersected them with the new `var_off` bounds, the
  intersection of the stale interval with the new bitwise result produced an
  inverted interval `u32_min_value > u32_max_value` (e.g., `u32_min_value = 1,
  u32_max_value = 0`), which subsequent pointer arithmetic trusted to perform
  out-of-bounds kernel memory writes.
- **Technical root cause:** Confusing **domain refinement (intersection)** with
  **state update (destructive assignment)** during a mutable transfer step:
  `reg_bounds_sync` assumes the existing `[u32_min, u32_max]` interval is already
  a sound over-approximation of the *new* register value and narrows it against
  `var_off`. Leaving the *pre-operation* interval in `[u32_min, u32_max]` and
  intersecting it with the *post-operation* `var_off` computed $I_{\text{pre}}
  \cap \gamma_{\text{tnum}}(v_{\text{post}}) = \emptyset$!
- **Architectural lesson for Anneal (`ProductiveOn` & Functional Transfer Proof in `theory/`):**
  1. In pure functional Lean (`theory/`), abstract transfer functions return a
     fresh `AbstractVal` rather than mutating fields in place and intersecting
     stale pre-state bounds with post-state `tnum` masks.
  2. Furthermore, an inverted interval (`u32_min > u32_max`) has an empty
     concretization $\gamma(a) = \emptyset$, which is the abstract-interpretation
     analog of a demonic miracle (`witness_1` / `witness_6`) and is immediately
     caught when proving transfer soundness on inhabited concrete states.

#### F-3.3: Linux Kernel eBPF Verifier 64-to-32-Bit Endpoint Truncation Bug (`CVE-2021-31440`, `torvalds/linux@10bf4e83167c`)

Basis: **source** + **execution** — `torvalds/linux` commit
`10bf4e83167cc68595b85fd73bb91e8f2c086e36`; NVD `CVE-2021-31440`;
`support/failure_mechanisms_probe.py` (`witness_6`).

- **Historical failure:** In `CVE-2021-31440`, the helper
  `__reg_combine_64_into_32(struct bpf_reg_state *reg)` attempted to tighten
  32-bit bounds `[u32_min_value, u32_max_value]` from 64-bit bounds
  `[umin_value, umax_value]`. It checked whether the lower 32 bits of
  `umin_value` and `umax_value` satisfied boundary conditions independently,
  rather than checking whether `umin_value` and `umax_value` shared the **same
  upper 32 bits** (`(umin_value >> 32) == (umax_value >> 32)`). As reproduced in
  `witness_6` (`support/failure_mechanisms_probe.py`), when a 64-bit register
  had bounds `[0x0_ffffffff, 0x1_00000000]` (straddling the $2^{32}$ boundary),
  the concrete low-32-bit values are $\{0\text{xffffffff}, 0\text{x00000000}\}$,
  which wrap around $2^{32}$! Projecting without the upper-32-bit equality check
  caused the verifier to miscalculate 32-bit bounds as a tight constant `0` or
  inverted range after a 32-bit ALU operation.
- **Technical root cause:** Modular wrap-around on subregister projection: the
  map $x \mapsto x \bmod 2^{32}$ is monotonic on an interval $[a, b] \subseteq
  [0, 2^{64}-1]$ **if and only if** $\lfloor a / 2^{32} \rfloor = \lfloor b /
  2^{32} \rfloor$.
- **Architectural lesson for Anneal (`bv_decide` Domain Verification in `theory/`):**
  When verifying the 32-bit projection operator in `theory/` via Lean 4's
  `bv_decide`, omitting the guard `(umin >>> 32) == (umax >>> 32)` immediately
  fails kernel checking and produces the exact counterexample `umin = 0xffffffff,
  umax = 0x100000000`.

#### F-3.4: Linux Kernel eBPF Verifier Nullable Pointer (`*_OR_NULL`) Arithmetic Bypass (`CVE-2022-23222`, `torvalds/linux@64620e0a1e71`)

Basis: **source** + **documentation** — `torvalds/linux` commit
`64620e0a1e712a778095bd35cbb277dc2259281f`; NVD `CVE-2022-23222`.

- **Historical failure:** In `CVE-2022-23222`, `adjust_ptr_min_max_vals` in
  `kernel/bpf/verifier.c` permitted pointer arithmetic (`BPF_ADD` / `BPF_SUB`)
  on registers carrying nullable pointer types (`PTR_TO_MEM_OR_NULL`,
  `PTR_TO_BTF_ID_OR_NULL`, `PTR_TO_SOCKET_OR_NULL`) *before* the pointer was
  checked for `NULL`. When the user program added a known offset `0` (or
  non-zero offset) to a `*_OR_NULL` pointer and then branched on `if (ptr == 0)`
  to convert the register into a known scalar `0`, the verifier's pointer-offset
  tracking corrupted the scalar range bounds, allowing arbitrary out-of-bounds
  pointer arithmetic.
- **Technical root cause:** Conflating a sum type $\text{Option}(\text{Ptr}) =
  \text{None} \mid \text{Some}(\text{AllocId}, \text{Offset})$ with a single
  pointer record whose base might be zero, and allowing offset arithmetic before
  case-splitting on the `Option` tag.
- **Architectural lesson for Anneal (`L_mir` Memory & Provenance Model):**
  In Anneal's `L_mir`, a valid pointer carries ` some allocId : Option AllocId`,
  whereas a null pointer has `allocId = none`. In `SmallStepMachine`, performing
  in-bounds pointer offset arithmetic (`PtrOffset` / `GEP`) on a pointer with
  `allocId = none` (for non-zero offset) steps immediately to `.failed .ub`.

#### F-3.5: Linux Kernel eBPF Verifier CFG State-Pruning Precision Backpropagation Bug (`CVE-2023-2163`, `torvalds/linux@71b547f56124`)

Basis: **source** + **documentation** — `torvalds/linux` commit
`71b547f561247897a0a14f3082730156c0533fed`; NVD `CVE-2023-2163`.

- **Historical failure:** To avoid exponential path explosion on large eBPF
  programs, the eBPF verifier performs **state pruning** (`is_state_visited` /
  `states_equal`): if the current abstract state $S_{\text{cur}}$ at a CFG join
  point is subsumed by a previously verified state $S_{\text{old}}$ on all
  registers marked `precise = true`, the verifier prunes the path. To know which
  registers must be tracked precisely, `mark_chain_precision` /
  `propagate_precision` walks backward along the explored execution history
  whenever a register is used in a sensitive sink (like packet/map pointer
  indexing). In `CVE-2023-2163`, `propagate_precision` failed to walk backward
  correctly across certain conditional branch / subprog jump histories, leaving
  a critical scalar register marked `precise = false` in $S_{\text{old}}$. When
  a later path arrived with an out-of-bounds value in that register,
  `states_equal` ignored the register (because `precise == false` in
  $S_{\text{old}}$) and pruned the unsafe path as "already verified"!
- **Technical root cause:** Dynamic backward precision tainting coupled with
  state-equivalence pruning is a fragile global optimization: if the backward
  walk misses *any* predecessor edge in the CFG, `states_equal` treats an
  unconstrained $\top$ bound as equivalent to a verified bound, creating an
  immediate soundness hole.
- **Architectural lesson for Anneal (Certifying Post-Fixpoint Checkers UC-5.1):**
  Anneal completely decouples *fixpoint search/pruning* (done by an untrusted
  external analyzer) from *fixpoint verification* (done by `checkNumFixpoint` in
  `theory/`). The untrusted analyzer can use whatever heuristic state pruning or
  precision tainting it likes; it must emit an explicit invariant table
  `inv : BasicBlockId → AbstractVal` to `theory/`, where `checkNumFixpoint`
  locally verifies $F^{\#}(\text{inv}[bb]) \sqsubseteq^{\#} \text{inv}[bb']$ on
  **every** CFG edge $(bb, bb')$ and verifies that $\text{inv}[bb]$ discharges
  all UB guards inside $bb$. If pruning dropped a precision bit needed at a downstream
  sink, the local check at that sink or join edge fails closed in the Lean
  kernel!

#### F-3.6: Automated Discovery of Unsound Kernel `tnum` Abstract Operators (`Agni`, CGO 2022 & CAV 2023)

Basis: **documentation** — Vishwanathan et al., *"Sound, Precise, and Fast
Abstract Interpretation with Tristate Numbers,"* CGO 2022, DOI
`10.1109/CGO53902.2022.9741267`; Vishwanathan et al., *"Verifying the Verifier:
eBPF Range Analysis Verification,"* CAV 2023, DOI
`10.1007/978-3-031-37709-9_12`.

- **Historical failure:** When Vishwanathan et al. built **Agni** to extract the
  Linux kernel's C range-analysis and `tnum` operators into SMT bitvector
  formulas and verify their soundness across kernel versions 4.14 through 5.19,
  they discovered multiple previously unknown soundness bugs and precision
  anomalies in `tnum_mul` (tristate multiplication), `scalar_min_max_and`,
  `scalar_min_max_or`, `scalar_min_max_xor`, and 32/64-bit synchronization
  routines where the kernel's abstract output violated the Galois/concretization
  soundness condition $\forall x \in \gamma(a),\, y \in \gamma(b) \implies
  (x \oplus y) \in \gamma(a \oplus^{\#} b)$.
- **Technical root cause:** Implementing bit-level abstract transformers in C
  without mechanized bitvector verification against the concrete ALU semantics
  inevitably introduces sign-extension, overflow, and bitmask propagation bugs.
- **Architectural lesson for Anneal (`bv_decide` Constructive Domain Proofs):**
  As designed in UC-5.2, Anneal's `KnownBits` (`tnum`) and interval abstract
  transformers are written in pure Lean 4 in `theory/` and proved sound once and
  for all against `BitVec 64` operations using `bv_decide` (checked LRAT
  certificates in the Lean kernel), providing permanent immunity against
  `Agni`-class abstract operator bugs.

#### F-3.7: Widening Precision Collapse and Unmodeled Library Stubs (`Astrée`, `Frama-C Eva`, `IKOS`, `MIRAI`)

Basis: **documentation** — Cousot et al., *Astrée* experience reports; NASA
`IKOS` and Frama-C `Eva` documentation; Meta `MIRAI` repository archive.

- **Historical failure:** Industrial abstract interpreters face a dual failure
  mode between **widening precision collapse** (usability failure) and **missing
  library/environment models** (soundness failure):
  1. **Threshold widening collapse (`Astrée`, `Frama-C Eva`, `IKOS`):** To force
     termination on loops, interval/octagon widening $\nabla$ extrapolates
     changing bounds to $\pm \infty$ or fixed thresholds. When a Rust or C loop
     index depends on a dynamic slice length `i < slice.len()` or nonlinear
     stride, non-relational interval widening widens `i` to `[0, +∞]`, causing
     cascade false-positive alarms on every subsequent array access unless
     relational domains (Octagons/Polyhedra) or manual loop unrolling directives
     are supplied.
  2. **Unmodeled standard-library and intrinsic stubs (`MIRAI`, `IKOS`):** Meta's
     `MIRAI` abstract interpreter for Rust MIR (eventually archived) and C++
     uses of `IKOS` suffered soundness gaps whenever an analyzed function called
     an unmodeled `core`/`std` intrinsic or trait method whose default fallback
     summary under-approximated heap mutations or assumed normal return without
     panicking.
- **Architectural lesson for Anneal (`VerificationResult` + `StepResult.externalCall`):**
  1. Because Anneal's certifying abstract interpreter (UC-5.1) checks
     *Farkas-witnessed relational polyhedra/octagon invariants* emitted by an
     offline solver rather than running fixed widening heuristics inside the
     Lean kernel, precision can be refined offline without touching the TCB.
  2. Any unverified external or `std` callee in `L_mir` steps via
     `StepResult.externalCall boundaryInv branches` (or creates an explicit
     obligation in `VerificationResult`), preventing silent under-approximating
     fallback stubs.

---

### 5. Usability, Proof-Maintenance, and Expressiveness Failures

#### F-4.1: Functional Lens Explosion and Interior-Mutability Expressiveness Wall (`Electrolysis`, Ullrich 2016)

Basis: **documentation** — Ullrich, *"Simple Verification of Rust Programs via
Functional Purification"* (`Electrolysis`), Master's Thesis, Karlsruhe Institute
of Technology (KIT), 2016 (`kha/electrolysis`).

- **Historical failure:** `Electrolysis` was the pioneering translator from Rust
  MIR into pure Lean 2 definitions. It translated mutable references `&mut T`
  into functional **lenses** (`Lens S T` with `get : S → T` and
  `set : S → T → S`). While effective on small functional data structures (like
  binary search trees and `VecDeque`), `Electrolysis` hit three architectural
  walls that led to its abandonment:
  1. **No semantic foundation for `unsafe` or interior mutability:** Because the
     entire target language was pure functional Lean without an underlying
     machine/heap semantics, `Electrolysis` could not verify the actual `unsafe`
     implementations of `Vec<T>`, `Cell<T>`, `RefCell<T>`, `Rc<T>`, or `Arc<T>`;
     those types had to be axiomatized by hand as trusted functional primitives.
  2. **Combinatorial lens explosion on reborrows and struct projections:**
     Functions returning mutable borrows from multiple branches or storing
     mutable borrows inside structs/iterators (`IterMut<'a, T>`) required
     dynamic lens composition whose lens-law proof obligations grew rapidly.
  3. **Unverified direct MIR-to-Lean AST translation:** The Rust-to-Lean
     transpiler was an unverified Rust binary; any bug in how `Electrolysis`
     reconstructed loops or borrow lifetimes silently produced a Lean function
     whose behavior differed from the compiled Rust code.
- **Architectural lesson for Anneal (`L_mir` Base + Certifying `Abstracts L_pure L_mir`):**
  Anneal solves all three problems by making operational `L_mir`
  (`SmallStepMachine`) the ground truth in `trusted/lean/` and treating pure
  functional translation (UC-1.1) as an **upward abstraction (`Abstracts L_pure L_mir codec f_pure f_mir`)
  proved in `theory/`**:
  - When a Rust function is safe and borrow-structured, `Abstracts L_pure L_mir`
    gives the user a pure Lean 4 function `f_pure` to reason about, **backed by
    a machine-checked proof** that `f_mir` refines `f_pure`.
  - When a function uses `unsafe` raw pointers, `UnsafeCell` interior
    mutability, or custom ownership (`Vec`, `Arc`, `GhostCell`), the user proves
    its spec in `theory/` using separation logic (UC-2.1/UC-2.2) or symbolic
    bitvector execution (UC-1.4) over the *exact same* `L_mir` language, and
    safe callers compose with that verified spec seamlessly!

#### F-4.2: Monolithic Viper Encoding Bottlenecks and Proof-Maintenance Collapse (`Prusti` Legacy vs. Rewrite)

Basis: **documentation** — Astrauskas et al., *"Leveraging Rust Types for
Modular Specification and Verification"* (`Prusti`), OOPSLA 2019;
`viperproject/prusti-dev` architecture redesign notes.

- **Historical failure:** Early versions of `Prusti` encoded each Rust MIR
  function—together with all implicit borrow-checker lifetime expiration loans,
  type invariants, and recursive predicate fold/unfold heuristics—into a single
  monolithic `Viper` method verified by `Silicon` (symbolic execution) or
  `Carbon` (Boogie VCGen). On realistic Rust functions with nested branches,
  loops, and trait calls, the automatically inferred `fold`/`unfold` footprint
  heuristics either failed with opaque Viper permission errors that users could
  not map back to Rust source lines, or triggered exponential Z3 branch/quantifier
  timeouts, prompting a major architectural rewrite of `Prusti`.
- **Architectural lesson for Anneal (`VerificationResult` Granular Obligations):**
  Anneal avoids monolithic black-box VC generation: `VerificationResult`
  decomposes verification into fine-grained, span-tagged `Obligation` propositions
  in `theory/`, where decidable sub-goals (bounds, alignment, bitmasks) are
  discharged by fast reflective checkers (`bv_decide`, `omega`, `checkSymHeapCert`)
  and complex algorithmic invariants are proved interactively in Lean 4.

#### F-4.3: Reference-Synthesizing Frontend Rewrites and Silent Partial Extraction (`Aeneas` & `Charon` `#583`, `#534`)

Basis: **source** + **documentation** —
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
`charon/src/options.rs`,
`charon/src/transform/simplify_output/index_to_function_calls.rs`,
`charon-ml/src/OfJson.ml`; Charon issues `#583` and `#534`; corpus report
`charon-support-and-unsoundness`.

- **Historical failure:** As established in our corpus report
  `charon-support-and-unsoundness`, the `Charon` MIR
  extractor (`0.1.210`, pinned by `Aeneas` `nightly-2026.06.03`) exhibits three
  severe frontend-pipeline hazards:
  1. **UB-introducing indexing transformation (`Charon #583`):** `Preset::Aeneas`
     enables `--index-to-function-calls`, which rewrites array/slice place
     indexing `(*raw_ptr)[i]` by synthesizing a shared or mutable reference
     `&(*raw_ptr)[i]` and passing it to a helper function—a transformation whose
     own source comment warns *"may introduce UB"* when indexing behind a raw
     pointer.
  2. **Bound-lifetime erasure in associated-type normalization (`Charon #534`):**
     `expand_associated_types.rs` erases higher-ranked bound lifetimes (`for<'a>`)
     inside associated type equalities (`T: for<'a> Trait<'a, Type = &'a ()>`).
  3. **Fail-open partial extraction (`OfJson.ml`):** By default, `Charon`
     continues after item translation panics/errors, serializes an LLBC JSON
     file with `"has_errors": true` and `Body::Error` placeholders, and exits
     with status `0`, while `Aeneas`'s `charon-ml/src/OfJson.ml` parser discards
     the third JSON field (`has_errors`)!
- **Architectural lesson for Anneal (`trusted/rustc-capture/` & `trusted/audit/`):**
  `anneal-rustc-capture` operates as a fail-closed extractor over
  `Runtime(PostCleanup)` MIR without running reference-synthesizing AST passes,
  and `trusted/cargo-anneal` + `trusted/audit` require `Trusted.CrateTheorem` to
  cover every captured function in the crate without `Body::Error` omissions.

#### F-4.4: Pure Functionalization Boundaries on Raw Pointers and Cyclic/Interior Mutability (`Aeneas` & `RustHorn`)

Basis: **documentation** — Ho and Protzenko, *"Aeneas: Rust Verification by
Functional Translation,"* ICFP 2022, DOI `10.1145/3547647`; Matsushita, Tsukada,
and Kobayashi, *"RustHorn: CHC-Based Verification for Rust Programs,"* TOPLAS
2021.

- **Historical failure:** Both `Aeneas` (backward functions) and `RustHorn`
  (first-order prophecies) rely fundamentally on the invariant that **no two
  live pointers alias the same mutable memory location unless one is a direct
  reborrow of the other**. Consequently, neither technique can directly
  translate:
  - Unsafe raw-pointer graphs (`*mut Node`), doubly-linked lists, or intrusive
    kernel data structures;
  - Shared interior mutability (`UnsafeCell<T>`, `Cell<T>`, `RefCell<T>`,
    `Mutex<T>`, `AtomicUsize`); or
  - Low-level byte-manipulation and zero-copy transmutation (`zerocopy`,
    `MaybeUninit`).
- **Architectural lesson for Anneal (Multi-Modal Composition via `Language SemObs`):**
  Anneal does not force an entire Rust crate through a single verification
  paradigm. Because `Language SemObs` and `BehaviorCodec` provide a uniform
  semantic interface in `trusted/lean/`, a single crate can verify its low-level
  `unsafe` pointer/byte primitives via Iris separation logic (UC-2.1) or
  `bv_decide` symbolic execution (UC-1.4) and expose clean `SpecOn` / `Abstracts`
  summaries that `Aeneas`-style functional translations (UC-1.1) consume for
  high-level algorithmic callers.

#### F-4.5: The SMT "Butterfly Effect," Trigger Matching Loops, and Proof Instability (`IronFleet`, `Dafny`, `Verus`, `Mariposa`)

Basis: **documentation** — Hawblitzel et al., *"IronFleet: Proving Practical
Distributed Systems Correct,"* SOSP 2015, DOI `10.1145/2815400.2815428`; Leino
and Pit-Claudel, *"Trigger Selection Strategies to Stabilize Program Verifiers,"*
CAV 2016, DOI `10.1007/978-3-319-41528-4_20`; Zhou et al., *"Mariposa: Measuring
and Mitigating SMT Instability,"* OOPSLA 2023, DOI `10.1145/3622852`.

- **Historical failure:** Large-scale SMT-based verification projects (`IronFleet`,
  `Komodo`, `VeriBetrKV` in `Dafny`, and systems proofs in `Verus` and `F*`)
  universally report **SMT instability ("the butterfly effect")** as their single
  largest engineering cost:
  - In `IronFleet` (SOSP 2015) and `Dafny` (CAV 2016), renaming a local variable,
    reordering two independent `assert` statements, or upgrading Z3's minor
    version changed hash-table ordering and E-matching quantifier instantiation
    priorities inside Z3, causing proofs that previously succeeded in 1.2
    seconds to time out after 60 seconds (`matching loops`).
  - In `Mariposa` (OOPSLA 2023), testing semantics-preserving mutations
    (variable alpha-renaming, assertion shuffling, random seed permutation)
    across large `Dafny`, `Verus`, `F*`, and `Serval` benchmarks revealed that a
    significant fraction of nontrivial quantified VCs exhibit high variance or
    spurious failure under trivial syntactic perturbations.
- **Technical root cause:** Entrusting proof checking to a time-bounded,
  heuristic SMT search procedure at every compile means a "proof" is not a
  durable mathematical object—it is a fragile coincidence that a heuristic search
  converged within $T$ seconds on a specific machine load and solver binary.
- **Architectural lesson for Anneal (Durable Kernel Certificates in `theory/`):**
  Anneal never runs time-bounded heuristic SMT search inside its trusted
  verification check. When an external solver (`Bitwuzla`, `CaDiCaL`, `cvc5`,
  `Z3`) is used during development, its output is a **static, deterministic
  certificate** (`LRAT` bit-blasting trace, `Alethe` proof DAG, ground
  instantiation witness $\vec{t}_j$, or Farkas multiplier vector $\vec{\lambda}$)
  checked in linear/polynomial time by Lean 4's kernel reducer (`decide` /
  `bv_decide`). Variable renaming or host CPU load cannot cause a checked Lean
  kernel proof or `LRAT` certificate to flip from valid to invalid.

#### F-4.6: Cross-Version Proof Session and Compiler Nightly Drift (`Why3`, `F*`, `Creusot`)

Basis: **documentation** — Bobot et al., *"Preserving User Proofs Across
Specification Changes,"* VSTTE 2013, DOI `10.1007/978-3-642-54108-7_10`; corpus
report `why3-durable-proof-sessions-2011-2025`.

- **Historical failure:** In `Why3` and `Creusot`, user proof sessions are stored
  as XML trees (`why3session.xml`) keyed by VC goal shapes and transformation
  hashes. When `rustc` updates its MIR lowering or `Creusot` adjusts its WhyML
  translation, goal shapes shift across the crate, leaving orphaned proof nodes
  in `why3session.xml` and forcing manual interactive session repair.
- **Architectural lesson for Anneal (`VerificationResult` & Compositional `Abstracts`):**
  By anchoring functional abstractions (`Abstracts L_pure L_mir`) at stable
  function-signature boundaries and discharging low-level MIR stepping via
  automated per-function simulation tactics in `theory/`, user-authored interactive
  Lean 4 theorems reason over the stable pure model `f_pure` rather than brittle
  basic-block numbers in `MirBody`.

---

### 6. Deterministic Mathematical Witnesses for the Six Core Failure Mechanisms

Basis: **execution** — `support/failure_mechanisms_probe.py` and
`support/probe-results.json`.

To make the six cross-cutting failure mechanisms concretely auditable and
reproducible without external solver installations,
`support/failure_mechanisms_probe.py` executes six deterministic finite
models comparing naive verification checks against Anneal's four `trusted/`
primitives:

| Witness ID | Historical Failure Mode Modeled | Naive Verification Gate Result | Anneal `trusted/` Primitive Gate Result | Discriminating Primitive |
| :--- | :--- | :--- | :--- | :--- |
| `witness_1_prophecy_vacuity` | Over-constrained prophecy / demonic miracle (`(sem q).val h = ∅`) proving `ensures false` (F-1.4, F-1.5) | `naive_vc_accepts_ensures_false: true` | `anneal_productive_on_accepts: false` | `L.ProductiveOn pre prog` |
| `witness_2_contradictory_pre` | Contradictory refinement / prelude axiom (`q > 10 ∧ q < 5`) on a UB program (F-1.1, F-1.7) | `spec_on_vacuously_holds: true`, `productive_on_vacuously_holds: true` | `anneal_inhabited_pre_accepts: false` | `InhabitedPre pre` |
| `witness_3_antecedent_waiver` | Waived false lemma (`ob_1 = False`) discharging unwaived buggy check (`ob_2 = False`) via antecedent implication (F-1.4) | `antecedent_waiver_accepts_unwaived_bug: true` | `anneal_positive_verification_result_accepts: false` | `VerificationResult` positive disjunction |
| `witness_4_reentrancy_unwind` | Mid-method broken `AdtInv` (`len = 2 > init = 1`) across callback and unwind path (`Vec::dedup_by`, F-2.3) | `naive_normal_post_only_accepts: true` | `anneal_external_call_boundary_inv_accepts: false`, `anneal_unwind_terminal_check_accepts: false` | `StepResult.externalCall` `boundaryInv` + `Terminal.panic` |
| `witness_5_stacked_vs_tree_borrows` | Two-phase borrow read-before-write (`v.push(v.len())`) under Stacked Borrows vs. Tree Borrows (F-2.4) | `stacked_borrows_accepts_two_phase_pattern: false` (false-positive UB) | `tree_borrows_accepts_two_phase_pattern: true`, `tree_borrows_state_after_conflicting_read: "Disabled"` | `Tree Borrows` `Reserved → Active` transition |
| `witness_6_ebpf_cve_2021_31440` | 64-to-32-bit interval projection on `[0x0_ffffffff, 0x1_00000000]` without upper-32-bit guard (`CVE-2021-31440`, F-3.3) | `buggy_64_to_32_projection_sound: false` | `fixed_64_to_32_projection_sound: true` | `bv_decide` domain soundness theorem |

## Boundaries

### Part I Boundaries — Real-World Verification Tools

- **Known not to apply (Ghost state in `Abstracts` `Query`):** Because
  `BehaviorCodec` requires `decodeQuery (encodeQuery q₁) = q₁`, an upward
  abstraction `Abstracts L_v L_mir codec v s` cannot define `L_v.Query :=
  MirState × GhostState` with `L_mir.Query := MirState` unless `GhostState` is a
  deterministic function of `MirState`. Any non-deterministic ghost state must
  be quantified inside `L_v.sem` or formulated horizontally via `Compiles L_mir L_ghost`.
- **Known not to apply (Many-to-one `decodeOut` over unprojected padding):**
  Because `BehaviorCodec` requires `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`,
  a codec cannot map multiple concrete memory states differing in uninitialized
  struct padding bytes to the same `some o₁` unless `L_mir.Out` projects out
  unobservable padding at function return or `L_v.Out` retains the padding bits
  and erases them in `L_v.obs`.
- **Known not to apply (Demonic `with_exposed_provenance`):** Modeling
  `ptr::with_exposed_provenance(addr)` in `L_mir` as a `StepResult.choice` over
  all previously exposed `AllocId`s is unsound under demonic refinement (`≤`)
  whenever two or more allocations have been exposed.
- **Known not to apply (Fuel exhaustion as `.stuck` in `Abstracts`):** Mapping
  fuel exhaustion in an abstract loop evaluator `L_loop` to `.stuck` or `.failed`
  (`defined = False`) invalidates `Abstracts L_loop L_mir` whenever the concrete
  program runs beyond the fuel bound.
- **Not examined (Full `theory/` implementations of all 24 engines):** While the
  core refinement primitives (`Trusted/Refinement.lean`,
  `Trusted/StepResult.lean`) and representative Lean 4 probes (`Aeneas`/Lithium
  in `rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026`, `bv_decide`
  and `Std.Do` in `lean4-core-tactics-kernel-bvdecide-stddo-and-containers-2026`,
  Tree Borrows in `anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026`,
  and `StepResult.externalCall` re-entrancy in
  `anneal-structural-external-calls-and-tcb-mutation-testing-2026`) have been
  mechanized, full production certificate checkers in `theory/` for `Polonius`
  (`UC-3.2`), `Flux` (`UC-4.1`), `Verasco` Farkas polyhedra (`UC-5.1`), and
  `CeTA` size-change termination (`UC-6.3`) remain future engineering work.
- **Unsupported (`native_decide` in Anneal's TCB):** Tools that rely on
  unverified native code execution in Lean (`Lean.ofReduceBool` via
  `native_decide`) are rejected by Anneal's `.olean` auditor; all reflective
  checkers (`bv_decide` `LRAT`, `checkSymHeapCert`, `checkPolonius`,
  `checkNumFixpoint`) must reduce inside the Lean kernel (`decide`).

### Part II Boundaries — Historical Verification Failures

- **Not examined:** Live execution of historical buggy versions of `Dafny`,
  `Verus`, `Creusot`, `Prusti`, `Kani`, `F*`, or vulnerable Linux kernels
  (`5.5`–`6.3`). All tool bugs and CVEs are established from primary upstream
  commit diffs, CVE records, issue trackers, and peer-reviewed postmortems,
  paired with the self-contained mathematical witnesses in
  `support/failure_mechanisms_probe.py`.
- **Known not to apply:** Anneal's four `trusted/lean/` primitives prevent
  vacuous specifications, antecedent waiver contamination, silent callback
  re-entrancy, and unverified VC/domain lowering only when `L_mir` in
  `trusted/lean/` and `anneal-rustc-capture` faithfully capture the target Rust
  program's operational semantics. A bug inside `trusted/lean/`'s own definition
  of `L_mir` or `anneal-rustc-capture`'s MIR serialization remains inside the
  TCB and must be mitigated via TCB semantic mutation testing (`#228`) and
  differential Miri conformance testing (`#229`).
- **Unsupported:** Treating `rustc`'s built-in borrow checker or type checker as
  an unverified axiom of memory disjointness for arbitrary higher-ranked trait
  bounds (`rust-lang/rust#25860`, `#84591`) without an accompanying `L_mir`
  operational or Polonius certificate check.

## Evidence

### Part I Evidence — Real-World Verification Tools

1. **Anneal `trusted/lean/` Refinement and Small-Step Foundations (`source`):**
   - Repository: `joshlf/anneal`, workspace revision
     `24367bd1a8c784f2578535954f9915e24894a56f` and `trusted/lean`
     revision `24367bd1a8c784f2578535954f9915e24894a56f`.
   - `trusted/lean/Trusted/Refinement.lean:207-473`: `Preorder`, `Partial`,
     `Partial.pure`, `Partial.ub`, `instPreorderPartial`, `Monotone`, `Behavior`,
     `Language`, `Language.SpecOn`, `Language.WellFormedOn`, `Compiles`,
     `Abstracts`, `Compiler`, `VerificationResultOn`.
   - `trusted/lean/Trusted/StepResult.lean:58-200`: `TerminationKind`,
     `StepResult`, `PrefixOutcome`, `ReachesPrefix`, `BehaviorOf`,
     `SmallStepMachine.toLanguage`.
   - Cross-referenced corpus packages (`source` + `execution`):
     `anneal-partial-compile-and-conditioning-refinement-algebra-2026`,
     `anneal-polar-ctfe-admission-and-semantic-polarity-2026`,
     `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`,
     and `anneal-structural-external-calls-and-tcb-mutation-testing-2026`
     (mechanizing `Language SemObs`, `BehaviorCodec`, `ProductiveOn`,
     `InhabitedPre`, positive `VerificationResult`, `EventualBehaviorOf`, and
     `StepResult.externalCall`).

2. **Category A — Functional Translators and Symbolic Evaluators (`source` + `documentation`):**
   - `Aeneas` (`AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`,
     `backends/lean/Aeneas/Std/Primitives.lean`, `Std/WP.lean`, `Tactic/Step/`,
     ICFP 2022 DOI `10.1145/3547647`, ICFP 2024 DOI `10.1145/3674640`) and
     `Charon` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
     v0.1.210).
   - `RustHorn` (TOPLAS 2021 DOI `10.1145/3462205`) and `RustHornBelt` (PLDI 2022
     DOI `10.1145/3519939.3523704`, Zenodo `6417462`).
   - `Creusot` (`creusot-rs/creusot@c4e9770ac1371ac4274bfe02145266d315c2fb86`,
     `creusot/src/backend/place.rs`) and `Coma` (ESOP 2025, sha256
     `a52ad7b745fb8a1d0b54bf52b54f0cfaec18e59f587eda551a54702cf61a8d8e`).
   - `coq-of-rust` / `rocq-of-rust`
     (`formal-land/rocq-of-rust@ca1374ae2fdeb28b069fe77ba412db5604525261`),
     `Electrolysis` (`Kha/electrolysis`, blob
     `670746012e99efc7b239bc5cd41f9ee2d967997b`), and `hax`
     (`cryspen/hax@1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`,
     `Hax/Tactic/HaxMvcgen.lean`).
   - `AutoCorres` (PLDI 2014 DOI `10.1145/2594291.2594296`), `Interaction Trees`
     (`DeepSpec/InteractionTrees@a2bc2c38ad998dccadb932559c922139dd957c4f`, POPL
     2020 DOI `10.1145/3371119`), `Vellvm`
     (`vellvm/vellvm@506f1eb0be542611521985719b971fbce8498dc9`), and `DimSum`
     (POPL 2023 DOI `10.1145/3571220`).
   - `Lean 4 bv_decide` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
     `src/Lean/Elab/Tactic/BVDecide/`), `SAW`
     (`GaloisInc/saw-script@27a7ae98256544b55a7a3ce4ce620c1a7889713b`),
     `Crucible` / `crux-mir`
     (`GaloisInc/crucible@7f49dac06c656f7b92c8b6cc054f47c63b60abe4`), `Kani`
     (`model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`),
     `Rosette` (`emina/rosette@373c8c35e4a7667f38fce10cf0b74ae17de07f1d`, PLDI
     2014 DOI `10.1145/2594291.2594340`), `Serval`
     (`uw-unsat/serval@72adc4952a1e62330aea527214a26bd0c09cbd05`, SOSP 2019 DOI
     `10.1145/3341301.3359641`), `Sail`
     (`rems-project/sail@0f51056900af85d0b18928d6ea2d2271d18184e8`), `Islaris`
     (`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`, PLDI 2022
     DOI `10.1145/3519939.3523434`), and `HolBA`
     (`kth-step/HolBA@ef22c1fd8da612c57f2e7f273cb14594a7e529d3`).

3. **Category B — Separation Logics and Spatial Resource Engines (`source` + `documentation`):**
   - `Iris` (`rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088`, JFP
     2018 DOI `10.1017/S0956796818000151`), `MoSeL` (ICFP 2018 DOI
     `10.1145/3236772`), and `iris-lean`
     (`leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`).
   - `RustBelt` (`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
     POPL 2018 DOI `10.1145/3158154`, POPL 2020 DOI `10.1145/3371102`),
     `RefinedC` (`iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`, PLDI
     2021 DOI `10.1145/3453483.3454036`), `RefinedRust`
     (`lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`, PLDI
     2024 DOI `10.1145/3656423`), and `VST`
     (`PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e`).
   - `CN` and `Fulminate`
     (`rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`, POPL 2023
     DOI `10.1145/3571194`, POPL 2025 DOI `10.1145/3704879`), `VeriFast`
     (`verifast/verifast@0a83dba42db7ce0b445034ece5298afe980e57dc`,
     `arXiv:2601.13727v1`), `Viper`
     (`viperproject/silver@da1c8993b66feb39976e3609e2580a4661137a0f`), `Prusti`
     (`prusti/prusti@0d4a8d497ac1e540d48ef50a031d53b4e3ae36e2`, OOPSLA 2019 DOI
     `10.1145/3360573`), `Gillian-Rust`
     (`GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`,
     PLDI 2025 DOI `10.1145/3729289`), `Infer`/`Pulse`
     (`facebook/infer@5aac32c06952a2f3a6b7043e91457920f065833b`), `VerCors`
     (`utwente-fmt/vercors@3300d5b007286225a33c17a233bda77db9471213`),
     `Steel`/`Pulse` (`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`),
     `GhostCell` (ICFP 2021 DOI `10.1145/3473597`), and `Verus`
     (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`, OOPSLA 2023
     DOI `10.1145/3586037`).

4. **Category C — Aliasing and Borrow Models (`source` + `normative` + `documentation`):**
   - `Miri` (`rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`),
     `Stacked Borrows` (POPL 2020 DOI `10.1145/3371109`), `Tree Borrows` (PLDI
     2025 DOI `10.1145/3735592`), `BorrowSanitizer`
     (`BorrowSanitizer/bsan@a2fd46ab89fc97ba1cf548645dd70acbeaa17d64`),
     `Polonius` (`rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df`),
     `Oxide` (`arXiv:1903.00982v4`), `Aquascope`
     (`cognitive-engineering-lab/aquascope@f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`),
     `VIP` (PLDI 2022 DOI `10.1145/3519939.3523702`), `Quasi-Concrete` (POPL 2015
     DOI `10.1145/2676726.2676985`), `CHERI`/`Morello`
     (`CTSRD-CHERI/sail-morello@2305f656ff84619caf50107f49dae7be52aec72b`),
     `MiniRust` (`minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`),
     and `CompCert Memdata`
     (`AbsInt/CompCert@f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03`).

5. **Categories D, E, and F — Type Systems, Abstract Interpreters, and VCGens (`source` + `documentation`):**
   - `Flux` (`flux-rs/flux@6769bb9cbd1216380f542349494efafafd6104a3`, PLDI 2023
     DOI `10.1145/3591283`), `Liquid Haskell`
     (`ucsd-progsys/liquidhaskell@c0cca0b9f92d8cdaae7f8fc604f78c32b534b69d`,
     ICFP 2014 DOI `10.1145/2628136.2628161`), `Stainless`
     (`EPFL-LARA/stainless@399c34a06df8e88679f0985131e8a59a28ab9b3f`),
     `embedded-hal` (`rust-embedded/embedded-hal@41f29f6bfced1cae0cbe712ba96ee32c075b3125`),
     `embassy` (`embassy-rs/embassy@14cf6a68ec0bfd0ecf873f7e3dbb2eb69013fa29`),
     `Austral` (`austral/austral@0962d2a8a5d77f7daacd7f696819520733f4897d`),
     `Vale` (`project-everest/vale@bbae0eb89143734363b14a77642dbf8dec36e288`),
     `no-panic` (`dtolnay/no-panic@9a0b1097f77dfd5ee4352b6ff060f68d791730f7`),
     `KaRaMeL` (`FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`),
     `Koka` (`koka-lang/koka@d23ee7cd73737c1da7a7a5fa837a2806facc3d6b`), and
     `Effekt` (`effekt-lang/effekt@91c540b1067721bdd1bb5d463e42827f8316a1da`).
   - `Verasco` (POPL 2015 DOI `10.1145/2676726.2676966`), `Astrée` (ESOP 2005 DOI
     `10.1007/978-3-540-31987-0_3`), `Crab`
     (`seahorn/crab@b1eeb1a9402ab0664e962f26f89d923f8514284c`), `SeaHorn`
     (`seahorn/seahorn@892780176731ec8e97bbb9f6b172fcacd77a8ff4`), `IKOS`
     (`NASA-SW-VnV/ikos@ac7f7c1738976cabc58c6a53413df6e458995c38`), `MIRAI`
     (`endorlabs/MIRAI@aae0a56f91d9a0a62073bb86e7b2c9793cefc24b`), `Agni` (CAV
     2023 DOI `10.1007/978-3-031-37709-9_12`), `PREVAIL`
     (`vbpf/prevail@cefe6a799f8b8f37aa2560e196f223802717c1e7`, PLDI 2019 DOI
     `10.1145/3314221.3314590`), `LLVM KnownBits`
     (`llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1`), `Frama-C Eva`
     (`git.frama-c.com/pub/frama-c@ce0648c726122d4a7b5e8614a1a5b97777d9d226`),
     `Goblint` (`goblint/analyzer@1463f411ce87edd49198033856b2946fc3366fb2`),
     `Mopsa` (`mopsa/mopsa-analyzer@f168a9c025738d4940cfb6a281dde258c871da73`),
     `Rudra` (`sslab-gatech/Rudra@fc9add2c4721c77490680462c7f0ad791af7cec7`, SOSP
     2021 DOI `10.1145/3477132.3483570`), `Lockbud`
     (`BurtonQin/lockbud@a1b5303cdbb1d4d0ad886359cc71418570e7c5fd`), `TVLA`
     (TOPLAS 2002 DOI `10.1145/514188.514190`), and `MemCAD`
     (`Antique-team/memcad@d95caa514f2b66b8c43c015799084d281944f028`, POPL 2008
     DOI `10.1145/1328438.1328469`).
   - `DM4All` (ICFP 2019 DOI `10.1145/3341708`), `Why3`
     (`why3/why3@d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`), `Boogie`
     (`boogie-org/boogie@751228a2cf2c78177f9a0d040904022294aea1b2`, CAV 2021 DOI
     `10.1007/978-3-030-81688-9_33`), `SPLean`
     (`verse-lab/splean@e24286f51bd9ee207197d47ec587d592cdfb0ddc`), `CakeML CF`
     (`CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`, ICFP 2017 DOI
     `10.1145/3110263`), `Ultimate Automizer`
     (`ultimate-pa/ultimate@82f536df1bea812c74d70a91d8e67c1770c3fefe`, CAV 2013
     DOI `10.1007/978-3-642-39799-8_42`), `CeTA` (TPHOLs 2009 DOI
     `10.1007/978-3-642-03359-9_31`), `SCT` (POPL 2001 DOI
     `10.1145/360204.360210`), `Terminator` (PLDI 2006 DOI
     `10.1145/1133981.1134029`), `Dafny`
     (`dafny-lang/dafny@5f717bf447b19d38cad1b69b1bf9a9f102feccfb`), and `VCC`
     (TPHOLs 2009 DOI `10.1007/978-3-642-03359-9_2`).

### Part II Evidence — Historical Verification Failures

Observed 2026-10-31. Primary sources, immutable commits, DOIs, and executable
package artifacts:

| Subject / Claim | Primary Coordinate / Identifier | Evidence Role |
| :--- | :--- | :--- |
| Anneal `trusted/` boundary and workspace | `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`, `trusted/lean/Trusted.lean`, `trusted/audit/TrustedBoundary.lean` | source |
| `Dafny` prelude axiom & solver soundness bugs | `dafny-lang/dafny` issues `#6534` (`$Box($Unbox(x))`), `#6537` (`Map#Items`), `#4053` (`smt.arith.solver=6`) | documentation |
| `Verus` ghost erasure, `Tracked`, and SMT trust | `verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`, `builtin/src/lib.rs:546–570`, `air/src/smt_verify.rs:249–364`; arXiv `2303.05491v2` | source + documentation |
| `Creusot` & `RustHornBelt` prophetic borrows | Matsushita, Denis, Jourdan, and Dreyer, PLDI 2022, DOI `10.1145/3519939.3523704`; `creusot-rs/creusot` `label:soundness` | documentation |
| `Boogie` & `Viper` failure-reflection certificates | Parthasarathy et al., CAV 2021 (DOI `10.1007/978-3-030-81688-9_33`) and PLDI 2024 (DOI `10.1145/3656438`) | documentation |
| `Kani` soundness false-negative tracker | `model-checking/kani` issues under label `[F] Soundness` | documentation |
| `F*` reflection and VC-simplifier soundness bugs | `FStarLang/FStar` issues `#4478`, `#4485`, `#4487` (`kind/unsoundness`) | documentation |
| `RustBelt` `MutexGuard::map` & `Arc::get_mut` bugs | Jung et al., POPL 2018 (DOI `10.1145/3158154`, `rust-lang/rust#25760`); Dang et al., POPL 2020 (DOI `10.1145/3371102`, `rust-lang/rust#51780`) | documentation |
| `Stacked Borrows` vs. `Tree Borrows` | Jung et al., POPL 2020 (DOI `10.1145/3371109`); Villani et al., PLDI 2025 (DOI `10.1145/3729338`) | documentation |
| `rustc` implied bounds & HRTB soundness bugs | `rust-lang/rust` issues `#25860`, `#84591`, `#100013` | documentation |
| LLVM/C/Rust pointer provenance miscompilations | Lee et al., PLDI 2017 (DOI `10.1145/3062341.3062343`); Kang et al., OOPSLA 2018 (DOI `10.1145/3276495`); `llvm#34548`, `llvm#35229` | documentation |
| Linux eBPF verifier soundness CVEs | `torvalds/linux` commits `581738a681b6` (`CVE-2020-8835`), `049c4e13714e` (`CVE-2021-3490`), `10bf4e83167c` (`CVE-2021-31440`), `64620e0a1e71` (`CVE-2022-23222`), `71b547f56124` (`CVE-2023-2163`) | source + documentation |
| `Agni` eBPF `tnum` & range analysis verification | Vishwanathan et al., CGO 2022 (DOI `10.1109/CGO53902.2022.9741267`) and CAV 2023 (DOI `10.1007/978-3-031-37709-9_12`) | documentation |
| `Charon` & `Aeneas` extraction hazards | `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`#583`, `#534`, `OfJson.ml`); Ho and Protzenko, ICFP 2022 (DOI `10.1145/3547647`) | source + documentation |
| SMT instability & trigger selection (`Mariposa`) | Hawblitzel et al., SOSP 2015 (DOI `10.1145/2815400.2815428`); Leino and Pit-Claudel, CAV 2016 (DOI `10.1007/978-3-319-41528-4_20`); Zhou et al., OOPSLA 2023 (DOI `10.1145/3622852`) | documentation |
| Six mathematical failure-mechanism witnesses | `support/failure_mechanisms_probe.py` and `support/probe-results.json` | execution |

## Revalidation

### Part I Revalidation — Real-World Verification Tools

To revalidate the architectural mappings in this report when `trusted/lean/`
evolves:

1. **Check the four `trusted/lean/` primitives:** Diff `Trusted/Refinement.lean`
   and `Trusted/StepResult.lean` against the four-primitive equations in
   Section 1:
   - Verify `BehaviorCodec` retains `decodeQuery_encodeQuery`,
     `decodeOut_encodeOut`, `encodeOut_of_decodeOut`, and `obs_decodeOut`.
   - Verify `Language.ProductiveOn` requires both `(L.sem prog q).defined` and
     `∃ o, (L.sem prog q).val h o`, paired with `InhabitedPre pre`.
   - Verify `VerificationResult` uses positive disjunction
     `ob.id ∈ waived ∨ ob.prop` without antecedent implication `→`.
   - Verify `EventualBehaviorOf` defines `defined` via finite-prefix safety and
     places `.diverges` inside `EventualOut`, and that
     `StepResult.externalCall boundaryInv branches` steps to `.failed .ub` when
     `boundaryInv = false`.
2. **Discriminating probes for each category (`UC-1.1`–`UC-6.4`):**
   - For functional translators (`UC-1.1`), test an unsatisfiable prophecy
     equation and confirm `ProductiveOn` rejects it.
   - For `BehaviorCodec` (`UC-2.3`, `UC-3.4`), confirm `encodeOut_of_decodeOut`
     rejects non-injective `decodeOut` over unprojected padding bytes.
   - For `StepResult.externalCall` (`UC-4.2`, `UC-6.3`, `UC-6.4`), run the
     re-entrant callback canary (`canary_reentrant_callback_rejected` in
     `anneal-structural-external-calls-and-tcb-mutation-testing-2026`) and
     verify that breaking `AdtInv` before an external call falsifies `defined`.

### Part II Revalidation — Historical Verification Failures

1. **Rerun the deterministic mathematical witnesses:**
   ```console
   python3 reports/anneal-deductive-logics-types-and-abstract-interp-survey/support/failure_mechanisms_probe.py
   ```
   Verify that the script exits with code `0` and reproduces
   `support/probe-results.json` byte-for-byte, confirming that each naive gate
   accepts the unsound/vacuous construction while the corresponding Anneal
   primitive (`ProductiveOn`, `InhabitedPre`, positive `VerificationResult`,
   `StepResult.externalCall`, `Tree Borrows` `Reserved`, and guarded 64-to-32
   interval projection) rejects it.
2. **Audit `trusted/lean/` primitive invariants on future Anneal revisions:**
   Whenever `Trusted/Refinement.lean` or `Trusted/StepResult.lean` is modified,
   verify that:
   - `Trusted.CrateTheorem` requires `InhabitedPre pre` and `ProductiveOn pre`
     alongside behavioral refinement (`SpecOn` / `Abstracts` / `Compiles`);
   - `VerificationResult` remains positively polarity-isolated (`ob.id ∈ waived ∨ ob.prop`)
     and never injects waived obligations as hypotheses into the context of
     unwaived obligations; and
   - `StepResult.externalCall` evaluates `boundaryInv : Bool` before branching
     to `branches : State → Prop` and transitions to `.failed .ub` when
     `boundaryInv = false`.

*Authored by an AI agent acting on joshlf's behalf.*
