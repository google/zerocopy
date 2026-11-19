# Lattice Configuration Languages, Verified Cloud Reconcilers, and DO-178C MC/DC Traceability

## Summary

Declarative configuration languages, distributed cloud control planes, and safety-critical avionics certification share one deep structural problem: **preserving algebraic, temporal, and structural invariants across lowering, composition, and optimization boundaries where extensional output equivalence is insufficient.** Seven primary-source findings anchor this domain:

1. **`CUE` Subsumption Lattice vs. Non-Monotonic Defaults (`cue-lang/cue`):** Grounded in Bob Carpenter's typed feature structures (1992), `CUE` unifies types, constraints, and concrete atoms into a commutative, associative, idempotent meet-semilattice (`&`). Pragmatic extensions—defaults (`*v`), closed structs (`ClosedRecursive` / `ClosedNonRecursive`), and nested disjunctions—break pure monotonicity and can cause $2^k$ Cartesian expansion or subtle default shifts. `CUE`'s normative specification (`doc/ref/spec.md:767–860`) formalizes defaults as value-default pairs `⟨v, d⟩` with explicit rewrite rules `U0–U2`, `D0–D2`, `M0–M3`, yet leaves nested default-elimination edge cases marked `TODO`, and `internal/core/adt/default.go:43–56` resolves conflicting defaults (`NumDefaults > 1`) back into an unmarked disjunction.
2. **Configuration & Policy Language Design Trade-Offs (`Nickel`, `Dhall`, `Pkl`, `Cedar`, `JSON Schema`):** No single language maximizes order-independence, higher-order abstraction, guaranteed polynomial-time termination, and non-monotonic overrides simultaneously:
   - **`Nickel`** (`core/src/eval/merge.rs:50–160`) combines gradual static typing, lazy Findler–Felleisen blame contracts, and priority-based merging, explicitly noting that `MergeMode::Contract` is **not commutative** (`t1` must be value, `t2` contract).
   - **`Dhall`** (`standard/imports.md`, `standard/binary.md`) enforces strong normalization via System $F_\omega$ and pins remote imports by alpha-beta-eta normalized CBOR SHA-256 semantic integrity hashes (immune to formatting/variable renames), though strong normalization does not prevent hyper-exponential normalization cost.
   - **`Cedar`** (OOPSLA 2024, `cedar-policy/cedar-spec`) omits general recursion so authorization policies admit a sound-and-complete SMT encoding; its Lean 4 specification proves `validation_is_sound`, `validate_with_level_is_sound`, and `validate_with_level_no_dne` (`Cedar/Thm/Validation.lean:55–120`), linked to the production Rust engine via Differential Random Testing rather than formal code refinement.
   - **Modern JSON Schema (Draft 2019-09 / 2020-12)** (`Attouche et al. POPL 2024`, DOI `10.1145/3632891`) jumps from `PTIME` (Draft-07) to **`PSPACE`-complete in schema size** due to dynamically scoped `$dynamicRef` / `$dynamicAnchor` (not `unevaluatedProperties`, though statically compiling away annotation-dependent keywords still causes exponential schema blowup).
3. **Single- vs. Multi-Controller Cloud Reconciliation (`Anvil` OSDI 2024, `Welder` SOSP 2026):** Cloud reconciliation is fundamentally a temporal **liveness** property—*Eventually Stable Reconciliation (`ESR`)*—not merely safety. `Anvil` verifies isolated Rust controllers in `Verus` using `verus-tla` over a state-machine `Reconciler` trait (`reconcile_init_state`, `reconcile_core`, `reconcile_done`, `reconcile_error`). However, composing two individually `ESR`-live controllers over shared mutable Kubernetes fields (`Server-Side Apply` `managedFields` tug-of-war or `resourceVersion` OCC starvation) produces infinite limit-cycle oscillation. `Welder` (merged into `anvil-verifier/anvil` `src/kubernetes_cluster/proof/core.rs:9–160`) solves this via **Compositional Reconciliation (`CORE`)**, attaching `ControllerSpec` rely-guarantee (`safety_guarantee`, `safety_partial_rely`, `environment_rely`) and `liveness_dependency` contracts composed via `compatible`, `compose`, and `compose_dep`.
4. **Configuration-to-Reconciler Impedance Mismatch:** Static config lattices validate *endpoint validity* ($S_2$), not *path-dependent transition safety* ($S_1 \to S_2$ for stateful databases, storage shrink, or CA rotation); fusing monotone lattice fields (`replicas >= 3` & `replicas >= 7` $\implies$ `>= 7`) eliminates whole classes of imperative `SSA` overwrite oscillation (demonstrated in Probe 3B-ii).
5. **Why Semantic Refinement Does Not Imply `DO-178C` `MC/DC` Traceability (`Kirner 2009`):** `DO-178C § 6.4.4.2.b` (`CAST-12`, `CAST-17`) requires verifying any DAL A executable object code not directly traceable to source statements. Even a formally verified compiler (`CompCert`) legally destroys 1-to-1 structural coverage via branch folding, jump threading, loop unrolling, and branchless if-conversion.
6. **Empirical Compiler Coverage Drift on `GCC 15.2.0` (`-fcondition-coverage` & `-O0` vs. `-O2`):** Executing `gcc (Debian 15.2.0-14) 15.2.0` on `if ((a && b) || c)` exposes *two* distinct compiler hazards:
   - **Uninstrumented `-O0` vs. `-O2`:** `-O0` emits **3 conditional branches** (`je .L2`, `jne .L3`, `je .L4`) isomorphic to the short-circuit source CFG, whereas `-O2` compiles the entire decision **100% branchlessly** (`testl`/`setne`/`andl`/`orl`/`movzbl`/`ret` — **0 jumps**), directly reproducing Kirner's coverage-non-preservation result on x86-64.
   - **Instrumented `-O0` vs. `-O2` (`-fcondition-coverage`):** At `-O0`, `gcov -b --conditions` tracks all **6** source condition outcomes (`5/6` on a branch-complete non-MC/DC suite, catching `condition 1 not covered (false)`, and `6/6` on the 4-vector minimal MC/DC suite). At **`-O2`**, pre-instrumentation GIMPLE folding silently collapses the decision from **6 condition outcomes down to 4** (`Condition outcomes covered: 100.00% of 4`), reporting `100.00%` while silently dropping two source MC/DC obligations!
7. **Tool Qualification Asymmetry (`DO-330` `TQL-1` vs. `TQL-5`, `DO-333`, `LLVM`/`GCC`/`GNATcoverage`/`Ferrocene`):** Qualifying a 20M-LOC optimizing compiler at `TQL-1` is prohibitive (forcing `-O0` penalties or massive black-box test suites like `Ferrocene`), whereas `DO-330` allows an unqualified `-O2` compiler paired with a tiny `TQL-5` / `DO-333` translation-validation and `SCO`-to-PC traceability certificate checker. In Rust, static panic-freedom and bounds-check elimination proofs directly reduce untraceable defensive branches (`core::panicking`, drop flags, macro expansions).

## Applicability

This report examines primary source implementations, formal specifications, regulatory standards, and live compiler executions across three interconnected layers:

- **Declarative configuration & policy languages:** `cue-lang/cue` (`b38d73e3f13559da0ba290e7e61d21ae7230a6ae`, `doc/ref/spec.md`, `internal/core/adt/{default,closed}.go`), `tweag/nickel` (`46ffe62b1cf54e97cf95bad6337570486008c89b`, `core/src/eval/merge.rs`, `core/src/label.rs`), `dhall-lang/dhall-lang` (`56b0997a4800bfc815ea221529a6bb2bfd6723dc`, `standard/{imports,binary}.md`), `apple/pkl` (`069c891ac86067cd26c68d4647100e26c5ed5ba0`), `cedar-policy/cedar` (`4ff0bb074699db8c348426ee03db933bf8ebfdd6`), `cedar-policy/cedar-spec` (`326d93c24490c90607a3e257318e9c6a049c8116`, OOPSLA 2024 DOI `10.1145/3649835`), `open-policy-agent/opa` (`674d3362381e14b55069a7a5741eeb8489365c2f`), and Modern JSON Schema Draft 2019-09 / 2020-12 (`POPL 2024` DOI `10.1145/3632891`).
- **Verified cloud reconcilers:** `anvil-verifier/anvil` (`e83ea0f5516ce2ece26740266165180018741e66`, containing merged `Welder` `CORE` proofs in `src/kubernetes_cluster/proof/core.rs`; OSDI 2024 & SOSP 2026 DOI `10.1145/3830418.3843868`) and `verus-lang/verus` (`a95764f23c6876b47500beda6118e2d142a87cc3`).
- **Safety-critical structural coverage & compiler qualification:** RTCA `DO-178C` / EUROCAE `ED-12C` (§ 6.4.4.2.b), `DO-330`, `DO-333`, FAA `CAST-10`/`12`/`17`/`32A` / EASA `AMC 20-193`, Chilenski & Miller (DOI `10.1049/sej.1994.0025`), Hayhurst et al. (`NASA/TM-2001-210876`), Kirner (DOI `10.1155/2009/127945`), `llvm/llvm-project` (`507de0cc365e4c6317d21fb08e298f742256a51f`, `CoverageMapping.{h,cpp}`), `gcc-mirror/gcc` (`78c5290e696d76fdbe7f3b006df9145d1ed7927c`, `gcc/tree-profile.cc`), `AdaCore/gnatcoverage` (`8b3ccf5be798827c7a7ae0245e13e1cb5ba89a56`, `sc_obligations.ads`), `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`), and `ferrocene/ferrocene` (`85d04a5bfcd57edb4e22df89d8d0eeb13a8ddc1d`).
- **Executable probes:** Executed on `gcc (Debian 15.2.0-14) 15.2.0`, `gcov 15.2.0`, and `CPython 3.13.15` (`x86_64-linux`). The exact x86-64 instruction sequence (`testl`/`setne`/`andl`/`orl`) and GIMPLE folding behavior (`6/6 → 4/4` condition outcomes) are observed directly on `GCC 15.2.0` (`-O0` vs. `-O2`), while the architectural distinction between frontend AST instrumentation (`LLVM -fcoverage-mcdc`), GIMPLE CFG instrumentation (`GCC -fcondition-coverage`), and uninstrumented object-trace back-mapping (`GNATcoverage`) generalizes across targets.

## Findings

### 1. `CUE` Typed-Feature-Structure Subsumption Lattice vs. Non-Monotonic Defaults and Closed Structs

Basis: normative + source + execution (`cue-lang/cue` @ `b38d73e3f13559da0ba290e7e61d21ae7230a6ae`; Carpenter 1992; `CPython 3.13.15` Probe 3B-i)

`CUE` adapts Bob Carpenter's *The Logic of Typed Feature Structures* (1992) into a configuration language where **types, constraints, schemas, and concrete values inhabit a single bounded meet-semilattice**: top (`_`), basic types (`int`, `string`), bounds (`>0 & <65536`), concrete atoms (`8080`), and bottom (`_|_`, conflict). Pure unification (`&`) is the lattice greatest lower bound—**commutative, associative, and idempotent**—eliminating order-dependent override bugs common in prototype-inheritance languages (`Jsonnet`/`GCL`) and raw string templating (`Helm`).

#### Normative Value-Default Pair Calculus (`doc/ref/spec.md:767–860`)
Because pure monotonic unification cannot express overridable defaults (unifying concrete `3` with `5` yields `_|_`), `CUE` attaches default annotations (`*v`) to disjunctions. The normative specification models every value as either unmarked `⟨v⟩` or a value-default pair `⟨v, d⟩` (requiring $d \sqsubseteq v$) governed by exact rewrite rules:

```text
Unification:                           Unmarked Disjunction:
  U0: ⟨v1⟩ & ⟨v2⟩         => ⟨v1&v2⟩     D0: ⟨v1⟩ | ⟨v2⟩         => ⟨v1|v2⟩
  U1: ⟨v1, d1⟩ & ⟨v2⟩     => ⟨v1&v2, d1&v2⟩  D1: ⟨v1, d1⟩ | ⟨v2⟩     => ⟨v1|v2, d1⟩
  U2: ⟨v1, d1⟩ & ⟨v2, d2⟩ => ⟨v1&v2, d1&d2⟩  D2: ⟨v1, d1⟩ | ⟨v2, d2⟩ => ⟨v1|v2, d1|d2⟩

Marked Disjunction Pre-Rewrite:        Subsumption:
  M0:  ⟨v⟩    => ⟨v⟩                     ⟨v2, d2⟩ ⊑ ⟨v1, d1⟩  iff v2 ⊑ v1 and d2 ⊑ d1
  M1: *⟨v⟩    => ⟨v, v⟩                  ⟨v1, d1⟩ ⊑ ⟨v⟩       iff v1 ⊑ v
  M2: *⟨v, d⟩ => ⟨v, d⟩                  ⟨v⟩      ⊑ ⟨v1, d1⟩  iff v ⊑ d1
  M3:  ⟨v, d⟩ => ⟨v⟩   (strips inner defaults on unmarked branches)
```

Three structural fault lines emerge directly in the specification and Go evaluator:
1. **Non-monotonic default elimination & ambiguity:** By `U2`, `(*1|2) & (1|*2)` evaluates to `⟨1|2, _|_⟩` (the default component collapses to bottom, leaving an ambiguous non-concrete disjunction). In `internal/core/adt/default.go:43–56`, `Disjunction.Default()` returns `d.Values[0]` only when `d.NumDefaults == 1`; for `NumDefaults > 1`, it returns a new unmarked `&Disjunction{Values: d.Values[:d.NumDefaults], NumDefaults: 0}`. In Probe 3B-i, unifying ambiguous `(*"a"|"b") | (*"b"|"c")` (`effective = ['a', 'b']`) with constraint `!="a"` jumps its effective default to concrete `['b']`; conversely, eliminating the unique marked default of `(*"a"|"b"|"c")` causes default concretization to vanish (`spec.md:785` explicitly notes `<!-- TODO: this formulation should be worked out more. -->`).
2. **Closed-struct provenance (`internal/core/adt/closed.go:80–284`):** Catching typoed keys (`relicas: 3`) requires distinguishing closed definitions (`#Def`) from open records (`ClosedRecursive` vs. `ClosedNonRecursive`, tracked via `CloseInfo` and `ApplyEmbedClosedness`). Embeddings and comprehensions propagate closedness non-trivially, and closed-world validation clashes with rolling-upgrade forward compatibility when a newer service adds optional fields rejected by an older consumer's closed schema.
3. **Disjunction blowup & structural cycles (`evalv2` → `evalv3`):** Unifying $k$ independent disjunctions `(A_1 | B_1) & ... & (A_k | B_k)` distributes into $2^k$ Cartesian disjuncts (encoding propositional SAT, `NP`-complete), and recursive schemas induce structural cycles requiring sophisticated cycle detection (driving `CUE`'s multi-year `evalv3` evaluator rewrite).

---

### 2. Comparative Matrix: `CUE`, `Nickel`, `Dhall`, `Pkl`, `JSON Schema 2020-12`, `Cedar`, and `Rego`

Basis: source + normative (`tweag/nickel` @ `46ffe62b1cf54e97cf95bad6337570486008c89b`; `dhall-lang/dhall-lang` @ `56b0997a4800bfc815ea221529a6bb2bfd6723dc`; `cedar-policy/cedar-spec` @ `326d93c24490c90607a3e257318e9c6a049c8116`, OOPSLA 2024 DOI `10.1145/3649835`; `POPL 2024` DOI `10.1145/3632891`)

| Language / Standard | Core Paradigm | Commutative / Order-Independent? | Total / Terminating? | Worst-Case Complexity | Override / Default Mechanism | Static Equivalence / Analysis | Blame / Integrity Mechanism |
|---|---|---|---|---|---|---|---|
| **`CUE`** (`cue-lang/cue`) | Typed-feature-structure meet-semilattice (`&`) | **Yes** on pure constraints; **No** on non-monotonic default jumps | Designed non-Turing-complete (guarded structural cycles) | Near-linear disjunction-free; **exponential (`NP`-hard)** with nested disjunctions | Marked disjunctions `*v` (`⟨v, d⟩`), no destructive override | Subsumption `⊑` decidable on core fragments | Vertex/conjunct provenance (`CloseInfo`) |
| **`Nickel`** (`tweag/nickel`) | Gradual static typing + lazy contracts + priority record merge | Standard merge associative/commutative on equal values; **`MergeMode::Contract` non-commutative** (`merge.rs:74–75`) | **No** (Turing-complete; lazy cyclic merges can diverge) | Undecidable in general | Explicit merge priorities (`default`, `force`, numeric) | Static check on typed blocks; lazy runtime contracts elsewhere | Findler–Felleisen **blame labels & polarity** (`core/src/label.rs`) |
| **`Dhall`** (`dhall-lang/dhall-lang`) | Total functional System $F_\omega$ | N/A (functional application / `//` right-biased record update) | **Yes** (strongly normalizing) | **Hyper-exponential** (System $F_\omega$ normalization $\neq \mathsf{PTIME}$) | Right-biased record merge (`//`, `//\\`) | $\alpha\beta\eta$-equivalence decidable | **Semantic integrity hashes** (SHA-256 over $\alpha\beta\eta$-normal CBOR, `imports.md`) |
| **`Apple Pkl`** (`apple/pkl`) | Typed OO classes, modules, and amendments | **No** (amendment / inheritance order matters) | Practical (guarded recursion) | Non-polynomial in general | `amends` / `extends` + inline predicates `UInt16(this > 1000)` | Type checking + runtime constraint evaluation | Stack traces; refinement predicates erased in Go/Java/Swift codegen |
| **JSON Schema 2020-12** (`POPL 2024`) | Structural wire-contract validation | Boolean combinators (`allOf`/`anyOf`/`oneOf`/`not`) | Yes (finite instance + guarded recursion) | **`PSPACE`-complete in schema size** (`$dynamicRef`); `PTIME` for Draft-07 | `default` is non-validating annotation only | Containment/satisfiability undecidable/high complexity | Annotation side-channel (`unevaluatedProperties`) causes cross-validator drift |
| **`Cedar`** (`cedar-policy/cedar`, `cedar-spec`) | Decidable RBAC/ABAC/ReBAC policy language | **Yes** (deny-by-default set of `permit`/`forbid` policies) | **Yes** (no general recursion or unbounded loops) | Linear-time policy eval; **SMT-decidable** analysis | Explicit `forbid` overrides `permit` | **Sound & complete SMT encoding** (mechanized in Lean 4) | Lean 4 `validation_is_sound` & `validate_with_level_no_dne` + DRT to Rust |
| **`Rego` (`OPA`)** (`open-policy-agent/opa`) | Datalog-inspired general policy language | Set-oriented rules (with `else` ordering) | **No** (general recursion / builtins) | Undecidable static analysis | `default` + `else` clauses | Static policy equivalence **undecidable** | Runtime evaluation trace |

#### Primary-Source Highlights
- **`Nickel` non-commutative contract merge (`core/src/eval/merge.rs:49–76`):** `MergeMode` separates `Standard(MergeLabel)` (data combination) from `Contract(Label)` (applying a record contract, returning `'Ok result` or `'Error {..}` on unexpected extra fields), explicitly documenting: *"In `MergeMode::Contract` mode, `t1` must be the value and `t2` must be the contract. It is important as `merge` is not commutative in this mode."*
- **`JSON Schema` `PSPACE`-completeness (`Attouche et al. POPL 2024`, DOI `10.1145/3632891`):** Formalizing Draft 2019-09 and Draft 2020-12 proves that validation against a *fixed* tiny JSON instance jumps from `PTIME` (Draft-07) to `PSPACE`-complete in schema size solely because **`$dynamicRef` / `$dynamicAnchor`** introduces dynamically scoped recursion over the validation call stack (capable of encoding QBF). Removing `$dynamicRef` restores `PTIME` validation, though statically eliminating annotation-dependent `unevaluatedProperties` / `unevaluatedItems` triggers exponential schema size blowup—creating parser-differential and CPU-DoS hazards wherever JSON Schema acts as a wire contract for OpenAPI, Kubernetes CRDs, or LLM constrained decoders.
- **`Cedar` Lean 4 Soundness Theorems (`cedar-lean/Cedar/Thm/Validation.lean:55–120`):**
  - `validation_is_sound`: proves that if `schema.validateWellFormed = .ok ()`, `validate policies schema = .ok ()`, `validateRequest schema request = .ok ()`, and `validateEntities schema entities = .ok ()`, then every policy evaluates to a boolean or one of three runtime-only errors (`entityDoesNotExist`, `extensionError`, `arithBoundsError`).
  - `validate_with_level_is_sound` & `validate_with_level_no_dne`: prove that if policies validate at level `n`, evaluating against the level-`n` entity slice `entities.sliceAtLevel request n` yields identical authorization decisions, and if `entities.closedAtLevel request n` holds, no policy can ever raise `.error .entityDoesNotExist`.
  - **DRT gap:** Production execution runs in Rust (`cedar-policy/cedar`), validated against the Lean 4 reference model via Differential Random Testing rather than formally verified Rust-to-Lean compilation.

---

### 3. Verified Desired-State Cloud Reconcilers (`Anvil` OSDI 2024 & `Welder` SOSP 2026)

Basis: source + normative + execution (`anvil-verifier/anvil` @ `e83ea0f5516ce2ece26740266165180018741e66`; OSDI 2024; SOSP 2026 DOI `10.1145/3830418.3843868`; `CPython 3.13.15` Probe 3B-ii)

Kubernetes controllers operate via level-triggered desired-state reconciliation loops against `etcd` through `kube-apiserver`. Chaos and state-space testing studies (`Sieve` OSDI 2022; `Acto` SOSP 2023) established that production operator bugs are predominantly **liveness bugs**—permanent wedges triggered by stale informer caches, crashes mid-reconciliation leaving orphaned resources or stuck finalizers, or dropped events.

#### `Anvil` (OSDI 2024): Eventually Stable Reconciliation (`ESR`) in `Verus`
`Anvil` embeds TLA-style temporal logic (`verus-tla`) inside `Verus` to verify production-deployable Rust Kubernetes controllers (ZooKeeper, RabbitMQ, FluentBit, and later built-in ReplicaSet, Deployment, and StatefulSet). Controllers implement a pure step-by-step state machine (`README.md:25–36`):

```rust
pub trait Reconciler {
    type R; // custom resource type
    type T; // reconcile local state type
    fn reconcile_init_state() -> Self::T;
    fn reconcile_core(cr: &Self::R, resp_o: Option<Response<...>>, state: Self::T)
        -> (Self::T, Option<Request<...>>);
    fn reconcile_done(state: &Self::T) -> bool;
    fn reconcile_error(state: &Self::T) -> bool;
}
```

- **Liveness specification (`ESR`):** Under weak fairness and an eventually quiescent environment (bounded external faults/updates), if desired state $d$ persists ($\Box \text{Desired}(d)$), the cluster eventually reaches and remains in matching state ($\Diamond \Box \text{CurrentMatches}(d)$).
- **FFI/shim trust boundary:** `Anvil` verifies the Rust state machine against a formal Verus model of `kube-apiserver`/`etcd`; HTTP/2 transport, `kube-rs`, `serde_json` marshaling, unmodeled mutating admission webhooks, and `etcd` compaction/watch bookmarks sit in the unverified runtime shim.

#### `Welder` (SOSP 2026): Multi-Controller Oscillation and Compositional Reconciliation (`CORE`)
Single-controller `ESR` proofs assume an isolated environment where external writers stop. In real clusters running dozens of controllers (Deployment, ReplicaSet, HPA, Argo CD GitOps, webhooks), two individually `ESR`-verified controllers can **oscillate forever** (e.g., Kubernetes Server-Side Apply `managedFields` tug-of-war where Argo CD force-applies `replicas: 3` while HPA scales to `replicas: 7`, or high-frequency status updates continuously bumping whole-object `resourceVersion` and starving slower OCC CAS writers).

`Welder` (Cai et al., SOSP 2026, DOI `10.1145/3830418.3843868`, merged directly into `anvil-verifier/anvil`) introduces **COmpositional REconciliation (`CORE`)** in `src/kubernetes_cluster/proof/core.rs:9–160`:

```rust
pub struct ControllerSpec {
    pub esr: TempPred<ClusterState>,
    pub liveness_dependency: TempPred<ClusterState>,
    pub safety_guarantee: TempPred<ClusterState>,
    pub environment_rely: TempPred<ClusterState>,
    pub safety_partial_rely: spec_fn(int) -> TempPred<ClusterState>,
    pub fairness: spec_fn(Cluster) -> TempPred<ClusterState>,
    pub membership: spec_fn(Cluster, int) -> bool,
}

pub open spec fn core(cluster: CoreCluster, s: CoreSet) -> bool {
    // G = /\_{c in s} safety_guarantee(c)
    // R = /\_{c in s, c' not in s} safety_partial_rely(c)(c')
    // cluster_model(cluster) |= G /\ ((R /\ s.liveness_dependency /\ env_rely) => ESR(s))
}
```

- **Modular composition rules (`core.rs:51–98`):** Two `CoreSet`s `s1` and `s2` compose via `compose` (independent liveness) or `compose_dep` (acyclic dependency chain where `satisfies_dependency(cluster, s1, s2)` proves `ESR(s1) ==> s2.liveness_dependency`) provided `compatible(cluster, s1, s2)` holds (`G(s1) ==> R(s2, s1)` and `G(s2) ==> R(s1, s2)`).
- **Lattice convergence bridge (Probe 3B-ii):** Imperative whole-field overwrites between GitOps (`replicas=3`) and HPA (`replicas=7`) oscillate `[3, 7, 3, 7, 3, 7, 3]` indefinitely. Lifting shared fields into a `CUE`-style monotone lower-bound lattice (`replicas >= 3` & `replicas >= 7` $\implies$ `max(lb, k)`) converges deterministically `[0, 7, 7, 7, 7, 7, 7]` in 1 tick—aligning declarative lattice semantics directly with compositional liveness!
- **Endpoint vs. trajectory gap:** Static config lattices validate only *endpoint* schemas ($S_2$), whereas stateful infrastructure transitions (storage-engine change, volume shrink, CA rotation) are path-dependent and irreversible, requiring explicit multi-step transition typestates (`DualWrite → Backfill → Cutover → Cleanup`) inside verified reconcilers.

---

### 4. `DO-178C` Level A `MC/DC`, Optimizing-Compiler Coverage Drift, and `TQL-5` Traceability Witnesses

Basis: normative + source + execution (RTCA `DO-178C § 6.4.4.2.b`, `DO-330`, `DO-333`, `CAST-10`/`12`/`17`/`32A`; DOIs `10.1049/sej.1994.0025`, `10.1155/2009/127945`; `NASA/TM-2001-210876`; `llvm/llvm-project` @ `507de0cc365e4c6317d21fb08e298f742256a51f`; `gcc-mirror/gcc` @ `78c5290e696d76fdbe7f3b006df9145d1ed7927c`; `AdaCore/gnatcoverage` @ `8b3ccf5be798827c7a7ae0245e13e1cb5ba89a56`; `GCC 15.2.0` Probe 3A)

#### `DO-178C` DAL A `MC/DC` Requirements & Decision Semantics
Under RTCA `DO-178C` / EUROCAE `ED-12C` Design Assurance Level A (and ISO 26262 ASIL D), structural coverage must satisfy **100% Modified Condition/Decision Coverage (`MC/DC`)** (Chilenski & Miller 1994, DOI `10.1049/sej.1994.0025`; Hayhurst et al., `NASA/TM-2001-210876`):
1. Every entry and exit point is invoked;
2. Every decision takes every possible outcome (`true` and `false`);
3. Every atomic condition takes every possible outcome (`true` and `false`);
4. **Independence:** Every atomic condition is shown to independently affect its enclosing decision's outcome—requiring only $N+1$ to $2N$ tests instead of $2^N$ exhaustive truth tables.
- **`CAST-10` & Masking vs. Unique-Cause `MC/DC`:** `CAST-10` clarifies that *every* Boolean expression (assignments `bool x = (a && b) || c;`, ternaries, arguments—not just `if`/`while`) is a decision. When a Boolean variable is coupled (appears twice in one decision), strict Unique-Cause MC/DC is mathematically impossible; **Masking MC/DC** allows other conditions to vary provided they are algebraically masked (cannot influence the subexpression outcome under short-circuit/Boolean operators).

#### `DO-178C § 6.4.4.2.b` and Kirner's Coverage Non-Preservation Theorem (`2009`)
`DO-178C § 6.4.4.2.b` (`CAST-12`, `CAST-17`) mandates that for Level A software, **additional verification must be performed on any executable object code not directly traceable to source statements.** Raimund Kirner (2009, DOI `10.1155/2009/127945`) proved that **semantic compiler correctness ($\text{Beh}(T) \subseteq \text{Beh}(S)$, as in `CompCert`) does NOT imply structural coverage preservation**:
- **Branchless if-conversion** (`cmov` / `setne` / bitwise `&`/`|`) eliminates object-level short-circuit branches completely;
- **Jump threading, loop unrolling, and function inlining** clone one source decision $D$ into $k$ specialized object sites $D_1, \dots, D_k$ where a 100%-MC/DC source suite leaves cloned object branches unexecuted;
- **Defensive hidden branches in modern safe languages (`Rust` / `Ferrocene`):** Slice bounds checks, overflow checks, `?` early returns, drop flags, procedural macro expansions, and monomorphized generic copies inject compiler-synthesized branches flagged as deactivated/untraceable code unless eliminated statically via formal panic-freedom proofs (`DO-333`) before codegen.

#### Primary-Source Architecture of Modern Compiler `MC/DC` Toolchains
- **`LLVM -fcoverage-mcdc` (`llvm/lib/ProfileData/Coverage/CoverageMapping.cpp:252–439`, `CoverageMapping.h:688–701`):** Instruments at the Clang frontend AST/IR level using a compact per-decision **ExecutedTestVectorBitmap** indexed by `mcdc::TVIdxBuilder` (guarded by `HardMaxTVs` overflow limit), then reconstructs independence pairs offline in `MCDCRecord::findIndependencePairs()`. *Trade-off:* Captures exact source short-circuit decisions prior to `-O2` folding, but **instrumentation mutates the binary** (altering code size, register pressure, and WCET—violating *"fly what you test"* unless paired with object traceability) and is blind to backend-synthesized branches.
- **`GCC -fcondition-coverage` (`gcc/tree-profile.cc:113–153,391–576,871–952`):** Computes **Masking MC/DC** on the GIMPLE CFG by modeling each Boolean expression as a Reduced Ordered Binary Decision Diagram (ROBDD) and exploiting the duality *"Masking is essentially short-circuiting in reverse"* (`masking_vectors`, `find_conditions`), instrumenting bitwise accumulators `_t`, `_f`, `_mask` (`uint64_t` bitmasks). *Trade-off:* Because instrumentation runs inside GIMPLE *after* early optimization passes at `-O2`, pre-instrumentation folding silently erases source conditions (verified directly in Probe 3A-iii below!).
- **`AdaCore GNATcoverage` / `Couverture` (`tools/gnatcov/sc_obligations.ads:76–161`; ERTS 2010):** Supports **uninstrumented flight binaries** executed under hardware trace probes (ARM ETM / Nexus / instrumented QEMU), back-mapping raw machine PC/branch traces onto compiler-emitted **Source Coverage Obligations (`SCOs`)**. Notably, `sc_obligations.ads:115` defines `type SCO_Provider is (Compiler, Instrumenter, LLVM);`—bridging compiler `.ali` SCOs, source instrumentation, and LLVM formats. Uninstrumented object-trace back-mapping preserves zero probe effect ("fly what you test") but requires restricting optimizations (`-O0`/`-O1`) unless the compiler emits verified pass-by-pass `SCO ↔ Machine PC` traceability certificates.

#### Executable Probe 3A: `GCC 15.2.0` `-fcondition-coverage` and `-O0` vs. `-O2` Disassembly Diff
Tested on `int decide(int a, int b, int c) { if ((a && b) || c) return 1; return 0; }` (`gcc (Debian 15.2.0-14) 15.2.0`, `x86_64-linux`):

| Build Mode & Test Suite | Emitted Machine Conditional Jumps | `gcov` Branches Reported | `gcov` Condition Outcomes Reported | Key Finding |
|---|---:|---:|---:|---|
| `-O0 -fcondition-coverage` + 3-vector suite `(1,1,0),(0,0,0),(0,0,1)` | Instrumented | `6` (`83.33%` taken) | **`5/6` (`83.33%`)** — `condition 1 not covered (false)` | Correctly catches missing `b=false` independence witness despite `100%` line & `100%` decision coverage! |
| `-O0 -fcondition-coverage` + 4-vector suite `(1,1,0),(1,0,0),(0,1,0),(1,0,1)` | Instrumented | `6` (`100.00%`) | **`6/6` (`100.00%`)** | Full Masking MC/DC achieved with minimal $N+1 = 4$ vectors. |
| **`-O2 -fcondition-coverage`** + 4-vector suite | Instrumented (post-GIMPLE opt) | **`4` (`100.00%`)** | **`4/4` (`100.00%`)** | **Silent obligation loss:** GIMPLE `-O2` folds 1 of 3 conditions away *before* `tree-profile.cc`, reporting `100.00% of 4` instead of `6`! |
| **Uninstrumented `-O0 -S`** | **3 conditional (`je/jne/je`) + 1 `jmp`** | N/A | N/A | 1-to-1 structural isomorphism with short-circuit source CFG. |
| **Uninstrumented `-O2 -S`** | **0 jumps (`testl/setne/andl/orl/movzbl/ret`)** | N/A | N/A | **100% branchless lowering:** destroys object-level branch correspondence while preserving extensional semantics (Kirner 2009). |

#### `DO-178C` DAL A Qualification & Traceability Matrix (`DO-330`, `DO-333`, `CAST-32A`)

| Toolchain / Strategy | Optimization Level | `DO-330` Qualification Burden | Source-to-Object Traceability Mechanism | Key Advantage | Key Limitation / Failure Mode |
|---|---|---|---|---|---|
| **Legacy Unqualified Compiler at `-O0`** | `-O0` (disabled) | Unqualified compiler; heavy verification | Near 1-to-1 assembly inspection + manual `OCA` | Avoids `TQL-1` compiler qualification | **2×–5× CPU/WCET/SWaP penalty**; breaks Rust/C++ zero-cost abstractions |
| **Ansys `SCADE KCG`** | Non-optimizing codegen | **`TQL-1`** (Criteria 1 development tool) | Qualified Lustre-to-C code generation | Eliminates downstream C unit testing | Restricted to synchronous dataflow subset; no general systems code |
| **`CompCert` + AbsInt Qualification** | Verified middle/backend (`-O1`/`-O2` subset) | **`DO-333`** formal verification credit | Coq semantic refinement proof + deterministic pass set | Eliminates miscompilation bugs mathematically | C only; lags `LLVM -O3`; still requires Kirner/object coverage justification |
| **`Ferrocene` (`ferrocene/ferrocene`)** | Qualified `rustc` + `LLVM` locked flags | Black-box conformance suite (`ISO 26262` ASIL D / `IEC 61508` / DO-178C path) | Locked target/flag profile + requirements traceability | Enables memory-safe Rust in certified stacks | Compiler not internally proved; Rust panic/macro hidden branches need audit |
| **`LLVM -fcoverage-mcdc` / `GCC -fcondition-coverage`** | `-O0` (safe); `-O2` hazardous on GCC | `TQL-5` verification tool (must be qualified for primary credit) | AST bitmap (`LLVM`) / GIMPLE ROBDD mask (`GCC`) | Automated Masking MC/DC at zero third-party license cost | Instrumentation alters binary/WCET; GCC `-O2` silently drops obligations |
| **`GNATcoverage` (`Couverture`)** | `-O0` / `-O1` (or traceability study) | `TQL-5` qualified verification tool | Uninstrumented hardware/QEMU PC traces $\to$ `SCO`s | Zero probe effect ("fly what you test") | Fragile under aggressive `-O2` branch folding/inlining |
| **Certifying `-O2` Compiler + `TQL-5` Checker** *(architectural pattern)* | Full `-O2` / `-O3` | **Compiler unqualified (`0`); tiny checker `TQL-5` + `DO-333`** | Per-pass semantic refinement + Kirner `SCO ↔ PC` proof witness | Recovers full `-O2` performance with tiny TCB | Emerging research; requires formalizing specialization-deadness witnesses & regulatory acceptance |

Finally, **multi-core interference (`CAST-32A` / EASA `AMC 20-193`)** closes the loop across all three domains: on shared-L2/L3/DRAM SoCs, a low-criticality core can inflate a DAL A core's WCET by $3\times$–$10\times$ unless spatial/temporal hardware partitioning (cache coloring, ARM MPAM, private TCMs, TDMA interconnects) is enforced—a hardware-topology configuration problem directly amenable to declarative lattice validation (`CUE`) and compositional rely-guarantee reasoning (`Welder`).

## Boundaries

- **Mechanized Lean 4 formalization of `CUE` `evalv3` (`unknown`):** No complete mechanized formalization of `CUE`'s `evalv3` evaluator—jointly handling non-monotonic nested defaults (`spec.md:785` `TODO`), closed-struct embedding provenance (`CloseInfo`), and structural cycles—is established in the examined sources.
- **Composing `Welder` `CORE` proofs with unverified Go/Rego controllers and webhooks (`unknown` / `known not to apply` without dynamic enforcement):** `Welder`'s `compose` and `compose_dep` proofs (`src/kubernetes_cluster/proof/core.rs:59–98`) require every participating controller in `CoreSet` to discharge its `safety_guarantee` and `safety_partial_rely` obligations in `Verus`; an unverified third-party Go controller or mutating admission webhook can violate `safety_partial_rely` unless dynamically fenced by an API-server field-ownership shield.
- **`Cedar` Rust↔Lean formal refinement (`known not to apply` at examined commits):** At `cedar-policy/cedar` `4ff0bb074699db8c348426ee03db933bf8ebfdd6` and `cedar-spec` `326d93c24490c90607a3e257318e9c6a049c8116`, conformance between the Lean 4 verified specification and the Rust production evaluator rests on Differential Random Testing rather than a machine-checked refinement proof.
- **Local `clang -fcoverage-mcdc` and `rustc -Z coverage-options=mcdc` execution (`not examined`):** `clang` and `llvm-cov` were not installed in the probe host; `LLVM` MC/DC mechanics were verified directly from pinned upstream source (`CoverageMapping.{h,cpp}`), while live `-fcondition-coverage` and `-O0`/`-O2` execution probes ran on `GCC 15.2.0` + `gcov 15.2.0`.
- **Regulatory precedent for certifying `-O2` compilers with `TQL-5` traceability checkers (`unknown`):** While `DO-330` and `DO-333` structurally separate `TQL-1` development tools from `TQL-5` verification checkers, FAA/EASA certification precedent for accepting machine-checked Kirner MC/DC coverage-preservation witnesses emitted by an unqualified `-O2` `LLVM`/`rustc` pipeline has not yet been established in public certification memos.
- **Bounded-time convergence in `Anvil`/`Welder` (`unsupported` in current `ESR` formulation):** `Anvil`/`Welder` verify unbounded eventual liveness ($\Diamond \Box$) under weak fairness rather than concrete wall-clock or bounded-step convergence deadlines.

## Evidence

### Primary Git Source Artifacts (Observed `2026-11-19`)
- **`cue-lang/cue` @ `b38d73e3f13559da0ba290e7e61d21ae7230a6ae`:**
  - `doc/ref/spec.md:672–915`: Unification, Disjunction, and Default values (`U0–U2`, `D0–D2`, `M0–M3`, subsumption rules, `(*1|2) & (1|*2) => ⟨1|2, _|_⟩`, L785 `TODO`).
  - `internal/core/adt/default.go:23–85`: `ConcreteDefault`, `DefaultDisjunct`, `Disjunction.Default()` (L43–56 collapsing `NumDefaults > 1` to unmarked disjunction).
  - `internal/core/adt/closed.go:80–284`: `IsRecursivelyClosed`, `ClosedRecursive`, `ClosedNonRecursive`, `ApplyEmbedClosedness`, `CloseInfo`.
- **`tweag/nickel` @ `46ffe62b1cf54e97cf95bad6337570486008c89b`:**
  - `core/src/eval/merge.rs:1–160`: `MergeMode::{Standard, Contract}` and `VirtualMachine::merge` documenting non-commutativity of `MergeMode::Contract` (L74–75).
  - `core/src/label.rs`: Blame `Label`, `MergeLabel`, and `Polarity` tracking.
- **`dhall-lang/dhall-lang` @ `56b0997a4800bfc815ea221529a6bb2bfd6723dc`:**
  - `standard/imports.md` and `standard/binary.md`: Normative CBOR encoding and SHA-256 semantic integrity checks over $\alpha\beta\eta$-normal forms.
- **`cedar-policy/cedar-spec` @ `326d93c24490c90607a3e257318e9c6a049c8116`** & **`cedar-policy/cedar` @ `4ff0bb074699db8c348426ee03db933bf8ebfdd6`:**
  - `cedar-lean/Cedar/Thm/Validation.lean:55–120`: Lean 4 theorems `validation_is_sound`, `validate_with_level_is_sound`, and `validate_with_level_no_dne`.
- **`anvil-verifier/anvil` @ `e83ea0f5516ce2ece26740266165180018741e66`** & **`verus-lang/verus` @ `a95764f23c6876b47500beda6118e2d142a87cc3`:**
  - `README.md:12–96`: `Reconciler` trait, `ControllerSpec` struct, Welder merged into `main`, `osdi24`/`sosp26` artifact branches.
  - `src/kubernetes_cluster/proof/core.rs:9–160`: `CoreCluster`, `CoreSet`, `cluster_model`, `well_formed`, `core`, `compatible`, `compose`, `satisfies_dependency`, `compose_dep`.
- **`llvm/llvm-project` @ `507de0cc365e4c6317d21fb08e298f742256a51f`:**
  - `llvm/lib/ProfileData/Coverage/CoverageMapping.cpp:252–439`: `MCDCRecord::findIndependencePairs`, `mcdc::TVIdxBuilder`, `MCDCRecordProcessor`.
  - `llvm/include/llvm/ProfileData/Coverage/CoverageMapping.h:688–701`: `Indices`, `NumTestVectors`, `HardMaxTVs`.
- **`gcc-mirror/gcc` @ `78c5290e696d76fdbe7f3b006df9145d1ed7927c`:**
  - `gcc/tree-profile.cc:113–153,391–576,871–952`: ROBDD masking-vector algorithm (`masking_vectors`, `find_conditions`) and `_t`/`_f`/`_mask` bitwise instrumentation.
- **`AdaCore/gnatcoverage` @ `8b3ccf5be798827c7a7ae0245e13e1cb5ba89a56`:**
  - `tools/gnatcov/sc_obligations.ads:76–161`: `Decision_Kind`, `SCO_Provider is (Compiler, Instrumenter, LLVM)`, `Fingerprint_Type`.
- **`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`**, **`ferrocene/ferrocene` @ `85d04a5bfcd57edb4e22df89d8d0eeb13a8ddc1d`**, **`apple/pkl` @ `069c891ac86067cd26c68d4647100e26c5ed5ba0`**, **`open-policy-agent/opa` @ `674d3362381e14b55069a7a5741eeb8489365c2f`**: Pinned upstream repositories.

### Peer-Reviewed Literature & Standards
- Carpenter, *The Logic of Typed Feature Structures*, Cambridge University Press, 1992.
- Attouche, Baazizi, Colazzo, Ghelli, Sartiani, & Scherzinger, *Validation of Modern JSON Schema: Formalization and Complexity*, POPL 2024, DOI `10.1145/3632891`.
- Cutler et al., *Cedar: A New Language for Expressive, Fast, Safe, and Analyzable Authorization*, OOPSLA 2024, DOI `10.1145/3649835`, `arXiv:2403.04651`.
- Sun et al., *Anvil: Verifying Liveness of Cluster Management Controllers*, USENIX OSDI 2024.
- Cai, Date, Gu, Rivera, Chajed, Padon, Xu, & Sun, *Welder: Compositional Liveness Verification of Cluster Control Planes*, ACM SOSP 2026, DOI `10.1145/3830418.3843868`.
- RTCA DO-178C / EUROCAE ED-12C (§ 6.4.4.2.b), DO-330, DO-333; FAA `CAST-10`, `CAST-12`, `CAST-17`, `CAST-32A`; EASA `AMC 20-193`.
- Chilenski & Miller, *Applicability of Modified Condition/Decision Coverage to Software Testing*, Software Engineering Journal 9(5):193–200, 1994, DOI `10.1049/sej.1994.0025`.
- Hayhurst, Veerhusen, Chilenski, & Rierson, *A Practical Tutorial on Modified Condition/Decision Coverage*, NASA/TM-2001-210876, May 2001.
- Kirner, *Towards Preserving Model Coverage and Structural Code Coverage*, EURASIP J. Embedded Systems 2009, Article 127945, DOI `10.1155/2009/127945`.
- Bordin, Comar, Gingold, Guitton, Hainque, & Quinot, *Object and Source Coverage for Critical Applications with the COUVERTURE Open Analysis Framework*, ERTS 2010.

### Executable Probes (Executed `2026-11-19`, `x86_64-linux`)

#### Probe 3A: `GCC 15.2.0` `-fcondition-coverage` & `-O0` vs. `-O2` Assembly Diff
```bash
# In /tmp/probe_mcdc/:
cat << 'EOF' > decide.c
int decide(int a, int b, int c) { if ((a && b) || c) { return 1; } return 0; }
EOF
cat << 'EOF' > main_branch.c
int decide(int,int,int);
int main(void) { return decide(1,1,0)+decide(0,0,0)+decide(0,0,1)-2; }
EOF
cat << 'EOF' > main_mcdc.c
int decide(int,int,int);
int main(void) { return decide(1,1,0)+decide(1,0,0)+decide(0,1,0)+decide(1,0,1)-2; }
EOF
gcc -O0 -fcondition-coverage -ftest-coverage -fprofile-arcs decide.c main_branch.c -o run_b && ./run_b && gcov -b --conditions run_b-decide
rm -f *.gcda *.gcno *.gcov
gcc -O0 -fcondition-coverage -ftest-coverage -fprofile-arcs decide.c main_mcdc.c -o run_m && ./run_m && gcov -b --conditions run_m-decide
rm -f *.gcda *.gcno *.gcov
gcc -O2 -fcondition-coverage -ftest-coverage -fprofile-arcs decide.c main_mcdc.c -o run_o2 && ./run_o2 && gcov -b --conditions run_o2-decide
gcc -O0 -S -fno-asynchronous-unwind-tables -fno-dwarf2-cfi-asm decide.c -o decide_O0.s
gcc -O2 -S -fno-asynchronous-unwind-tables -fno-dwarf2-cfi-asm decide.c -o decide_O2.s
```
Observed outputs on `gcc (Debian 15.2.0-14) 15.2.0` / `gcov 15.2.0`:
- `run_b` (`-O0`, 3 vectors): `Branches executed:100.00% of 6`, `Condition outcomes covered:83.33% of 6` (`condition 1 not covered (false)`).
- `run_m` (`-O0`, 4 vectors): `Branches executed:100.00% of 6`, `Condition outcomes covered:100.00% of 6`.
- `run_o2` (`-O2`, 4 vectors): `Branches executed:100.00% of 4`, `Condition outcomes covered:100.00% of 4` (2 source MC/DC outcomes silently folded away before instrumentation).
- `decide_O0.s` body: 3 conditional jumps (`cmpl $0,-4(%rbp); je .L2; cmpl $0,-8(%rbp); jne .L3; .L2: cmpl $0,-12(%rbp); je .L4`) + 1 `jmp .L5`.
- `decide_O2.s` body (0 branches):
```asm
decide:
    testl   %edi, %edi
    setne   %al
    testl   %esi, %esi
    setne   %cl
    andl    %ecx, %eax
    testl   %edx, %edx
    setne   %dl
    orl     %edx, %eax
    movzbl  %al, %eax
    ret
```

#### Probe 3B: `CUE` Default Non-Monotonicity & Controller Oscillation vs. Monotone Lattice (`CPython 3.13.15`)
- `(*'a' | S) & (*'b' | S)` under `U2`: `V=['a', 'b', 'c'], D=[] -> effective=['a', 'b', 'c']`.
- `(*'a'|'b') | (*'b'|'c')`: `before=['a', 'b']`, `after & !='a'=['b']`.
- Imperative 2-controller overwrite trace (`replicas=3` vs `replicas=7`): `[3, 7, 3, 7, 3, 7, 3]` (oscillates indefinitely).
- Monotone lower-bound lattice (`replicas >= 3` & `replicas >= 7`): `[0, 7, 7, 7, 7, 7, 7]` (converges to fixed point `7` at tick 1).

## Revalidation

1. **`CUE` `evalv3` & default specification:** Diff `cue-lang/cue` (`doc/ref/spec.md` around `Default values` and `internal/core/adt/default.go`) to check whether the `spec.md:785` `TODO` on nested marked-disjunction elimination is finalized and whether `evalv3` becomes the sole default evaluator.
2. **`Welder` / `Anvil` compositional verification:** Diff `anvil-verifier/anvil` (`src/kubernetes_cluster/proof/core.rs` and `src/controllers/composition/`) to track new verified built-in/custom controllers, transactional API-server models, or bounded-time convergence extensions.
3. **`GCC` `-O2 -fcondition-coverage` & `LLVM`/`rustc` MC/DC:** Re-run Probe 3A on newer `GCC` releases (and compare against `clang -O2 -fcoverage-mcdc` and `rustc -C instrument-coverage -Z coverage-options=mcdc` once stabilized) to verify whether pre-instrumentation folding still reduces reported condition counts (`6 → 4`) under optimization.
4. **`Cedar` Lean-to-Rust gap:** Inspect `cedar-policy/cedar-spec` (`cedar-lean/Cedar/Thm/`) and `cedar-policy/cedar` for any formal Rust verification replacing or augmenting Differential Random Testing.
5. **JSON Schema Draft successors:** Check whether post-2020-12 JSON Schema drafts deprecate or lexically restrict `$dynamicRef` to recover `PTIME` combined validation complexity.
