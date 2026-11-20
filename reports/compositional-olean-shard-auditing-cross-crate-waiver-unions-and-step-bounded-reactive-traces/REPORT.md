# Compositional `.olean` Shard Auditing, Cross-Crate Waiver Unions, and Step-Bounded Reactive Traces

## Summary

Auditing a multi-hundred-function verified crate in Lean 4 by replaying an entire transitive closure of `.olean` modules into a single kernel `Environment` hits two structural walls: memory exhaustion from loading every transitive helper's proof terms and IR ASTs, and critical-path serialization along deep call graphs. **Compositional SCC-sharded `.olean` kernel replay** resolves both bottlenecks by partitioning the crate's interprocedural dependency graph into strongly connected components (SCCs) yielding a condensation DAG, replacing cross-shard dependencies with proof-free **interface stubs** over a shared hash-pinned specification prelude $\mathcal{E}_0$, replaying each shard $S_i$ independently, and validating global soundness with a deterministic **shard linker**.

A compositional shard audit is only as sound as four mandatory invariants:

1. **Anti-spoofing via canonical export digests**: Name or pretty-printed type equality is unsound against local shadowing, differing `levelParams`, or primitive tampering. Both $\mathcal{E}_0$ and every stubbed contract $c$ must match a canonical export/DAG digest (`leanprover/comparator`'s `compareAt` over `lean4export` streams and `primitiveTargets`), ensuring stubbed axioms match exported kernel theorems (`ConstantInfo.thmInfo`).
2. **Acyclic post-replay dependency linking**: Because two shards can forge a mutual cycle (`S1` proves `p_1 : False` from stub `axiom p_2 : False` while `S2` proves `p_2 : False` from stub `axiom p_1 : False`), the linker must construct the dependency graph strictly from **kernel-replayed `collectAxioms` outputs** (never build manifests) and verify a topological ordering $\rho(S_j) < \rho(S_i)$ so cut-elimination reduces all proofs to approved standard axioms $\mathcal{A}_{\text{std}}$.
3. **Conservative cross-crate trust-waiver unions**: If crate $A$ waives an item via an axiom $w$ and crate $B$ treats $A$'s `.olean` as opaque, $B$'s dependent proofs are laundered as waiver-free ($\emptyset$). Manifests must compute a monotone **waiver-union semilattice** $W(C::f) = W_{\text{local}}(C::f) \cup \bigcup_{d \in \text{Stubs}(C::f)} W(\text{origin}(d))$ alongside checks for non-axiom Lean 4 TCB hatches (`@[implemented_by]`, `@[extern]`, `@[csimp]`, `unsafe`, `Lean.ofReduceBool`).
4. **Step-bounded prefix reactive traces vs. coinductive interaction trees**: OS event and interrupt loops never return, breaking terminating Hoare triples, whereas Lean 4 omits primitive `coinductive` types so `ITree` encodings incur heavy `M`-type / `Quot.sound` / `paco` proof overhead. By the **Alpern–Schneider** safety theorem, step-bounded prefix specs ($\forall \omega\, k,\, \mathsf{stepK}\;\omega\;k \neq \mathsf{Fault} \land \mathsf{TraceInv}\;k\;tr_k$) are **exact** for all safety properties and bounded-latency deadlines using only inductive `Nat` and `List`, while requiring an explicit event-progress bound or ranking ordinal whenever separating `Reacts` from silent `Diverges` ($\tau^\omega$) or proving unbounded liveness.

## Applicability

This report synthesizes architecture, primary source inspection, and formal trade-offs across six upstream repositories:

- **Lean 4 kernel, replay, and axiom tracking**: `leanprover/lean4` at `48f4bfec97ce283618d9a798d7fcf8f0798d8103` (`src/Lean/Replay.lean`, `src/Lean/Util/CollectAxioms.lean`), `leanprover/lean4checker` at `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` (`Main.lean`), `leanprover/comparator` at `865edc14486c3388e9225daa971da8e157488c3e` (`Main.lean`), and `digama0/lean4lean` at `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`.
- **Coinductive and small-step reactive semantics**: `DeepSpec/InteractionTrees` at `284d42248a3c5517cff9f582e335fcee2f6bdc1f` (`theories/Core/ITreeDefinition.v`) and `AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc` (`common/Behaviors.v`, `common/Smallstep.v`).
- **Scope and relation to prior reports**: Existing Lean kernel reports cover single-module `Environment.replay`, `.olean` determinism, metaprogramming import isolation, and `nanoda`/mmap throughput. This report extends them to (1) **compositional SCC-sharded `.olean` linking**, (2) **cross-crate waiver propagation**, and (3) **reactive trace specifications** in Lean 4. Target consumers are proof-system architects auditing multi-hundred-function verified Rust/Lean crates under workstation/CI RAM limits (16–32 GiB) and formalizers verifying non-terminating OS dispatch loops, MMIO polling loops, or device-driver interrupt handlers.

## Findings

### 1. Memory and Serialization Bottlenecks in Monolithic and Per-Module Replay

Basis: source + derived

Direct inspection of `leanprover/lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`, `Main.lean:14-60`) and `leanprover/lean4` (`48f4bfec97ce283618d9a798d7fcf8f0798d8103`, `src/Lean/Replay.lean:33-155`) highlights two bottlenecks:

1. **Monolithic single-environment replay (`replayFromFresh`)**:
   ```lean
   unsafe def replayFromFresh (module : Name) : IO Unit := do
     Lean.withImportModules #[{module}] {} fun env => do
       discard <| (← mkEmptyEnvironment).replay' env.constants.map₁
   ```
   Loading a crate root pulls every transitive `ConstantInfo`—lowered IR ASTs, `omega`/`bv_decide` certificates, and auxiliary `_proof_k` declarations—into a single sequential `Kernel.Environment`, giving $O(\sum_i |P_i|)$ runtime and cumulative peak RAM.
2. **Per-module worker replay (`replayFromImports`)**:
   ```lean
   let parts ← readModuleDataParts fnames
   let (mod, _) := parts[0]
   let (_, s) ← importModulesCore mod.imports |>.run
   let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
   ...
   let env' ← env.replay' newConstants
   ```
   `defaultNumWorkers : Nat := 8` (`Main.lean:57-60`) explicitly warns: *"avoid OOM on machines with 32GB RAM when checking large projects like Mathlib, where each worker loads a near-complete environment."* Worse, `finalizeImport` trusts `mod.imports` without re-checking them in that worker (requiring whole-project verification and disk integrity), and deep call chains $f_1 \to \dots \to f_N$ keep upstream proof modules resident in every downstream worker's RSS. Furthermore, `Main.lean:18-35` loads all three `.olean` levels (exported, server, and private) and replays `parts[parts.size-1]` (the most private part subsuming prior levels), so every tactic proof term in upstream imports contributes to downstream worker RSS unless severed by interface stubs.

### 2. SCC Condensation and Content-Addressed Interface Stubbing

Basis: derived

Partition the crate's call/dependency graph $G = (V, E)$ via Tarjan's $O(|V| + |E|)$ algorithm into maximal SCCs yielding condensation DAG $\mathcal{D} = (\{S_1, \dots, S_m\}, E_{\mathcal{D}})$:

- **Singleton vs. mutually recursive shards**: Acyclic items form singleton shards ($|S_i| = 1$); mutually recursive items share one shard $S_i$ proved with a common fuel/termination measure so internal recursion never requires cyclic axioms.
- **Proof-free interface stubs over shared prelude $\mathcal{E}_0$**: Audit the shared specification base $\mathcal{E}_0$ (operational IR semantics, memory model, machine types) **once** from `mkEmptyEnvironment`. For every cross-shard dependency $(S_i \to S_j) \in E_{\mathcal{D}}$, shard $S_i$ imports a generated stub over $\mathcal{E}_0$ instead of $S_j$'s proof `.olean`:
  ```lean
  -- Generated proof-free stub for cross-shard dependency g ∈ S_j (imports ONLY ℰ_0)
  axiom Stub.g_spec : ∀ (args : ...), VerificationResult ...
  ```
  Peak worker RSS drops from $O(|\mathcal{E}_0| + \sum_{j \le i} |\text{Proof}(S_j)|)$ to $O(|\mathcal{E}_0| + |\text{Proof}(S_i)| + \sum_{(S_i \to S_j)} |\tau_j|)$, enabling parallel builds and kernel audits independent of call-graph depth. Because `Stub.g_spec` omits $g$'s lowered IR body and tactic proof certificate, an upstream function whose proof term spans megabytes of bitvector/`omega` reflection adds only a few hundred bytes of signature AST to downstream shards.

### 3. Anti-Spoofing Interface Verification via Canonical Export Digests

Basis: normative + source + derived

Replacing `.olean` imports with stubs risks **spec-stub spoofing** via shadowed identifiers, mismatched `levelParams`, or redefined kernel primitives. `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`, `Main.lean:233-302`) establishes why name/string checks fail:

1. `primitiveTargets` (`Main.lean:233-266`) pins 26 kernel constants (`Nat`, `Nat.add`, ..., `String`, `Char`, `List`, `eagerReduce`, `optParam`, `autoParam`, `semiOutParam`, `outParam`) and `builtinTargets` (`Main.lean:267-271`) pins `Quot`/`Quot.{mk,lift,ind}`. Without verifying that every shard leaves `primitiveTargets` and `builtinTargets` identical to $\mathcal{E}_0$, a rogue shard could redefine `Nat.add` or `optParam` locally while matching surface theorem names.
2. In `leanprover/lean4` (`src/Lean/Replay.lean:84-97`), `replayConstant` skips duplicate `.thmInfo` declarations only when `name`, `type`, `levelParams`, and `all` match syntactically *within* one environment where referenced constants agree identically.

**Mandatory stub-binding invariant**: Pin $\mathcal{E}_0$ by SHA-256 of its replayed `.olean`/export stream, verify zero shadowing or redefinition of $\mathcal{E}_0$ or `primitiveTargets` in any shard, and bind every contract $c$ by canonical export digest:
$$H_{\text{iface}}(c) = \text{SHA256}\big(\text{canonicalExport}_{\mathcal{E}_0}(c.\text{levelParams},\; c.\text{type})\big)$$
(or direct `Comparator.compareAt` over `lean4export` DAGs, `Main.lean:284`). The linker accepts stub $a$ only when matched to a unique exported `.thmInfo` $t$ with $H_{\text{iface}}(a) = H_{\text{iface}}(t)$ and identical `levelParams` order.

### 4. Acyclic Cross-Shard Dependency Linking and Soundness Cut-Elimination

Basis: derived + normative

Even with exact signature digests, two shards can forge `False` via a mutual cycle: `S1` consumes `axiom p_2 : False` and proves `theorem p_1 : False := p_2`, while `S2` consumes `axiom p_1 : False` and proves `theorem p_2 : False := p_1`. Both pass `lean4checker` and `lean4lean` in isolation!

**Linker acyclicity & cut-elimination protocol**:

1. **Kernel-derived axiom edges**: In `leanprover/lean4` (`src/Lean/Util/CollectAxioms.lean:37-74`), `CollectAxioms.collect` reads cached `extFind?` entries on imported modules before inspecting `env.checked.get.find?`. The linker must bypass untrusted `extFind?` metadata for audited shards and invoke `CollectAxioms.collect` over the replayed `Kernel.Environment` (`env.checked`) for every exported theorem $t \in S_i$.
2. **Realized graph & strict topological numbering**: Build
   $$E_{\text{link}} = \big\{ (S_i \to S_j) \;\big|\; \exists t \in \text{Exports}(S_i),\; a \in \text{collectAxioms}(t) \cap \text{Stubs}(S_i),\; \text{producer}(a) = S_j \big\}$$
   and check existence of $\rho : \{S_1,\dots,S_m\} \to \mathbb{N}$ such that $(S_i \to S_j) \in E_{\text{link}} \implies \rho(S_j) < \rho(S_i)$ (rejecting all cycles including self-loops $S_i \to S_i$, so intra-shard stubs cannot prove themselves).
3. **Cut-elimination soundness**: By substitution closure of typing in Lean's Calculus of Inductive Constructions (`digama0/lean4lean` `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, Carneiro *TYPES 2025* DOI `10.4230/LIPIcs.TYPES.2025.2`), well-founded induction on $\rho(S_i)$ replaces every stub `axiomDecl` with its lower-ranked kernel-checked `thmDecl`, yielding a single closed derivation in $\mathcal{E}_0$ using only $\mathcal{A}_{\text{std}} = \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.

### 5. Conservative Cross-Crate Trust-Waiver Unions and Non-Axiom Escape Hatches

Basis: source + derived

If Crate `A` proves `A.mmio_read` using an explicit trust waiver $w_1$ and Crate `B` imports `A`'s interface contract to prove `B.poll_device` with zero local waivers, treating `A`'s `.olean` as unwaived launders $B$'s proof as waiver-free ($\emptyset$).

- **Waiver-union semilattice**: Every contract symbol $s$ binds $(H_{\text{iface}}(s), W(s))$ where $W(s)$ is the set of `(crate_id, crate_rev, item_path, waiver_kind, spec_hash)` records:
  $$W(C :: f) = W_{\text{local}}(C :: f) \;\cup\; \bigcup_{a \in \text{collectAxioms}_{\text{replayed}}(f) \setminus \mathcal{A}_{\text{std}}} W(\text{origin}(a))$$
  Taking the shard-level union $\widehat{W}(S_i) = \bigcup_{f \in S_i} W_{\text{local}}(f) \cup \bigcup_{a \in \text{Axioms}(S_i) \setminus \mathcal{A}_{\text{std}}} W(\text{origin}(a))$ is **soundly conservative** (never omits a real trust assumption, though a pure helper sharing a multi-item SCC inherits its sibling's waiver unless split into a lower singleton SCC).
- **Non-axiom Lean 4 TCB hatches**: `CollectAxioms.lean:56-67` records `.axiomInfo` nodes and proof-embedded compiler axioms (`Lean.ofReduceBool`, `Lean.trustCompiler` from `native_decide`, plus `sorryAx`), but does not reject `@[implemented_by]`, `@[extern]`, `@[csimp]`, or `unsafe`/`partial` attributes stored in environment extensions. The shard auditor must check **both** `collectAxioms` (`Main.lean:285` in `comparator`) and environment extensions so runtime extraction or reflection cannot diverge from kernel definitions.

### 6. Step-Bounded Prefix Reactive Trace Specifications vs. Coinductive Interaction Trees

Basis: normative + source + derived

Non-terminating OS event and interrupt loops make terminating Hoare triples unusable (`{P} loop {Q}` holds vacuously for diverging loops; `[P] loop [Q]` is unprovable). Two formalisms address this:

- **Coinductive `ITree` and CompCert `Behaviors.v`**: `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`, `common/Behaviors.v:41-55`) distinguishes `Terminates | Diverges | Reacts: traceinf -> program_behavior | Goes_wrong`. `DeepSpec/InteractionTrees` (`284d42248a3c5517cff9f582e335fcee2f6bdc1f`, `theories/Core/ITreeDefinition.v:30-43`; Xia et al., *POPL 2020*, DOI `10.1145/3371119`) defines `Variant itreeF` (`RetF | TauF | VisF`) and `CoInductive itree := go { _observe : itreeF itree }` with `paco` bisimulation (Hur et al., *POPL 2013*, DOI `10.1145/2429069.2429093`). Because Lean 4's kernel omits primitive `coinductive` types, `ITree` requires `M`-type/`Nat`-indexed approximations + `Quot` (`Quot.sound`, `Classical.choice`, `funext`), blocking kernel `whnf`/`rfl` execution and complicating shard composition.
- **Step-bounded finite-prefix reactive traces**: Quantify inductively over arbitrary input schedules $\omega : \mathbb{N} \to \iota$ and finite step counts $k : \mathbb{N}$:
  ```lean
  inductive StepOutcome (σ ε : Type) where | ok (next : σ) (events : List ε) | fault
  def PrefixSafe (step : ι → σ → StepOutcome σ ε) (s₀ : σ) (TraceInv : List ε → Prop) : Prop :=
    ∀ (ω : Nat → ι) (k : Nat), ∃ s_k tr_k, runReactive step ω s₀ [] k = some (s_k, tr_k) ∧ TraceInv tr_k
  ```

| Obligation Class | Step-Bounded Prefix (`∀ ω k`) | Coinductive `ITree` / `Behaviors` | Lean 4 Kernel Overhead |
| :--- | :--- | :--- | :--- |
| **All 1-safety invariants** (UB freedom, state/capability invariants, MMIO protocol order) | **100% Exact** (Alpern–Schneider closure) | Exact | `Nat.rec` from 1-step invariant (`0` coinduction axioms). |
| **Bounded-latency deadlines** ("IRQ at step $i$ emits `Ack` within $\le B$ steps") | **100% Exact** (safety over $k + B$ prefix) | Expressible via `Tau`-counted bisimulation | Pure `Nat` arithmetic over finite traces. |
| **Compositional shard linking** | **Direct** (body matches finite-step shard postcondition) | Requires lifting leaf helpers into `ITree` + `eutt` | Reuses SCC `.olean` stubs directly. |
| **Separating `Reacts` vs. silent `Diverges` ($\tau^\omega$)** | Needs explicit $B$-step event-progress bound | Native (`Tau`-guarded coinductive observation) | Inductive if $\exists B,\, \forall s \in \mathsf{Inv},\, \text{emits } \ge 1 \text{ event in } \le B$ steps. |
| **Unbounded fairness / $\square\lozenge$ liveness** | **Known not to apply** | Native (with ranking / transfinite coinduction) | Out of scope for pure finite prefixes. |
| **Effect-handler algebra (`interp_bind`)** | Awkward fuel re-indexing | Native (`eutt`, DOI `10.1145/3371119`) | Use `ITree` when handler equational theory dominates. |

By **Alpern & Schneider** (*Inf. Process. Lett.* 21(4):181–185, 1985, DOI `10.1016/0020-0190(85)90056-0`), an $\omega$-property $P$ is a safety property iff every violating $\sigma \notin P$ has a bad finite prefix $\sigma[0..k]$. Thus all seL4-style kernel invariants (Klein et al., *SOSP 2009*, DOI `10.1145/1629575.1629596`), CompCert `not_wrong` traces (Leroy, *CACM 2009*, DOI `10.1145/1538788.1538814`), and Bedrock2 MMIO prefix specs (Erbsen et al., *PLDI 2021*, DOI `10.1145/3453483.3454065`) are **100% captured** inductively by `∀ ω k` with constant proof size independent of $k$: verifying $10^9$ reactive iterations costs the exact same single-step proof obligation as verifying $1$ iteration, while exposing each helper invoked inside the interrupt handler as an ordinary finite-step SCC shard contract.

## Boundaries

- **Primitive `coinductive` kernel types in Lean 4**: Native `CoInductive`/`CoFixpoint` declarations as in `DeepSpec/InteractionTrees` (`ITreeDefinition.v:41`) are **unsupported** by the Lean 4 kernel (`48f4bfec97ce283618d9a798d7fcf8f0798d8103`).
- **Unbounded $\square\lozenge$ liveness and fairness**: Proving unbounded liveness without a step ceiling $B$ or ranking ordinal is **known not to apply** to pure `∀ ω k` prefix specs (Alpern–Schneider duality, DOI `10.1016/0020-0190(85)90056-0`).
- **Silent spin (`Diverges`) vs. productive `Reacts` without progress bounds**: Without a bounded-step event emission guarantee, a bare `∀ ω k, runReactive ≠ none` spec is **known not to apply** as a hang check against infinite silent stuttering.
- **Binary `.olean` parser exploits**: Running `lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`, `readModuleDataParts` at `Main.lean:26`) alone leaves memory-corruption resistance against malformed `.olean` binaries **unsupported** without out-of-process text export (`comparator` + `lean4export` + external kernel).
- **PKI and multi-org cache signing**: Signing key management and remote artifact cache distribution for cross-crate waiver manifests were **not examined**.
- **Optimal SCC shard batching granularity**: Exact worker RAM vs. process-startup crossover across future Lean 4 module-system `.olean` compaction changes remains **unknown** without workload benchmarking.

## Evidence

- **`leanprover/lean4`** (`48f4bfec97ce283618d9a798d7fcf8f0798d8103`): `src/Lean/Replay.lean:33-155` (`replayConstant` duplicate-`.thmInfo` check lines `90-97`); `src/Lean/Util/CollectAxioms.lean:15-83` (`extFind?` cache vs. `env.checked.get.find?`).
- **`leanprover/lean4checker`** (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`): `Main.lean:14-36` (`replayFromImports`), `38-40` (`replayFromFresh`), `57-60` (`defaultNumWorkers := 8` 32GB OOM note).
- **`leanprover/comparator`** (`865edc14486c3388e9225daa971da8e157488c3e`): `Main.lean:233-271` (`primitiveTargets`, `builtinTargets`), `277-302` (`verifyMatch`, `Comparator.compareAt`, `Comparator.checkAxioms`).
- **`digama0/lean4lean`** (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`): Formalized Lean 4 kernel checker and metatheory (Carneiro, *TYPES 2025* LIPIcs 384, DOI `10.4230/LIPIcs.TYPES.2025.2`, arXiv `2403.14064`, DOI `10.48550/arXiv.2403.14064`).
- **`DeepSpec/InteractionTrees`** (`284d42248a3c5517cff9f582e335fcee2f6bdc1f`): `theories/Core/ITreeDefinition.v:30-43` (Xia et al., *POPL 2020*, DOI `10.1145/3371119`; Hur et al., *POPL 2013*, DOI `10.1145/2429069.2429093`).
- **`AbsInt/CompCert`** (`2685140bf72c959446981fb99b5e44a8975021bc`): `common/Behaviors.v:41-55` (`program_behavior`, `not_wrong`), `common/Smallstep.v` (Leroy, *CACM 2009*, DOI `10.1145/1538788.1538814`).
- **Additional Papers**: Alpern & Schneider *IPL 1985* DOI `10.1016/0020-0190(85)90056-0`; Klein et al. *SOSP 2009* DOI `10.1145/1629575.1629596`; Erbsen et al. *PLDI 2021* DOI `10.1145/3453483.3454065`.

## Revalidation

1. **Upstream `Lean.Replay` and `CollectAxioms` drift check**:
   ```bash
   curl -fsSL https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Replay.lean | grep -n -C 4 "thmInfo info'"
   curl -fsSL https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Util/CollectAxioms.lean | grep -n -C 4 "extFind?"
   ```
2. **Adversarial shard-linker test matrix**: Before accepting compositional audit verdicts, confirm rejection on (A) cyclic cross-shard `False` proofs (`S1`: `p_2 ⊢ p_1`, `S2`: `p_1 ⊢ p_2`), (B) shadowed helper / `levelParams` stub spoofing caught by `H_iface` digest mismatch, (C) cross-crate waiver laundering where clean consumer `B.g` imports waived `A.f` and must report `w_A ∈ W(B.g)`, and (D) non-axiom hatches (`@[implemented_by]`, `native_decide` / `Lean.ofReduceBool`).
3. **Inductive prefix reactive-loop probe (Lean 4 minimal self-contained theorem)**:
   ```lean
   inductive Outcome (σ ε : Type) where | ok : σ → List ε → Outcome σ ε | fault
   def runK {σ ε ι : Type} (step : ι → σ → Outcome σ ε) (ω : Nat → ι) (s : σ) (tr : List ε) :
       Nat → Option (σ × List ε)
     | 0     => some (s, tr)
     | k + 1 => match step (ω k) s with
                | .ok s' ev => runK step ω s' (tr ++ ev) k
                | .fault   => none

   theorem prefixSafe_of_stepInv {σ ε ι : Type}
       (step : ι → σ → Outcome σ ε) (Inv : σ → Prop) (TraceInv : List ε → Prop)
       (h_append : ∀ tr ev, TraceInv tr → TraceInv (tr ++ ev))
       (h_step : ∀ i s, Inv s → ∃ s' ev, step i s = .ok s' ev ∧ Inv s')
       (s₀ : σ) (h₀ : Inv s₀) (tr₀ : List ε) (htr₀ : TraceInv tr₀) :
       ∀ ω k, ∃ s_k tr_k, runK step ω s₀ tr₀ k = some (s_k, tr_k) ∧ Inv s_k ∧ TraceInv tr_k := by
     intro ω k
     induction k generalizing s₀ tr₀ with
     | zero => exact ⟨s₀, tr₀, rfl, h₀, htr₀⟩
     | succ k ih =>
       obtain ⟨s', ev, h_eq, h_inv'⟩ := h_step (ω k) s₀ h₀
       simpa [runK, h_eq] using ih s' h_inv' (tr₀ ++ ev) (h_append tr₀ ev htr₀)
   ```
