# Tarjan SCC Proof Sharding, Acyclic Interface Digests, and Incremental `.olean` Auditing

## Summary

Monolithic fresh-kernel proof replay—starting from an empty `Kernel.Environment` to check the entire transitive closure of `.olean` or export-format declarations in one process—hits severe multi-gigabyte memory walls on large verified crates (`lean4checker` caps parallel workers at `8` to prevent 32 GiB Mathlib OOM, while `nanoda_lib` materializes the entire `FxIndexMap` declaration arena in RAM). Non-fresh per-module checking (`lean4checker`'s `replayFromImports`) avoids reloading upstream proofs, but relies unconditionally on unverified serialized `.olean` imports (`finalizeImport`).

A sharded `.olean` auditor solves both scaling and zero-trust replay by condensing the global constant graph $G = (V, E)$ into maximal strongly connected components (SCCs) via Tarjan's $O(|V| + |E|)$ algorithm and replaying each shard $S_i$ freshly in isolation with cross-shard dependencies $a \notin S_i$ stubbed:

1. **Kernel Soundness Boundary for `.axiomInfo` Stubbing**: Because `TheoremVal` constants never delta-unfold (`constant_info::has_value(false)` in `type_checker::is_delta`), stubbing upstream `TheoremVal` lemmas as `.axiomInfo` is exact for proof checking and K-like `Eq.rec`, **except** when a downstream computational `DefinitionVal` eliminates a non-K subsingleton proof (such as `Acc.rec`) into `Type`. Upstream `DefinitionVal` constants unfolded during reduction must remain intact or be decoupled behind behavioral spec theorems.
2. **Defeating Split-Brain Cycle & Drift Exploits**: Fresh per-shard replay alone fails to stop cross-shard mutual recursion (`thmA : False := thmB` in shard 0, `thmB : False := thmA` in shard 1). Global link checking closes this with four invariants: **disjoint constant ownership**, **strict topological rank monotonicity** ($\tau(\text{owner}(a)) < \tau(S_i)$), **canonical per-constant interface digests** $H_{\text{sig}}(c)$ (omitting `TheoremVal` bodies so upstream proof edits keep 100% of downstream shard caches valid), and **root target-manifest completeness**.
3. **Bottom-Up Trust Aggregation**: Rather than trusting `.olean`-cached `exportedAxiomsExt` tables, the linker propagates verified shard axioms bottom-up across the condensation DAG in $O(|V_{\text{DAG}}| + |E_{\text{DAG}}|)$ time to validate exact transitive axiom and FFI/assembly trust waivers.

## Applicability

These findings govern fresh-kernel proof auditors, incremental verification caches, and cross-crate certificate linkers targeting Lean 4 (`.olean` / `lean4export`) and Rocq (`.vo` / `.vos` / `coqchk`) across large multi-module developments where:

- Full single-process fresh replay (`lean4checker --fresh` or monolithic `nanoda_lib`) exceeds host physical RAM limits or destroys incremental verification throughput when an upstream proof body changes;
- Trust policy requires **zero unverified `.olean` or `.vo` imports** (forbidding `finalizeImport`-only checking and Rocq `-norec`/`-admit` exemptions unless explicitly audited as a waiver);
- Target crates enforce **partial/unsafe rejection** (closing the `Kernel.Environment.replay` gap that silently skips `isPartial`/`isUnsafe` declarations) and **statement-origin completeness** (`Comparator.compareAt`, `SafeVerify`) across all exported verification obligations.

In the subject set, `leanprover/lean4` (`5b6d9d25edb59b0f9264ecd3136c44cca7cfafe0`), `leanprover/lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`), `ammkrn/nanoda_lib` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`), and `digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`) define the Lean 4 replay and external-checker substrate; `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`) and `GasStationManager/SafeVerify` (`b291b588a53999a7e837dda61c7dbfe8c550c814`) define target-manifest matching and axiom-set enforcement; `rocq-prover/rocq` (`ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76`) supplies the mature `coqchk` library-digest and opaque-table design; and Tarjan (1972, DOI `10.1137/0201010`) defines the linear-time condensation decomposition.

## Findings

### 1. Memory and Trust Bottlenecks in Existing Monolithic Fresh Checkers

Basis: source + documentation + derived

Current open-source Lean 4 and Rocq standalone checkers make an uncomfortable binary trade-off between trusted memory blowup and untrusted incremental imports:

- **`lean4checker` (`leanprover/lean4checker`, `Main.lean`, lines `14-60, 120-150`)**:
  - In **default module mode** (`replayFromImports`, lines `14-36`), `lean4checker` calls `importModulesCore` + `finalizeImport` (`lines 29-30`) on all imported `.olean` dependencies *without* replaying them, and replays only `newConstants` from the target module's private `.olean` part (`lines 33-35`). Because `defaultNumWorkers := 8` spawns concurrent tasks each loading near-complete environments, the source comment explicitly warns of out-of-memory failures on 32 GiB machines checking Mathlib (`lines 57-60`). More importantly, trusting `finalizeImport` allows an unverified upstream `.olean` to smuggle arbitrary inconsistent axioms or malformed kernel objects.
  - In **`--fresh` mode** (`replayFromFresh`, lines `38-40, 120-126`), `lean4checker` imports the entire closure via `withImportModules` and replays every entry of `env.constants.map₁` into `mkEmptyEnvironment`, restricting execution to a **single module** (`targetModules.length != 1` throws an error at `lines 121-123`) and holding the entire project's expression DAG in one single-threaded kernel arena.
- **`nanoda_lib` (`ammkrn/nanoda_lib`, `src/env.rs`, lines `218-276`)**: `Env` backs all parallel checking threads with a single parsed `FxIndexMap<NamePtr, Declar>` (`declars`) arena (`lines 218-231`), enforcing linear visibility ordering via an index slice `EnvLimit::ByIndex(cutoff)` (`lines 247-276`). Parallel workers therefore avoid cross-thread duplication of the arena on one host, **but** peak resident memory still scales with the full monolithic export file parsed upfront, and incremental caching across distributed builds is absent without sharding.
- **Rocq `coqchk` / `rocqchk` (`rocq-prover/rocq`, `checker/checkLibrary.ml`, lines `56-65, 120-137, 342-460`; `checker/safe_checking.ml`, lines `31-58`)**: Rocq partitions `.vo` files into explicit segments (`summary`, `library`, `opaques`, `checkLibrary.ml`, lines `342-344`), ignores serialized VM bytecode (`vmlibrary` is recomputed from verified terms in `safe_checking.ml`, lines `26-34`), binds dependencies by `Safe_typing.vodigest` (`seg_md.hash`, `checkLibrary.ml`, line `377`), detects cyclic library imports via `LibrarySet.mem dir seen` (`line 393`), and supports partial skipping via `-norec` / `-admit` (`lines 430-454`). However, Rocq shards only at coarse source-file `.vo` granularity (`checkLibrary.ml`, line `377`)—so changing one theorem inside a large library file alters `seg_md.hash` and invalidates downstream library digests—and `unsafe_import` (`safe_checking.ml`, lines `52-58`) admits entire upstream `.vo` libraries rather than individual signatures.

### 2. Tarjan SCC Call-Graph Sharding and Kernel Edge Completeness

Basis: normative (`10.1137/0201010`) + source (`leanprover/lean4/src/Lean/Replay.lean`, `src/kernel/type_checker.cpp`) + derived

To split a monolithic Lean 4 environment $E$ into minimal independently replayable shards without losing mutual recursion or breaking inductive type invariants, an auditor constructs a directed dependency graph $G = (V, E)$ over all constant names $c \in \text{dom}(E)$ and computes maximal SCCs via Tarjan's DFS algorithm (Tarjan 1972, DOI `10.1137/0201010`) in $O(|V| + |E|)$ time.

#### 2.1 Mandatory Edge Closure Beyond Naive `Expr.getUsedConstants`

Inspecting `Lean.Kernel.Environment.replay` (`leanprover/lean4/src/Lean/Replay.lean`, lines `74-198`) and `src/kernel/type_checker.cpp` reveals **four edge classes** that any dependency graph builder *must* include before running Tarjan's algorithm:

1. **Syntactic type and value constant references** (`ci.getUsedConstantsAsSet`, `Replay.lean`, line `77`): edges $c \to d$ for every `ConstantInfo` name $d$ appearing in `c.type`, `c.value` (for `defnInfo`, `thmInfo`, `opaqueInfo`), or constructor/recursor types.
2. **Indivisible mutual inductive blocks** (`Replay.lean`, lines `102-129, 149-166`): `Kernel.Environment.replay` processes mutual inductive types atomically (`Declaration.inductDecl lparams nparams types false`, line `121`) using `info.all` and `ci.inductiveVal!.ctors`, and checks `ctorInfo` and `recInfo` by structural equality against kernel-synthesized descriptors (`checkPostponedConstructors`, `checkPostponedRecursors`, lines `149-166`). Furthermore, `type_checker::reduce_proj_core` (`type_checker.cpp`, lines `415-425`) reads `mk_val.get_induct()` from structure constructors. Thus, every inductive family $I$, all members of `I.all`, every constructor $k \in \text{ctors}(I)$, and its recursor(s) `I.rec` **must be co-located in the exact same SCC** by adding bidirectional clique edges among $\{I.\text{all}, \text{ctors}, \text{recs}\}$.
3. **Implicit quotient dependency** (`Replay.lean`, lines `130-134`): `Quot.lift` and `Quot.ind` depend on `Eq` outside direct term references when initializing quotient reduction (`replayConstant \`Eq`, line `133`), requiring an explicit edge `Quot* -> Eq`.
4. **Implicit string-literal kernel dependencies** (`Replay.lean`, lines `187-192`; `type_checker.cpp`, lines `409-410`): When reducing a projection or matching on a string literal (`Expr.lit (.strVal _)`), the kernel calls `string_lit_to_constructor`, expanding literals into `String.ofList [Char.ofNat n, ...]`. As `Replay.lean` explicitly documents (`lines 189-190`), `getUsedConstants` **does not report `String.ofList` or `Char.ofNat`**, so any shard containing or reducing a string literal must inject implicit dependencies on `String.ofList` and `Char.ofNat` (or include the core prelude shard).

#### 2.2 Closing the Silent `isPartial` / `isUnsafe` Skip in `Replay.lean`

In `leanprover/lean4/src/Lean/Replay.lean` (`lines 181-184`), `replay` filters out constants with `!ci.isUnsafe && !ci.isPartial` without error. In a zero-trust sharded auditor, **every** reachable `ci.isUnsafe` or `ci.isPartial` declaration must trigger immediate rejection (unless explicitly whitelisted as an external trust waiver), because partial recursive definitions elaborate using `Lean.ofReduceBool` / `opaque` inhabitance axioms that bypass kernel totality checks.

### 3. Per-SCC Signature-Stubbed Replay and the `TheoremVal` Unfolding Boundary

Basis: source + derived

Replaying a shard $S_i$ freshly requires loading only $S_i$'s internal declarations plus its **external stub boundary** $\partial(S_i) = \{ a \notin S_i \mid \exists c \in S_i,\ (c, a) \in E \}$. How each cross-shard dependency $a \in \partial(S_i)$ is represented in the fresh kernel environment obeys a sharp soundness/performance boundary derived from Lean 4's C++ kernel (`declaration.h`, `type_checker.cpp`, `environment.cpp`) and `nanoda_lib` (`env.rs`, `tc.rs`):

| Cross-Shard Constant Kind $a \in \partial(S_i)$ | Stubbing Representation in Shard $S_i$ | Kernel Reduction Behavior (`whnf_core` / `is_delta`) | Soundness & Fidelity Trade-Off |
| --- | --- | --- | --- |
| **`TheoremVal` (general `Prop` lemma)** | Replaced by `Declaration.axiomDecl { name, levelParams, type, isUnsafe := false }` | Identical to `TheoremVal`: `has_value(false)` (`declaration.h:448`) refuses delta-unfolding | **Exact except** for non-K subsingleton elimination (`Acc.rec`) into `Type` inside `DefinitionVal` |
| **`TheoremVal` (used in `Acc.rec` / well-founded recursion)** | Must retain **`TheoremVal`** proof body (or `Acc` proof witness) in computational cone | `reduce_recursor` inspects structural witness of `Acc.intro` (`Acc.rec` reduces on proof terms!) | Stubbing an `Acc` termination proof as `.axiomInfo` stalls `is_def_eq` for callers reducing the recursive function |
| **`DefinitionVal` (needed computationally)** | Must retain **`DefinitionVal`** body (or split via `#[spec]` theorem) | `is_delta` unfolds `DefinitionVal` via `unfold_definition_core` (`type_checker.cpp:543-570`) | Stubbing as `.axiomInfo` breaks `rfl`, `decide`, and type-level computation |
| **`DefinitionVal` (encapsulated behind verified spec)** | Replaced by `.axiomInfo` for body-free specs, paired with stubbed `.axiomInfo` of its spec theorem | Caller reduces against spec theorem only (never unfolds concrete function body) | Breaks definitional cones **if and only if** every downstream user reasons strictly propositionally via spec axioms |
| **`InductiveVal` / `ConstructorVal` / `RecursorVal`** | **Cannot** be stubbed as `.axiomInfo` | `reduce_proj_core` & `reduce_recursor` require exact inductive/constructor/recursor tables | Must replay the full inductive declaration block in $\partial(S_i)$ (compact type signatures only) |

#### 3.1 Why `.axiomInfo` Stubbing of `TheoremVal` Is Almost—But Not Universally—Transparent

In `leanprover/lean4/src/kernel/declaration.h` (`lines 221-224` vs. `447-449`), `declaration::has_value()` returns `true` only for definitions, whereas `constant_info::has_value(bool allow_opaque = false)` returns:
`is_theorem() || is_definition() || (allow_opaque && is_opaque())`, and `type_checker::is_delta` (`type_checker.cpp`, lines `543-551`) passes `allow_opaque = false`. Despite `constant_info::has_value` returning `true` for `is_theorem()`, theorem expressions occur almost exclusively in proof positions (`Prop`), where Lean 4's kernel proves definitional equality via **proof irrelevance** (`is_def_eq_proof_irrel`) without ever unfolding the theorem body. `nanoda_lib` mirrors this directly (`src/env.rs`, lines `322-326`; `src/tc.rs`, lines `1171-1177`), treating `Declar::Theorem` with `ReducibilityHint::Opaque` during delta comparisons.

The critical exception documented in Lean 4 metatheory (Carneiro, *Lean4Lean*, LIPIcs.TYPES.2025.2, DOI `10.4230/LIPIcs.TYPES.2025.2`) is **subsingleton elimination from `Prop` into `Type`**—prototypically `Acc.rec` (well-founded recursion) and `Eq.rec`:
- For `Eq.rec`, Lean supports **K-like reduction** (`recursor_val::is_k()`, `declaration.h`, line `345`): `Eq.rec` reduces on *any* proof of `a = a`, even an opaque `.axiomInfo` stub, provided the indices are definitionally equal.
- For `Acc.rec` (non-K inductive in `Prop` eliminating into `Type`), `reduce_recursor` requires the major premise to evaluate in WHNF to `Acc.intro ...`. If a function $f$ in shard $S_i$ uses well-founded recursion backed by an auxiliary termination theorem `f_wf : WellFounded lt` stored in upstream shard $S_j$, and a downstream shard $S_k$ checks a definitional equality `f 3 = 6` via `rfl`, then stubbing `f_wf` as `.axiomInfo` prevents `Acc.intro` from appearing in WHNF, causing `rfl` to fail! Therefore, **non-K `Prop`-to-`Type` eliminators (`Acc.rec`, `Nat.decLe`-style constructive witnesses)** require retaining the computational `TheoremVal` slice (or including `f_wf` inside the `DefinitionVal` transitive computational cone) whenever `is_def_eq` reduces `f`.

### 4. Adversarial Link-Graph Exploits and Compositional Soundness Invariants

Basis: derived + execution

Replacing monolithic replay with parallel per-shard replay creates a distributed **link-graph attack surface** where every individual shard passes `Kernel.Environment.replay` in isolation, yet the global crate environment is unsound or incomplete. A sound sharded auditor must enforce four global link invariants after replaying every shard:

#### Exploit Class 1: Split-Brain Mutual Recursion Cycle
Suppose an attacker exports two shards $S_0 = \{\texttt{Exploit.A}\}$ and $S_1 = \{\texttt{Exploit.B}\}$:
- Shard $S_0$ declares `Exploit.B : False` as a trusted cross-shard `.axiomInfo` stub, and proves `theorem Exploit.A : False := Exploit.B`. **Replaying $S_0$ in a fresh kernel succeeds.**
- Shard $S_1$ declares `Exploit.A : False` as a trusted cross-shard `.axiomInfo` stub, and proves `theorem Exploit.B : False := Exploit.A`. **Replaying $S_1$ in a fresh kernel succeeds.**
Together, `False` has been proved with **zero genuine axioms**.

**Defense (Disjoint Ownership + Strict Topological Rank Certificate):**
Assign every shard $S_i$ an explicit integer rank $\tau(S_i)$ and a claimed set of owned definitions $\text{Defs}(S_i)$. The global linker checks:
1. **Disjointness**: $\forall i \ne j,\ \text{Defs}(S_i) \cap \text{Defs}(S_j) = \emptyset$. (Without disjointness, an attacker could create duplicate definitions of `Exploit.A` at rank `0` and rank `2` to spoof acyclicity!)
2. **Strict Rank Monotonicity**: $\forall S_i,\ \forall a \in \partial(S_i),\ \exists! j,\ a \in \text{Defs}(S_j) \wedge \tau(S_j) < \tau(S_i)$.

#### Exploit Class 2: Universe-Parameter Permutation, Private Collision, or Signature Drift
Even when the shard DAG is acyclic, an attacker can match a stub by symbol name while altering its universe parameter order (`levelParams := [v, u]` instead of `[u, v]`), changing `DefinitionVal.safety`, swapping `Prop` vs. `Type` annotations, or exploiting module-system private name collisions (cf. `Replay.lean`, lines `85-96`, where duplicate private theorem entries require exact equality on `name`, `type`, `levelParams`, and `all`).

**Defense (Canonical Interface Digest $H_{\text{sig}}$):**
Every shard entry binds each external stub $a \in \partial(S_i)$ to `(provider_shard_id, expected_digest)` where:
$$H_{\text{sig}}(c) = \text{SHA-256}\big(\text{encode}(\text{name}(c),\ \text{kind}(c),\ \text{levelParams}(c),\ \text{type}(c),\ \text{inductMeta}(c),\ \text{body?}(c))\big)$$
Here $\text{body?}(c)$ is included for transparent `DefinitionVal` constants (and non-K `Acc` witnesses in computational cones), and **omitted (`None`) for ordinary `TheoremVal` constants**. Consequently:
- Permuting `[u, v] -> [v, u]` or mutating a `DefinitionVal` immediately breaks $H_{\text{sig}}(c)$ and triggers re-verification;
- Editing only a proof term inside an upstream `TheoremVal` (`proof_v1 -> proof_v2`) preserves $H_{\text{sig}}(c)$ identically, guaranteeing **100% cache reuse across all downstream shards**.
By contrast, Rocq's `Safe_typing.vodigest` (`checkLibrary.ml`, line `377`) hashes the entire compiled library segment (`seg_md.hash`) per `.vo` file rather than per-constant interface digests.

#### Exploit Class 3: Omitted-Export and Weakened-Obligation Attacks
An attacker may omit a failing verification target from all shards or weaken its exported theorem type. Calling the target-manifest gate (`Comparator.compareAt`, `Compare.lean`, lines `67-109`; `SafeVerify`, `Main.lean`, lines `42-66`) on the union of owned shard exports guarantees every expected specification `DefinitionVal` and target `TheoremVal` is present in $\bigcup_i \text{Defs}(S_i)$ with exact structural equality (`challengeConst == solutionConst`).

#### Compositional Soundness Theorem (Derived)
If every shard $S_i$ passes `Kernel.Environment.replay` with only standard kernel rules plus stubbed declarations $\partial(S_i)$ and recorded direct axioms $A_0(S_i)$, and the global link checker verifies disjointness, strict topological rank $\tau$, exact per-stub digest match $H_{\text{sig}}(a)$, and target-manifest completeness, then by induction over $\tau(S_i)$ there exists a single valid global `Kernel.Environment` accepting every constant in $\bigcup_i \text{Defs}(S_i)$ using **only** axioms in $\bigcup_i A_0(S_i)$.

### 5. Untrusted `.olean` Axiom Metadata vs. Bottom-Up DAG Trust-Waiver Aggregation

Basis: source + execution + derived

In `leanprover/lean4/src/Lean/Util/CollectAxioms.lean` (`lines 96-146`), `exportedAxiomsExt` serializes precomputed `(Name × Array Name)` axiom tables into `.olean` files via `exportEntriesFnEx` (`lines 126-145`) so downstream modules perform binary search (`ExportedAxiomsState.find?`, lines `102-111`) without traversing imported bodies. **An untrusted `.olean` can falsify `exportedAxiomsExt` entries.**

Under Tarjan SCC sharding, the auditor computes `A_0(S_i)` directly during per-shard fresh replay by inspecting every `Declaration.axiomDecl` encountered inside $S_i$ (excluding the verified stub set $\partial(S_i)$) plus any explicit external-trust annotations (such as FFI/inline-assembly wrappers). Once all shards pass replay, a lightweight coordinator pass walks the condensation DAG in increasing $\tau$ order (`O(|V_DAG| + |E_DAG|)` time, keeping only axiom-name bitsets in RAM):
$$\text{TrustSummary}(S_i) = A_0(S_i) \cup \bigcup_{a \in \partial(S_i)} \text{TrustSummary}(\text{owner}(a))$$
Root verification obligations inherit exact transitive axiom closures $\text{TrustSummary}(\text{owner}(r))$, which the policy gate checks against the crate's allowed base axioms (`{propext, Quot.sound, Classical.choice}`) and explicit signed waivers.

### 6. Empirical Probe Verification of Sharding, Caching, and Exploit Rejection

Basis: execution

Executing `probe_scc_sharding.py` (embedded in **Evidence**) against five adversarial and incremental scenarios confirms all link-graph invariants deterministically:

```text
case1_valid_scc_count= 3 proof_edit_reused_downstream= True
case2_split_brain_cycle= REJECT_RANK_CYCLE:0->1
case3_duplicate_ownership= REJECT_DUPLICATE_OWNERSHIP:Exploit.A
case4_uparam_drift= REJECT_DIGEST_DRIFT:Spec.add
case5_omitted_root= REJECT_OMITTED_ROOT:Missing.obl unwaived= REJECT_UNWAIVED_AXIOMS:Target.main:Ffi.oracle waived= OK
```

1. **SCC condensation & proof-edit cache preservation**: Two mutually recursive lemmas (`Lemma.a`, `Lemma.b`) collapse into 1 SCC alongside `Spec.add` and `Target.main` (`3` shards total); mutating `Lemma.a`'s proof body (`proof_v1 -> proof_v2`) leaves `H_sig(Lemma.a)` unchanged (`proof_edit_reused_downstream=True`).
2. **Split-brain cycle rejection**: Two shards with cyclic stubs (`Exploit.A <-> Exploit.B`) are caught immediately by `REJECT_RANK_CYCLE:0->1`.
3. **Duplicate-ownership rejection**: Attempting to define `Exploit.A` in two shards fails with `REJECT_DUPLICATE_OWNERSHIP:Exploit.A`.
4. **Universe-parameter permutation detection**: Reordering `("u",)` to `("v", "u")` on `Spec.add` fails with `REJECT_DIGEST_DRIFT:Spec.add`.
5. **Omitted-root & transitive trust-waiver gating**: Missing root target triggers `REJECT_OMITTED_ROOT:Missing.obl`; injecting `Ffi.oracle` into `Lemma.b` propagates transitively to `Target.main`, failing `REJECT_UNWAIVED_AXIOMS:Target.main:Ffi.oracle` unless `Ffi.oracle` is explicitly whitelisted (`waived=OK`).

## Boundaries

- **Known not to apply**: The claim that `Lean.Kernel.Environment.replay` rejects `partial` or `unsafe` constants is **known not to apply** to `leanprover/lean4` at commit `5b6d9d25edb59b0f9264ecd3136c44cca7cfafe0` (`Replay.lean`, line `183` silently skips `!ci.isUnsafe && !ci.isPartial` rather than throwing), and the claim that `TheoremVal` bodies can *always* be stubbed as `.axiomInfo` transparently is **known not to apply** when a downstream `DefinitionVal` reduces a non-K subsingleton elimination (such as `Acc.rec`) over that proof term.
- **Unsupported**: Splitting a mutual `InductiveType` block, its `ConstructorVal` entries, or its `RecursorVal` across distinct replay shards via `.axiomInfo` stubs is **unsupported** by Lean 4's kernel because `Replay.lean` (`lines 102-129, 149-166`) and `type_checker.cpp` (`reduce_proj_core`, lines `415-425`) require matching inductive/constructor/recursor kernel descriptors.
- **Not examined**: Wall-clock peak RSS measurements and replay speedups across full multi-million-line Lean 4 libraries (such as Mathlib or large Rust verification exports) under live `lean4checker` / `nanoda_lib` parallel worker pools were **not examined** experimentally; memory-ceiling behavior of monolithic replay is cited from `lean4checker` (`Main.lean`, lines `57-60`), and link-graph soundness invariants were executed via the standalone Python verifier `probe_scc_sharding.py`.
- **Unknown**: Quantitative cache hit-rate distributions for downstream shards under realistic `DefinitionVal` specification refactoring vs. pure `TheoremVal` proof edits across multi-crate Rust verification corpora remain **unknown**.

## Evidence

### Primary Upstream Sources

| Source | Immutable Revision / Identifier | Inspected Artifact & Lines | Role |
| --- | --- | --- | --- |
| `leanprover/lean4` | `5b6d9d25edb59b0f9264ecd3136c44cca7cfafe0` | `src/Lean/Replay.lean` (`74-198`), `src/Lean/Util/CollectAxioms.lean` (`56-146`), `src/kernel/declaration.h` (`221-224`, `345`, `447-449`), `src/kernel/type_checker.cpp` (`378-438`, `543-570`) | Source |
| `leanprover/lean4checker` | `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` | `Main.lean` (`14-60`, `120-150`) | Source / Documentation |
| `ammkrn/nanoda_lib` | `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` | `src/env.rs` (`218-276`, `322-326`), `src/tc.rs` (`1171-1177`) | Source |
| `digama0/lean4lean` | `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` | Formalized Lean 4 kernel checker (`10.4230/LIPIcs.TYPES.2025.2`) | Normative / Documentation |
| `rocq-prover/rocq` | `ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76` | `checker/checkLibrary.ml` (`56-65`, `120-137`, `342-460`), `checker/safe_checking.ml` (`31-58`) | Source |
| `leanprover/comparator` | `865edc14486c3388e9225daa971da8e157488c3e` | `Comparator/Compare.lean` (`45-109`) | Source |
| `GasStationManager/SafeVerify` | `b291b588a53999a7e837dda61c7dbfe8c550c814` | `Main.lean` (`17-66`) | Source |

### Peer-Reviewed Literature

- Robert Endre Tarjan, *Depth-First Search and Linear Graph Algorithms*, SIAM Journal on Computing 1(2):146–160 (1972), DOI `10.1137/0201010`.
- Mario Carneiro, *Lean4Lean: Verifying a Typechecker for Lean, in Lean*, TYPES 2025, LIPIcs, DOI `10.4230/LIPIcs.TYPES.2025.2` (arXiv `2403.14064`).

### Self-Contained Probe (`probe_scc_sharding.py`)

Executed `2026-11-20` with Python 3 (`python3 /tmp/probe_scc_sharding.py`, exit code `0`):

```python
#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json
from dataclasses import dataclass
from typing import Dict, List, Set, Tuple

@dataclass(frozen=True)
class ConstDecl:
    name: str; kind: str; uparams: Tuple[str, ...]; type_sig: str; value_expr: str
    deps: Tuple[str, ...]; explicit_axioms: Tuple[str, ...] = (); induct_block: Tuple[str, ...] = ()
    non_k_subsingleton_elim: bool = False

def sig_digest(c: ConstDecl) -> str:
    inc_body = c.kind == "defn" or (c.kind == "thm" and c.non_k_subsingleton_elim)
    p = {"name": c.name, "kind": c.kind, "uparams": list(c.uparams), "type_sig": c.type_sig,
         "induct_block": list(c.induct_block), "body": c.value_expr if inc_body else None}
    return hashlib.sha256(json.dumps(p, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def tarjan_sccs(nodes: List[str], edges: Dict[str, List[str]]) -> List[List[str]]:
    cnt, idx, low, st, on, out = 0, {}, {}, [], set(), []
    def sc(v: str) -> None:
        nonlocal cnt
        idx[v] = low[v] = cnt; cnt += 1; st.append(v); on.add(v)
        for w in edges.get(v, []):
            if w not in idx: sc(w); low[v] = min(low[v], low[w])
            elif w in on: low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop(); on.remove(w); comp.append(w)
                if w == v: break
            out.append(sorted(comp))
    for v in sorted(nodes):
        if v not in idx: sc(v)
    return out

@dataclass(frozen=True)
class ShardRecord:
    shard_id: int; rank: int; owned: Tuple[str, ...]
    stubs: Dict[str, Tuple[int, str]]; direct_axioms: Tuple[str, ...]

def build_shards(decls: Dict[str, ConstDecl]) -> List[ShardRecord]:
    edges = {n: list(c.deps) + [m for m in c.induct_block if m != n] for n, c in decls.items()}
    sccs = tarjan_sccs(list(decls.keys()), edges)
    owner = {n: i for i, comp in enumerate(sccs) for n in comp}
    recs = []
    for i, comp in enumerate(sccs):
        cset = set(comp)
        stubs = {d: (owner[d], sig_digest(decls[d])) for n in comp for d in edges[n] if d not in cset}
        axs = sorted({ax for n in comp for ax in decls[n].explicit_axioms})
        recs.append(ShardRecord(i, i, tuple(comp), stubs, tuple(axs)))
    return recs

def verify_link(shards: List[ShardRecord], decls: Dict[str, ConstDecl], roots: Set[str], allowed: Set[str]):
    by_id, owner = {s.shard_id: s for s in shards}, {}
    for s in shards:
        for n in s.owned:
            if n in owner: return False, f"REJECT_DUPLICATE_OWNERSHIP:{n}", {}
            owner[n] = s.shard_id
    missing = sorted(roots - set(owner))
    if missing: return False, f"REJECT_OMITTED_ROOT:{','.join(missing)}", {}
    tax = {}
    for s in sorted(shards, key=lambda x: x.rank):
        acc = set(s.direct_axioms)
        for sn, (pid, exp_d) in s.stubs.items():
            if owner.get(sn) != pid: return False, f"REJECT_UNKNOWN_STUB_OWNER:{sn}", {}
            if by_id[pid].rank >= s.rank: return False, f"REJECT_RANK_CYCLE:{s.shard_id}->{pid}", {}
            if sig_digest(decls[sn]) != exp_d: return False, f"REJECT_DIGEST_DRIFT:{sn}", {}
            acc |= tax[pid]
        tax[s.shard_id] = acc
    rsum = {r: set(tax[owner[r]]) for r in sorted(roots)}
    for r, axs in rsum.items():
        bad = sorted(axs - allowed)
        if bad: return False, f"REJECT_UNWAIVED_AXIOMS:{r}:{','.join(bad)}", rsum
    return True, "OK", rsum

def main() -> None:
    base = {
        "Spec.add": ConstDecl("Spec.add", "defn", ("u",), "Nat -> Nat -> Nat", "Nat.add", ()),
        "Lemma.a": ConstDecl("Lemma.a", "thm", ("u",), "Spec.add 1 1 = 2", "proof_v1", ("Spec.add", "Lemma.b")),
        "Lemma.b": ConstDecl("Lemma.b", "thm", ("u",), "Spec.add 2 2 = 4", "proof_v1", ("Spec.add", "Lemma.a")),
        "Target.main": ConstDecl("Target.main", "thm", ("u",), "TargetProp", "proof_main", ("Lemma.a", "Spec.add")),
    }
    shards = build_shards(base)
    ok1, m1, s1 = verify_link(shards, base, {"Target.main"}, {"propext"})
    assert ok1 and m1 == "OK" and s1["Target.main"] == set()
    edited = {**base, "Lemma.a": ConstDecl("Lemma.a", "thm", ("u",), "Spec.add 1 1 = 2", "proof_v2", ("Spec.add", "Lemma.b"))}
    ok1b, m1b, _ = verify_link(shards, edited, {"Target.main"}, {"propext"})
    assert ok1b and m1b == "OK"
    cyc = {"Exploit.A": ConstDecl("Exploit.A", "thm", (), "False", "Exploit.B", ("Exploit.B",)),
           "Exploit.B": ConstDecl("Exploit.B", "thm", (), "False", "Exploit.A", ("Exploit.A",))}
    cyc_sh = [ShardRecord(0, 0, ("Exploit.A",), {"Exploit.B": (1, sig_digest(cyc["Exploit.B"]))}, ()),
              ShardRecord(1, 1, ("Exploit.B",), {"Exploit.A": (0, sig_digest(cyc["Exploit.A"]))}, ())]
    ok2, m2, _ = verify_link(cyc_sh, cyc, {"Exploit.A"}, set())
    assert not ok2 and m2 == "REJECT_RANK_CYCLE:0->1"
    dup_sh = [ShardRecord(0, 0, ("Exploit.A",), {}, ()),
              ShardRecord(1, 1, ("Exploit.A", "Exploit.B"), {"Exploit.A": (0, sig_digest(cyc["Exploit.A"]))}, ())]
    ok3, m3, _ = verify_link(dup_sh, cyc, {"Exploit.A"}, set())
    assert not ok3 and m3 == "REJECT_DUPLICATE_OWNERSHIP:Exploit.A"
    drifted = {**base, "Spec.add": ConstDecl("Spec.add", "defn", ("v", "u"), "Nat -> Nat -> Nat", "Nat.add", ())}
    ok4, m4, _ = verify_link(shards, drifted, {"Target.main"}, set())
    assert not ok4 and m4 == "REJECT_DIGEST_DRIFT:Spec.add"
    ok5a, m5a, _ = verify_link(shards, base, {"Target.main", "Missing.obl"}, set())
    assert not ok5a and m5a == "REJECT_OMITTED_ROOT:Missing.obl"
    w_decls = {**base, "Lemma.b": ConstDecl("Lemma.b", "thm", ("u",), "Spec.add 2 2 = 4", "proof_v1", ("Spec.add", "Lemma.a"), explicit_axioms=("Ffi.oracle",))}
    w_sh = build_shards(w_decls)
    ok5b, m5b, _ = verify_link(w_sh, w_decls, {"Target.main"}, {"propext"})
    ok5c, m5c, _ = verify_link(w_sh, w_decls, {"Target.main"}, {"propext", "Ffi.oracle"})
    assert not ok5b and m5b == "REJECT_UNWAIVED_AXIOMS:Target.main:Ffi.oracle" and ok5c
    print("case1_valid_scc_count=", len(shards), "proof_edit_reused_downstream=", ok1b)
    print("case2_split_brain_cycle=", m2)
    print("case3_duplicate_ownership=", m3)
    print("case4_uparam_drift=", m4)
    print("case5_omitted_root=", m5a, "unwaived=", m5b, "waived=", m5c)

if __name__ == "__main__":
    main()
```

## Revalidation

1. **Rerun the SCC link-graph and trust-aggregation probe**:
   Extract the `probe_scc_sharding.py` block above to `/tmp/probe_scc_sharding.py` and run `python3 /tmp/probe_scc_sharding.py` (expected exit `0`, confirming all five cycle, duplicate-ownership, universe-drift, omitted-root, and trust-waiver checks).
2. **Audit `Kernel.Environment.replay` and `CollectAxioms` invariants on Lean toolchain updates**:
   Inspect `src/Lean/Replay.lean` (specifically the `!ci.isUnsafe && !ci.isPartial` filter, `Quot -> Eq`, and `String.ofList`/`Char.ofNat` string-literal prelude constants), `src/kernel/declaration.h` (`constant_info::has_value`), `src/kernel/type_checker.cpp` (`is_delta`), and `src/Lean/Util/CollectAxioms.lean` (`exportedAxiomsExt`) in `leanprover/lean4`. Any change to `TheoremVal` unfolding or `Acc.rec` kernel elimination directly affects Section 3.1's stubbing boundary.
3. **Verify external checker alignment (`nanoda_lib`, `lean4checker`, `coqchk`)**:
   Confirm `ammkrn/nanoda_lib` (`src/env.rs`, `src/tc.rs`) maintains `Theorem` non-delta-reducibility (`ReducibilityHint::Opaque` in `get_applied_def`) and inspect `leanprover/lean4checker` (`Main.lean`) or upstream `lean4`'s integrated `leanchecker` binary for native `.olean` parallel/fresh replay flags. For Rocq comparisons, inspect `checker/checkLibrary.ml` (`intern_from_file`, `recheck_library`) and `checker/safe_checking.ml` in `rocq-prover/rocq`.
