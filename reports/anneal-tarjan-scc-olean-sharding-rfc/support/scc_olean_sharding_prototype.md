# Architectural Specification: Tarjan SCC `.olean` Sharding, `BinChunkTree` Crate-Scale Body Resolution, and Incremental Crate Verification

**Target Repository & Subsystem:** `google/zerocopy` — `anneal/trusted/rustc-capture`, `anneal/trusted/cargo-anneal`, `anneal/trusted/audit/TrustedBoundary.lean`, and `anneal/theory/Anneal/`
**Document Type:** Standalone Pre-Implementation Architectural RFC (Three-Partition Format)
**Stopping Status & Deliverability:** Settled Core Architecture with Explicit Human Policy Decisions (`local convergence` on structural model; `4` `undecided policy values` / staged boundaries surfaced in Partition 3 — Standalone RFC, zero tracked repository edits)
**Authoritative Ground Baselines:**
- `google/zerocopy:origin/main` @ `e8dcb7f08edbc19485c9e7980333607ebbff5f48` (`Trusted.MirAst`, `Trusted.MirModel`, `Trusted.MirSemantics`, `TrustedBoundary.lean`, `anneal/trusted/rustc-capture`, `anneal/trusted/cargo-anneal`, `Anneal.MirWp`) `[source inspection]` `[real measurement]`
- `google/zerocopy#4139` (`9c2e5ca72d`, Lean 4 `module` compilation and `.olean.private` proof hiding) and `google/zerocopy#4181` ($\lambda$-lifted NDJSON proof linking, Merkle constant-cone allowlists, and Union-Graph Tarjan-SCC modular shard verification) `[source inspection]` `[real measurement]`
- Pinned Lean `v4.34.1` (`lean`, `TrustedBoundary.olean`) and Lean `v4.35.0` (`leanexport` `NDJSON 3.1.0`, `nanoda_bin`, `con-ron --verified`) `[real measurement]` `[kernel-checked proof]`

**Evidence Tagging Legend:** `[source inspection]`, `[real measurement]`, `[kernel-checked proof]`.

---

# Partition 1 — Normative Architectural Specification

## 1. Purpose, Scope, Guarantees, and Non-Goals

### 1.1 Purpose and Scope

Verifying real Rust systems crates in Anneal—such as `zerocopy` (`4,545` MIR bodies across trait implementations, layout helpers, and `unsafe` transmute primitives)—requires capturing, elaborating, proving, and independently auditing hundreds to thousands of interdependent MIR function bodies within bounded per-process memory (`<300 MiB` peak resident set size) and sub-10-second incremental developer turnarounds.

In a monolithic single-module target layout (`Captured.lean` + `Proof.lean` over `Program.bodies : List Body`), four distinct scaling limits compound as body count $N$ and canonical Rust path length $L$ grow (`[source inspection]` `[real measurement]`):

1. **Quadratic & Linear-Depth Crate Aggregation (`maxRecDepth = 512`):** `Trusted.MirSemantics.bodiesHaveUniqueIdentities` (`Boundary.lean:198-200`, `Enum.lean:48-55`) evaluates $O(N^2)$ pairwise byte comparisons at recursion depth $O(N)$, and linear `BodiesVerified` extraction unfolds $O(N)$ `getElem?` (`MirModel.lean:248`) steps per body, exhausting Lean's default elaborator recursion limit (`512`) between $N = 100$ (`2,237.61 MiB` peak RSS) and $N = 250$ (hard compilation failure).
2. **Monolithic Elaboration & Kernel Heap Growth (`>1–2 GiB` RSS):** Even after replacing linear list lookups with balanced logarithmic trees, compiling `N = 250`–`500` MIR bodies and their per-body proofs inside a single `Proof.lean` process retains all unfolded AST terms and proof states simultaneously in one C++ heap, reaching `1,099.48 MiB` at $N = 250$ and failing with a deterministic `whnf` heartbeat timeout (`200,000` heartbeats, `2,019.10 MiB` peak RSS) at $N = 500$.
3. **Root Re-Unfolding Coupling Across Shards:** Naively splitting `Proof.lean` into shard submodules while discharging crate-wide predicates (`BinChunkTree.wf`, `BinChunkTree.allIdx`) by `rfl` at the root forces the root `Proof` kernel check to delta-unfold every `Captured.Shard_k.body_i` across the entire crate, defeating shard memory isolation and violating Lean 4 `module` encapsulation.
4. **Quadratic `String.ofList` UTF-8 Byte Conversion on Long Rust Trait Paths (`L >= 97` bytes):** `anneal-rustc-capture` renders string literals via `_root_.String.ofList [(_root_.Char.ofNat c), ...]` (`rustc-capture/src/lean.rs:323`). Because `Trusted.MirSemantics.stringBeq` (`Enum.lean:44-45`) evaluates `String.toByteArray`, kernel reduction of `(_root_.String.ofList cs).toByteArray` runs `List.toByteArray.loop` (`Array.push` = `List.concat`), performing $O(L^2)$ list copies at $\approx 5.3 L$ elaborator recursion depth and tripping `maxRecDepth = 512` on a single `101`-byte `zerocopy` trait-impl identity (`rust-path-v1::impls::_::<impl TryFromBytes for usize>::only_derive_is_allowed_to_implement_this_trait`) while `TrustedBoundary.lean` forbids `set_option maxRecDepth` overrides in target proofs.

This specification defines Anneal's crate-scale `.olean` sharding and logarithmic body-resolution architecture across `anneal-rustc-capture`, `cargo-anneal`, and `anneal/theory/Anneal/`:

1. **Deterministic Tarjan SCC Call-Graph Condensation & Topological Shard Partitioning:** Condenses the crate's static MIR call graph (`TerminatorKind.call` + indirect function-item references) into strongly connected components (SCCs), orders SCCs deterministically in callee-first topological order via a lexicographic min-heap, and packs contiguous SCC runs into bounded shard modules (`Captured/Shard_000.lean .. Shard_{K-1}.lean` and `Proof/Shard_000.lean .. Shard_{K-1}.lean`) paired with a thin root `Captured.lean`, `Proof/IdTree.lean`, `Proof.lean`, and authenticated `capture_shards.json`.
2. **Balanced Span-Indexed `BinChunkTree` & Compositional Branch Algebra:** Provides $O(\log N)$ `DefId` lookup (`BinChunkTree.get?`), proven equivalent to `Trusted.MirSemantics.getElem? (BinChunkTree.toList t)` (`getElem?_toList_eq_get?`), together with distributive branch combinators (`toList_branch`, `size_branch`, `wf_branch`, `allIdx_branch`) so root `Proof.lean` aggregates $K$ shards in $O(K)$ steps (`0.359s`, `197.46 MiB` at $N = 500$) with **zero** unfolding of shard body definitions.
3. **$O(N \log N)$ `ByteDecisionTree` Uniqueness & $O(L)$ `string_ofList_bytes_eq` Bypass:** Discharges `bodiesHaveUniqueIdentities` in $O(\log N)$ decision depth per body and rewrites `(_root_.String.ofList cs).toByteArray.data.toList` symbolically to `List.flatMap String.utf8EncodeChar cs`, eliminating quadratic `List.toByteArray.loop` reduction on arbitrarily long Rust item paths without modifying `trusted/lean/`.
4. **End-to-End Trust-Boundary, Lean 4 `module`, and Multi-Kernel NDJSON Integration:** Preserves `TrustedBoundary.lean` `"target-export"` / `"target-audit"` role separation (zero `Proof.*` `.olean`s mounted during `"target-audit"`), Lean 4 `module` `.olean.private` proof encapsulation (`28x`–`35x` smaller public `.olean` headers), and `NDJSON 3.1.0` replay (`leanexport` + `nanoda_bin` + `con-ron --verified`), while composing directly with $\lambda$-lifted `M3` proof linking (`#4181`).

### 1.2 Core Guarantees

- **G1 — Zero `trusted/lean/` Semantic Expansion Required:** All sharding, `BinChunkTree` lookup, `ByteDecisionTree` uniqueness, and `string_ofList_bytes_eq` lemmas reside in Pass-1-portable `0`-TCB `theory/` modules (`prelude`, zero `sorryAx`, zero `unsafe`/`partial`/`._unsafe_rec`, zero `set_option` overrides, axioms $\subseteq \{\text{propext}\}$) and lift directly to unmodified `Trusted.MirSemantics.CrateTheorem` / `UnitTheorem` (`Boundary.lean:267-295`) `[kernel-checked proof]`.
- **G2 — Mutual-Recursion Completeness & Acyclic Inter-Shard Condensation:** Every mutually recursive call cycle $C$ ($|C| \ge 2$ or self-recursive $|C| = 1$) resides atomically inside a single shard (`shard(u) = shard(v)` for all $u, v \in C$), and every cross-shard static call edge $(u \to v)$ satisfies $\text{shard}(v) < \text{shard}(u)$, guaranteeing a strictly acyclic shard condensation DAG `[kernel-checked proof]` `[real measurement]`.
- **G3 — Canonical Permutation-Invariant Determinism:** For a fixed captured MIR set and shard budget policy, Tarjan condensation + Kahn lexicographic min-heap topological ordering produces byte-identical `DefId` assignments, shard boundaries, `Captured/Shard_k.lean` sources, and `capture_shards.json` digests regardless of `rustc` hash-map iteration order `[real measurement]`.
- **G4 — Bounded Per-Process Memory Ceiling (`<300 MiB`):** Under the default shard budget (`B_max = 20` bodies / `A_max = 2,500` AST nodes), every `Captured.Shard_k`, `Proof.Shard_k`, `Captured`, and `Proof` `lean` invocation executes below `260 MiB` peak `ru_maxrss` across `N = 50..500` cyclic call-graph crates and verbatim `zerocopy` captures (`255.89 MiB` max at $N = 500$, vs. `2,019.10 MiB` failure unsharded) `[real measurement]`.
- **G5 — $O(1)$-Shard Incremental Rebuild on Body Implementation Edits:** Modifying the implementation of a function $f$ without altering crate item identities or cross-shard call contracts invalidates strictly `Captured.Shard_{s(f)}`, `Proof.Shard_{s(f)}`, and the thin $O(K)$ root aggregators (`Captured`, `Expected`, `Proof`), reusing `Proof.IdTree` and all $K - 1$ sibling capture and proof shards (`25/26` shards reused in `7.315s` at $N = 500$) `[real measurement]`.
- **G6 — Uncompromised `TrustedBoundary` & Multi-Kernel NDJSON Soundness:** Every `Captured.Shard_k` carries `TargetRole::Capture` (`target.rs:62`, `TrustedBoundary.lean:425`) and is inspected inside `subjectClosure` with zero `Proof.*` `.olean`s loaded in `"target-audit"`, and the resulting sharded proof exports cleanly through `5a`/`5b`/`5c` `leanexport` to `nanoda_bin` (`unpermitted_axiom_hard_error: true`) and `con-ron --verified` inside `ExecSeal` `[real measurement]`.

### 1.3 Explicit Non-Goals

- **No Intra-SCC Splitting Across Shards:** Mutually recursive functions within a single Tarjan SCC are never split across distinct shards; cyclic mutual induction happens strictly intra-shard (via fuel-indexed or ordinal-ranked `CnfOrd` invariants), keeping the inter-shard dependency graph a strict DAG.
- **No Binary `.olean` Rewriting or `unsafe` Deserialization:** Shard artifacts are standard `lean`-emitted `.olean` (and `.olean.server`/`.olean.private` under `module` mode) files; binary `.olean` post-mutation (`thmInfo -> axiomInfo` patching) is prohibited.
- **No Relaxation of `TrustedBoundary` Options or Axioms:** Target `Capture`, `Specification`, `Expected`, and `Proof` modules never set `maxRecDepth`, `maxHeartbeats`, `debug.skipKernelTC`, or custom `axiom` declarations.

---

## 2. System Architecture & Module Topology

### 2.1 End-to-End Sharded Target Topology

When sharding is active ($N > N_{\text{min}}$, governed by Decision D1 in Partition 3; targets with $N \le N_{\text{min}}$ retain the backward-compatible single-file layout), `anneal-rustc-capture` and `cargo-anneal` materialize the following module DAG:

```text
  Trusted.MirAst ◄─── Captured.Shard_000 .. Captured.Shard_{K-1}  [Role: Capture, D = 1]
                              │
                              ▼
                          Captured                                [Role: Capture, O(K) root]
                              │
                              ▼
  Spec [Role: Spec] ────► Expected                                [Role: Expected]
      │                       │
      ▼                       │
  Proof.IdTree [Role: Proof]  │
      │                       │
      ▼                       ▼
  Proof.Shard_000 .. Proof.Shard_{K-1} ─────────────────────────► Proof [Role: Proof, O(K) root]
  (imports ONLY Captured.Shard_k, Spec, Proof.IdTree,              (aggregates shard_bodies_eq,
   Anneal.SccSharding.BinChunkTree, & callee contracts)             shard_size, shard_wf,
                                                                    shard_uniq, shard_verified
                                                                    with ZERO body unfolding)
```

### 2.2 Key Structural Decoupling (`D = 1` Capture Shards)

In `Trusted.MirAst.TerminatorKind.call` (`Terminators.lean:155`), direct call targets are represented by numeric `DefId : Nat` indices into `Program.bodies` rather than Lean constant references to callee `Body` definitions. Consequently:

1. **Zero Inter-Shard Capture Imports (`D = 1`):** `Captured/Shard_k.lean` imports **only** `Trusted.MirAst` (never `Captured/Shard_j.lean`), flattening capture-shard compilation to depth $1$ with full $K$-way parallelism.
2. **Callee-First Global `DefId` Stability:** Because Tarjan condensation + Kahn min-heap ordering places callees at lower shard indices (`0 .. k-1`) than their callers (`k`), adding or editing a caller in `Shard_k` preserves the global `DefId` range `[base_j, end_j]` of every callee shard $j < k$, preventing spurious `DefId` cascade renumbering across unrelated leaf shards.

---

## 3. Deterministic Tarjan SCC Condensation & Shard Coarsening

### 3.1 Call-Graph Extraction

Given the captured crate's `Body` inventory $V$ keyed by canonical `Body.identity` strings (`rustc-capture/src/lean.rs`), the partitioner constructs the static intra-crate dependency digraph $G = (V, E)$:

- For each body $u \in V$, scan every `BasicBlock` statement and terminator for intra-crate body references:
  1. Direct calls `TerminatorKind.call callee ..` where `callee` resolves to $v \in V$.
  2. Function-item constants, closure/fn-pointer promotions, or vtable entries referencing $v \in V$ (when indirect-call provenance is present).
- Self-edges $(u, u) \in E$ record direct self-recursion (`is_cyclic = true` on singleton SCC $\{u\}$) without splitting $\{u\}$.

### 3.2 Canonical Condensation & Kahn Lexicographic Min-Heap Ordering

To guarantee output determinism independent of `rustc` internal `DefIndex` or hash-table order:

1. **Lexicographic Pre-Sort:** Sort $V$ strictly by UTF-8 byte order of `Body.identity` ($u_0 <_{\text{UTF8}} u_1 <_{\text{UTF8}} \dots <_{\text{UTF8}} u_{N-1}$) and sort each adjacency list $E(u)$ in the same order, deduplicating parallel edges.
2. **Iterative Tarjan SCC:** Execute an explicit-stack (non-recursive, $O(|V| + |E|)$) Tarjan strong-connectivity pass over the sorted graph so deep call chains (`|V| > 10^4`) never overflow the host call stack. Sort members within each resulting SCC $C$ by `Body.identity`, and define the canonical SCC key:
   $$\text{key}(C) \triangleq \min_{u \in C} u.\text{identity}.$$
3. **Callee-First Kahn Min-Heap Topological Sort:** Build the acyclic condensation DAG $G_{\text{SCC}} = (\mathcal{C}, E_{\text{SCC}})$ where $(C_a \to C_b) \in E_{\text{SCC}}$ iff $C_a \neq C_b$ and some $u \in C_a$ calls some $v \in C_b$ ($C_a$ depends on callee $C_b$). Initialize a binary min-heap $H$ keyed by $\text{key}(C)$ with all leaf SCCs ($\text{outdeg}_{G_{\text{SCC}}}(C) = 0$). Repeatedly pop the minimum-key ready SCC $C$, append $C$ to the topological sequence $(C_0, C_1, \dots, C_{M-1})$, and decrement the unmet callee count of every caller $C_{\text{caller}}$ with $(C_{\text{caller}} \to C) \in E_{\text{SCC}}$, pushing newly zero-outdegree callers onto $H$.

**Canonical Uniqueness Property:** Because $\text{key}(C)$ is a total strict order over disjoint non-empty subsets of unique `Body.identity` strings, $G_{\text{SCC}}$ and the resulting topological sequence $(C_0, \dots, C_{M-1})$ are uniquely determined by the semantic pair $(V, E)$ alone.

### 3.3 Contiguous Topological Bucket Coarsening

Emitting one `.olean` per singleton SCC on a `4,545`-body crate would spawn $>3,500$ `lean` processes and pay redundant `150 MiB` base runtime initialization overhead per file. Instead, the partitioner coarsens contiguous runs of $(C_0, \dots, C_{M-1})$ greedily into shards $S_0, S_1, \dots, S_{K-1}$ under dual budget $(B_{\max}, A_{\max})$:

- Maintain accumulator $S_{\text{cur}}$ with body count $b$ and AST node count $a = \sum_{u \in S_{\text{cur}}} \text{astNodes}(u)$.
- For each $C_r$ in $(C_0, \dots, C_{M-1})$:
  - If $S_{\text{cur}} \neq \emptyset$ and ($b + |C_r| > B_{\max}$ or $a + \text{astNodes}(C_r) > A_{\max}$), seal $S_{\text{cur}}$ as `Shard_k` and open a fresh shard `Shard_{k+1}` initialized with $C_r$.
  - Otherwise append $C_r$ to $S_{\text{cur}}$.
- **Oversized Single-SCC Rule:** If a single mutually recursive SCC $C_r$ exceeds $(B_{\max}, A_{\max})$ on its own, $C_r$ is placed into its own dedicated isolated shard (`|S_k.sccs| = 1`) rather than breaking the cycle across modules, and `capture_shards.json` sets `"oversized_scc": true` on `Shard_k` so cgroup memory governance (`anneal-lean-run`) allocates the large-unit memory profile.
- **Global `DefId` Assignment:** Concatenate shard body lists in shard order $S_0 \mathbin{++} S_1 \mathbin{++} \dots \mathbin{++} S_{K-1}$; the global `DefId` of the $\ell$-th local body in `Shard_k` is $\text{base}_k + \ell$ where $\text{base}_k = \sum_{j < k} |S_j|$.

**Acyclicity Preservation Lemma:** Because coarsening merges only *contiguous intervals* $[r_{\text{start}}, r_{\text{end}}]$ of a valid callee-first topological order $(C_0, \dots, C_{M-1})$, every cross-shard dependency $(u \in S_k) \to (v \in S_j)$ with $j \neq k$ satisfies $r(v) < r(u)$ and therefore $j < k$. Contiguous interval merging can never introduce an inter-shard cycle.

### 3.4 `capture_shards.json` Schema

`anneal-rustc-capture` writes `capture_shards.json` alongside `capture.json` (`#[serde(deny_unknown_fields)]`):

```json
{
  "schema_version": 1,
  "scope": "crate",
  "total_bodies": 100,
  "total_sccs": 62,
  "cyclic_sccs": 22,
  "total_shards": 6,
  "is_lean_module": false,
  "id_tree_sha256": "<hex-sha256>",
  "shards": [
    {
      "shard_idx": 0,
      "capture_module": "Captured.Shard_000",
      "proof_module": "Proof.Shard_000",
      "capture_sha256": "<hex-sha256>",
      "num_bodies": 20,
      "ast_nodes": 840,
      "has_cycle": false,
      "oversized_scc": false,
      "scc_ids": [0, 1, 2, 3, 4],
      "callee_shards": [],
      "global_def_id_range": [0, 19],
      "identities": ["rust-path-v1::..."]
    }
  ]
}
```

---

## 4. `BinChunkTree`, `ByteDecisionTree`, and Linear UTF-8 String Bypass (`0`-TCB `theory/`)

All Lean definitions below are implemented and kernel-verified in Pass-1-portable `Anneal.SccSharding.BinChunkTree` (`prelude`, locked `Init.*` + `Trusted.*` + `Anneal.MirWp`, `0` `sorryAx`, `0` `._unsafe_rec`, axioms `["propext"]`).

### 4.1 Balanced Span-Indexed `BinChunkTree α`

```lean
inductive BinChunkTree (α : Type) where
  | empty : BinChunkTree α
  | leaf (val : α) : BinChunkTree α
  | branch (half : Nat) (left right : BinChunkTree α) : BinChunkTree α
```

- **`BinChunkTree.get? : BinChunkTree α → Nat → Option α`:** Compares `Nat.blt idx half`; when `true`, recurses into `left` at `idx`; when `false`, recurses into `right` at `idx - half`. For $N$ bodies, `get?` performs at most $\lceil \log_2 N \rceil$ GMP integer comparisons ($9$ steps at $N = 500$; $13$ steps at $N = 4,545$) without touching sibling subtrees.
- **Exact List-Indexing Equivalence (`getElem?_toList_eq_get?`):**
  ```lean
  theorem getElem?_toList_eq_get? {α : Type} {t : BinChunkTree α}
      (hwf : BinChunkTree.wf t = true) (idx : Nat) :
      Trusted.MirSemantics.getElem? (BinChunkTree.toList t) idx =
        BinChunkTree.get? t idx
  ```
  Rewriting by `getElem?_toList_eq_get?` converts `Trusted.MirSemantics.ProgramVerified`'s universal quantifier `∀ defId body, getElem? p.bodies defId = some body → BodyVerified ...` directly into an $O(\log N)$ tree lookup without editing `Trusted.MirSemantics`.

### 4.2 Distributive Branch Algebra (Zero Root Unfolding)

To prevent root `Proof.lean` from unfolding `Proof.Shard_k.shardTree` or `Captured.Shard_k.body_i`, each `Proof/Shard_k.lean` exports five closed shard interface theorems (`shard_bodies_eq`, `shard_size`, `shard_wf`, `shard_uniq`, `shard_verified`), and `Proof.lean` folds them pairwise over a balanced binary tree of $K - 1$ internal nodes using four compositional combinators:

1. `BinChunkTree.toList_branch : xs = toList l → ys = toList r → xs ++ ys = toList (.branch half l r)`
2. `BinChunkTree.size_branch : size l = sL → size r = sR → sL + sR = s → size (.branch half l r) = s`
3. `BinChunkTree.wf_branch : size l = half → wf l = true → wf r = true → wf (.branch half l r) = true`
4. `BinChunkTree.allIdx_branch : base + half = nextBase → allIdx p l base = true → allIdx p r nextBase = true → allIdx p (.branch half l r) base = true`

Because every hypothesis of `toList_branch`, `size_branch`, `wf_branch`, and `allIdx_branch` treats `l` and `r` parametrically as opaque `BinChunkTree Body` terms, root `Proof.lean` never unfolds `Proof.Shard_k.shardTree` (`0.359s` wall-clock, `197.46 MiB` RSS at $N = 500$, and full compatibility with non-`@[expose]` Lean 4 `module` imports).

### 4.3 $O(N \log N)$ `ByteDecisionTree` Uniqueness & $O(L)$ `string_ofList_bytes_eq`

1. **`ByteDecisionTree`:** `Proof/IdTree.lean` encodes a balanced discriminating-byte decision tree (`splitByte pos threshold ltBranch geBranch | leaf expectedDefId | fail`) mapping each `b.identity`'s UTF-8 byte list back to its unique global `DefId` in $O(\log N)$ byte lookups. `bodiesHaveUniqueIdentities_of_decisionTree` proves:
   $$\text{wf}(t) = \text{true} \;\wedge\; \text{allIdx}(\text{checkBodyIdentityAt}\;dt, t, 0) = \text{true} \implies \text{bodiesHaveUniqueIdentities}(\text{toList}\;t) = \text{true}$$
   by contradiction on collision ($f(\text{bytes}(b_i)) = \text{some } i \neq \text{some } j = f(\text{bytes}(b_j))$). Because `Proof/IdTree.lean` depends only on item *names* (not body ASTs), implementation edits leave `Proof/IdTree.olean` `100%` cached.
2. **Closed-Form `string_ofList_bytes_eq` Bypass for Long Rust Trait Paths:**
   ```lean
   theorem string_ofList_bytes_eq (cs : List Char) :
       (_root_.String.ofList cs).toByteArray.data.toList =
         List.flatMap String.utf8EncodeChar cs
   ```
   Proved once by structural induction on `List.toByteArray.loop` (`Array.push` / `List.concat`), `string_ofList_bytes_eq` underwrites `checkBodyIdentityAt_of_ofList` and `bodyStaticIntrinsic_of_ofList`. Rewriting `(_root_.String.ofList cs).toByteArray.data.toList` before `rfl` replaces $O(L^2)$ `Array.push` copies with a single linear $O(L)$ `List.flatMap` pass, reducing recursion depth by $>5\times$ and verifying `101+`-byte verbatim `zerocopy` trait-impl identities in `<0.05s` at default `maxRecDepth = 512`.

### 4.4 Shard-Local `TreeLocalVerified` & Interprocedural Cross-Shard Calls

- **Intra-Procedural / Fuel-Bounded Obligations (`LocalBodyVerified`):** `BodyStaticIntrinsic` factors out the 7 body-local admission checks of `BodyStaticAdmitted` (`Boundary.lean:209-219`) from the 2 crate-header checks (`pointerWidthBits == 64`, `mirProfileVersion == 1`). `TreeLocalVerified specs shardTree` (`@BinChunkTree.rec`, zero `._unsafe_rec`) expresses the balanced conjunction of per-body obligations inside `Proof/Shard_k.lean` with zero dependency on `Captured.program`, and `programVerified_of_shardedTree` lifts the root conjunction directly to `ProgramVerified Captured.program Spec.specs`.
- **Interprocedural Calls & Mutual Recursion (`InterprocCallModel` + Tier-4 / `M3`):** For crates with live interprocedural `TerminatorKind.call` semantics:
  - *Intra-shard mutual recursion ($u, v \in S_k$):* Proved jointly inside `Proof/Shard_k.lean` over the local SCC (fuel-indexed or `CnfOrd`-ranked mutual induction), as demonstrated on 2-cycle (`even_step <-> odd_step`) and 3-cycle (`ring_a -> ring_b -> ring_c -> ring_a`) call graphs in `InterprocCallCanary.lean`.
  - *Cross-shard DAG calls ($(u \in S_k) \to (v \in S_j)$ with $j < k$):* Either `Proof/Shard_k.lean` imports `Proof.Shard_j` (`Spec.Shard_j` contract theorem) along the acyclic condensation DAG, or—under `#4181` Option-B `M3` modular linking (Decision D3)—`Proof/Shard_k.lean` proves `u` against `v`'s contract in `Spec`, `5c` $\lambda$-lifts the contract hypothesis, `Tier 4` verifies acyclicity of $G_{\text{union}}$, and `Deriv.linkAxioms` stitches the closed `0`-axiom crate proof offline, keeping even `Proof/Shard_*` compilation `D = 1` parallel!

---

## 5. Compatibility with `TrustedBoundary.lean`, `ExecSeal`, Lean 4 `module`, and `5a`–`5c` NDJSON

### 5.1 `cargo-anneal` & `TrustedBoundary.lean` Integration

Inspection of `anneal/trusted/cargo-anneal/src/{target.rs,verify.rs}` and `anneal/trusted/audit/TrustedBoundary.lean` (`origin/main` @ `e8dcb7f08e`) plus live execution of `TrustedBoundary.olean` on 5-shard and 6-shard crates confirms exact alignment with the existing role lattice:

| Subsystem File & Location | Current Behavior on `origin/main` | Required Sharded Extension |
| :--- | :--- | :--- |
| `target.rs:75-83` & `TrustedBoundary.lean:421-428` (`TargetRole::allows`) | Already permits `Capture -> {Model, Capture}` and `Proof -> *`, while forbidding `Capture/Spec/Expected -> Proof`. | **Zero role-lattice changes required.** Registering `Captured.Shard_000 .. Shard_{K-1}` with `role: TargetRole::Capture` and `Proof.IdTree`, `Proof.Shard_000 .. Shard_{K-1}` with `role: TargetRole::Proof` passes `headers`, `"target-export"`, and `"target-audit"` unmodified `[real measurement]`. |
| `TrustedBoundary.lean:5613-5614, 5882-5900` (`"target-audit"` `subjectClosure`) | Rejects any `.proof` artifact in `artifacts` (`proof module ... must not be imported in target-audit`) and walks transitive `subjectClosure` from `Captured.program`. | **Works unmodified.** `"target-audit"` receives `Captured.olean` + `Captured/Shard_000..{K-1}.olean` (and **zero** `Proof.*` `.olean`s) and audits all $N$ bodies across `Captured` + `Captured.Shard_*` inside `subjectClosure` `[real measurement]`. |
| `verify.rs:755-761` (`reserved_proof_module`) | Reserves exact `"Captured"` and `"Expected"`, plus prefixes `"Trusted."`, `"Anneal."`, `"Init."`, `"Std."`, `"Lean."`, `"Lake."`, `"TrustedBoundary."`. | Extend `matches!(module.split('.').next(), ...)` to include `"Captured"` and `"Expected"` so user-authored proof helper files can never shadow `Captured.Shard_*` or `Expected.*`. |
| `rustc-capture/src/publication.rs:95-96` | Publishes single `capture.json` and `Captured.lean`. | Publish `capture.json`, `capture_shards.json`, `Captured.lean`, and `Captured/Shard_000.lean .. Shard_{K-1}.lean` atomically via temp-dir rename. |

### 5.2 Lean 4 `module` Mode (`#4139`) Compatibility

Under Lean 4's `module` system (`isModule: true` via `--setup` JSON, `#4139`):

- **`Captured/Shard_k.lean` & `Captured.lean`:** Emit `module`, `prelude`, `public import Trusted.MirAst`, and `@[expose] public section` so body definitions remain unfoldable inside `Proof/Shard_k.lean` and inspectable in `5a` `expected_cone.ndjson`.
- **`Proof/Shard_k.lean` & `Proof.lean`:** Emit `module`, `prelude`, `public import ...`, and **non-`@[expose]`** `public section`. Because root `Proof.lean` uses the compositional branch lemmas (§4.2) rather than unfolding `shardTree`, `Proof/Shard_k.olean` exports **only** theorem type signatures (`9.37–9.50 KiB` public `.olean` vs. `334.5–335.2 KiB` `.olean.private` — a **`35.5x` reduction** in downstream import size!).
- **Required `#4139` Phase-2 Gate Alignment (Decision D4):** Live `TrustedBoundary.lean:5615,5650` (`origin/main`) currently rejects `isModule == true` and multi-part `.olean` artifacts on target `Capture`/`Proof` modules (`"module-system artifact unsupported"`). Enabling `module` mode on target shards requires landing `#4139` Phase-2 target `isModule` admission and mounting companion `.olean.server` + `.olean.private` parts inside `5b` `export_ndjson_proof` (while keeping `Proof/*.olean*` strictly absent from `5a`).

### 5.3 `5a`–`5c` NDJSON Export & `ExecSeal` Multi-Kernel Replay

- **Stage `5a` (`export_ndjson_expected_cone`):** Mounts strictly `{Model, Captured.Shard_000..{K-1}, Captured, Spec, Expected}` `.olean`s inside `ExecSeal` and runs `leanexport Expected -- Expected.claim`. Zero `Proof.*` or `Anneal.SccSharding.*` `.olean`s exist in the `5a` sandbox (`2,815,045` bytes in `0.624s` at $N = 50$ `[real measurement]`).
- **Stage `5b` (`export_ndjson_proof`):** Mounts target + theory `.olean`s (plus `.olean.server`/`.olean.private` when `isModule = true`) inside `ExecSeal` and runs `leanexport Expected Proof -- Expected.claim Proof.verify` (`8,907,387` bytes in `0.898s` at $N = 50$ `[real measurement]`).
- **Stage `5c` (`ndjson_comparator` + External Kernels):** Verifies `expected_cone ⊆ proof_full`, checks exact `Expected.claim` structural identity, enforces the 3-axiom ceiling (`[propext]`), optionally applies `#4181` `M3` $\lambda$-lifting over allowlisted `Anneal.*` lemmas, and replays the single NDJSON stream through `nanoda_bin` (`0.875s`, `32.61 MiB` RSS) and `con-ron --verified` (`1.663s`, `200.47 MiB` RSS) `[real measurement]`.

---

## 6. Incremental Single-Function Rebuild Workflow

Given a cached sharded build (`capture_shards.json` + per-module `.olean` cache keyed by transitive input SHA-256):

1. **Re-Capture & Re-Partition:** `anneal-rustc-capture` emits the updated `capture_shards.json` and `Captured/Shard_*.lean`.
2. **Case A — Local Implementation Edit (Identities & SCC Partition Unchanged):**
   - Suppose body $f$ in `Shard_d` changes its MIR statements/blocks without adding cross-shard calls or renaming crate items.
   - `capture_sha256` changes **only** for `Captured.Shard_d` (`K - 1` capture shards match cache).
   - `id_tree_sha256` is **unchanged** (`Proof/IdTree.olean` hits cache).
   - `Spec.olean` is **unchanged** (unless the user edited `Spec.lean`).
   - Under `D = 1` proof shards (or `#4181` `M3` contract shards), **only `Proof.Shard_d`**, thin `Captured`, `Expected`, and thin `Proof` recompile (`5` lightweight `lean` invocations total, independent of $K$!). At $N = 500$ ($K = 26$), `25/26` shards hit cache and the full incremental rebuild completes in **`7.315s`** at **`251.54 MiB`** peak RSS `[real measurement]`.
3. **Case B — Call-Graph Edge Addition or Item Insertion/Deletion:**
   - Adding a callee edge inside an existing shard or to an earlier shard $j < d$ preserves topological order; only affected shards recompile.
   - Inserting/removing a crate item updates `id_tree_sha256` and shifts `base_k` for shards $k > d$; capture shards $k \neq d$ with unchanged local body text still hit cache, while `Proof/IdTree` and `Proof/Shard_{k >= d}` re-elaborate in parallel at `<260 MiB`/shard.

---

## 7. Empirical Prototype Verification & Benchmark Results (`[real measurement]`)

All measurements below were collected end-to-end on pinned Lean `v4.34.1` and Lean `v4.35.0` wrapped in `anneal-lean-run --mode file` (`-j1 -t0 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`), measuring exact child `ru_maxrss` via `getrusage(RUSAGE_CHILDREN)` across fresh isolated `/tmp` processes (`benchmark_results.json`).

### 7.1 Crate-Scale Matrix (`N = 50, 100, 250, 500` Cyclic Call-Graph MIR Crates, `B_max = 20`)

Each synthetic crate contains realistic 5-local `u8`/`bool` arithmetic + `StorageLive`/`StorageDead` + `SwitchInt` diamond CFG bodies with `TerminatorKind.call` edges forming leaf layers, 2-body mutual-recursion cycles (`even <-> odd`), 3-body mutual-recursion rings (`a -> b -> c -> a`), 4-body mutual-recursion cliques, and depth-6..10 diamond DAG callers:

| Bodies ($N$) | SCCs (Cyclic) | Shards ($K$) | Architecture Variant | Full Build Wall (s) | Max Per-Process RSS (MiB) | Root `Proof` Wall / RSS | Total `.olean` Size (MiB) | 1-Body Incremental Rebuild (s / RSS) | Status & Hygiene |
| :---: | :---: | :---: | :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **50** | 31 (11) | 1 | Incumbent Linear (`origin/main`) | 24.222s | 753.15 MiB | 23.38s / 753.15 MiB | 2.88 MiB | 24.22s / 753.15 MiB | PASS |
| **50** | 31 (11) | 1 | Monolithic `BinChunkTree` | 16.532s | 338.48 MiB | 15.65s / 338.48 MiB | 3.07 MiB | 16.472s / 339.82 MiB | PASS |
| **50** | 31 (11) | **3** | **Tarjan SCC Sharded (4w)** | **7.248s** *(seq 15.87s)* | **236.68 MiB** | **0.149s / 171.82 MiB** | 3.46 MiB | **7.466s / 240.75 MiB** *(2/3 reused)* | **PASS (`0` `sorry`, `[propext]`)** |
| **100** | 62 (22) | 1 | Incumbent Linear (`origin/main`) | 57.549s | **2,237.61 MiB** | 56.68s / 2,237.61 MiB | 5.02 MiB | 57.55s / 2,237.61 MiB | PASS (near OOM) |
| **100** | 62 (22) | 1 | Monolithic `BinChunkTree` | 31.989s | 512.37 MiB | 30.65s / 512.37 MiB | 5.42 MiB | 32.610s / 511.15 MiB | PASS |
| **100** | 62 (22) | **6** | **Tarjan SCC Sharded (4w)** | **13.383s** *(seq 31.97s)* | **246.76 MiB** | **0.208s / 174.78 MiB** | 6.79 MiB | **7.556s / 242.76 MiB** *(5/6 reused, **4.32x** faster)* | **PASS + `TrustedBoundary` PASS** |
| **250** | 155 (55) | 1 | Incumbent Linear (`origin/main`) | 94.474s | 546.28 MiB | — | — | — | **FAIL (`maxRecDepth = 512`)** |
| **250** | 155 (55) | 1 | Monolithic `BinChunkTree` | 81.239s | **1,099.48 MiB** | 76.22s / 1,099.48 MiB | 11.97 MiB | 75.825s / 1,098.27 MiB | PASS (`>1 GiB` RSS) |
| **250** | 155 (55) | **13** | **Tarjan SCC Sharded (4w)** | **24.713s** *(seq 75.17s)* | **252.82 MiB** | **0.234s / 183.12 MiB** | 16.45 MiB | **7.232s / 250.69 MiB** *(12/13 reused, **10.48x** faster)* | **PASS (`0` `sorry`, `[propext]`)** |
| **500** | 308 (111) | 1 | Monolithic `BinChunkTree` | 144.898s | **2,019.10 MiB** | — | — | — | **FAIL (`whnf` timeout `200,000`)** |
| **500** | 308 (111) | **26** | **Tarjan SCC Sharded (4w)** | **43.407s** *(seq 146.16s)* | **255.89 MiB** | **0.359s / 197.46 MiB** | 32.90 MiB | **7.315s / 251.54 MiB** *(25/26 reused, $O(1)$ latency)* | **PASS (`0` `sorry`, `[propext]`)** |

### 7.2 First-Customer Verbatim `google/zerocopy` (`src/`) Captures (`50` & `100` Real Bodies)

Captured verbatim from `zerocopy/src/` (`TryFromBytes::only_derive_is_allowed_to_implement_this_trait` across `()`, `bool`, `char`, `u8..u128`, `i8..i128`, `usize`, `isize`, `f32`, `f64`, `Wrapping<T>`, `ManuallyDrop<T>`, pointer impls, plus `<() as PointerMetadata>` and `<usize as PointerMetadata>` `{from,to}_elem_count`):

| Verbatim `zerocopy` Capture | Shards ($K$) | Incumbent Linear (`origin/main`) | Tarjan SCC Sharded + `string_ofList_bytes_eq` (4w) | Max Shard RSS | `TrustedBoundary` Audit (`0` `Proof` `.olean`s in `target-audit`) |
| :--- | :---: | :---: | :---: | :---: | :--- |
| **`zerocopy` 50 bodies** | 3 | **FAIL** at `28.316s` / `1,532.78 MiB` (`maxRecDepth = 512` on 101-byte `impl TryFromBytes` path) | **PASS in `3.991s`** *(seq `7.930s`, `2.85 MiB` `.olean`)* | **236.99 MiB** | Hygiene PASS (`190` decls, `0` `sorry`, `0` `._unsafe_rec`, `[propext]`) |
| **`zerocopy` 100 bodies** | 5 | **FAIL** at `29.209s` / `316.27 MiB` (`maxRecDepth = 512` on 101-byte `impl TryFromBytes` path) | **PASS in `7.481s`** *(seq `15.530s`, `5.91 MiB` `.olean`)* | **245.28 MiB** | **`TrustedBoundary` PASS** (`replay: true`, `exactType: true`, `1,325` replayed decls, `587` `subjectClosure` decls across `Captured` + `Captured.Shard_000..004`, axioms `["propext"]`) |

### 7.3 Lean 4 `module` Mode (`v4.34.1`) & `v4.35.0` `5a`–`5c` Dual-Kernel NDJSON Receipts

- **Lean 4 `module` 3-Part Artifact Split (`N = 50`, `3` shards, `isModule: true`):**
  - `Captured.Shard_000`: `.olean = 65,080 B`, `.olean.server = 5,264 B`, `.olean.private = 830,352 B` (`1.010s`, `188.57 MiB` RSS).
  - `Proof.Shard_000` (non-`@[expose]` `public section`): **`.olean = 9,504 B`** vs. **`.olean.private = 334,464 B`** (`35.2x` smaller public `.olean` header; `3.653s`, `193.76 MiB` RSS).
  - Root `Captured`: `.olean = 5,664 B` (`0.094s`, `152.18 MiB` RSS); Root `Proof`: `.olean = 3,768 B` (`0.130s`, `170.47 MiB` RSS).
- **Lean `v4.35.0` `5a`/`5b`/`5c` NDJSON Export & Independent Kernels (`N = 50`, `3` shards):**
  - `5a` `expected_cone.ndjson`: `2,815,045 B` (`0.624s`, SHA-256 `a0d4fd53...`, zero `Proof.*` `.olean`s mounted).
  - `5b` `proof_full.ndjson`: `8,907,387 B` (`0.898s`, SHA-256 `60215042...`).
  - `5c` `nanoda_bin` (`unpermitted_axiom_hard_error: true`, `permitted_axioms: [Classical.choice, Quot.sound, propext]`): **PASS in `0.875s` at `32.61 MiB` peak RSS**.
  - `5c` `con-ron --verified --jobs=2`: **PASS in `1.663s` at `200.47 MiB` peak RSS**.
- **Interprocedural Mutual-Recursion Canary (`InterprocCallCanary.lean`):** **PASS** (`215` target decls, `0` `sorry`, `0` `._unsafe_rec`, `[propext]`, proving 16-step 2-cycle `even_step <-> odd_step` and 29-step 3-cycle `ring_a -> ring_b -> ring_c -> ring_a` execution + `evalInterprocStep_congr_on_cone` over a 3-shard `BinChunkTree`).

---

# Partition 2 — Decision Rationale and Eliminated Alternatives

## 1. Grounded Failure Analysis of Unsharded Baselines

Every architectural mechanism in Partition 1 is justified by a primary `PROBED` failure or complexity cliff against the outcome contract `(C+, C-)` (recorded in full in Partition 3 §2):

| Discriminating Premise ID | Tested Hypothesis | Primary Probe Outcome (`PROBED`) | Architectural Consequence |
| :--- | :--- | :--- | :--- |
| **`P1` (Linear List & Pairwise Uniqueness Wall)** | Can `origin/main`'s linear `BodiesVerified` + `bodiesHaveUniqueIdentities := rfl` verify $N \ge 250$ bodies under `TrustedBoundary` (`maxRecDepth = 512`)? | **`PROBED: falsified`.** Hits `2,237.61 MiB` at $N = 100$ and fails hard (`maximum recursion depth has been reached`) at $N = 250$ (`94.47s`). | Disqualifies brownfield `no change` (`C+1`, `C+2`); requires $O(\log N)$ `BinChunkTree` + $O(N \log N)$ `ByteDecisionTree`. |
| **`P2` (Monolithic `BinChunkTree` Heap & Heartbeat Wall)** | Does replacing `List Body` lookup with `BinChunkTree` + `ByteDecisionTree` inside a *single* `Captured.lean` / `Proof.lean` suffice for $N \ge 250$–`500` at `<300 MiB`? | **`PROBED: falsified`.** Monolithic `BinChunkTree` reaches `512.37 MiB` at $N = 100$, `1,099.48 MiB` at $N = 250$, and **fails** (`deterministic timeout at whnf (200000)`, `2,019.10 MiB` RSS) at $N = 500$, with `75.83s` single-body rebuilds at $N = 250$. | Disqualifies unsharded tree lookup (`C+2`, `C+5`); requires multi-process `.olean` sharding. |
| **`P3` (Root `rfl` Re-Unfolding Cliff)** | Can sharded `Proof.lean` prove `wf rootTree = true` and `allIdx ... rootTree 0 = true` directly by `rfl` over imported `Proof.Shard_k.shardTree`s? | **`PROBED: falsified` (for `module` encapsulation & sub-`200 MiB` root scaling).** Root `rfl` fails in Lean 4 `module` mode unless `shardTree` is `@[expose]`d, and unfolds every body across all $K$ shards (`354.89 MiB` root RSS at $N = 50$). | Requires distributive `BinChunkTree.{toList,size,wf,allIdx}_branch` combinators (`171.82–197.46 MiB` root RSS, non-`@[expose]` `shardTree`). |
| **`P4` (`String.ofList` Quadratic `maxRecDepth` Wall on `zerocopy`)** | Does `BodyStaticAdmitted ... := rfl` succeed on verbatim `zerocopy/src/` captures without `set_option maxRecDepth`? | **`PROBED: falsified`.** `101`-byte `zerocopy` trait-impl identities fail at `maxRecDepth = 512` (`List.toByteArray.loop` $O(L^2)$ reduction) even at $N = 50$. | Requires `string_ofList_bytes_eq` symbolic UTF-8 rewrite (`O(L)` flatMap, `0` TCB edits). |
| **`P5` (`TargetRole::Capture` Multi-Module Closure)** | Does live `TrustedBoundary.lean` `"target-audit"` accept multiple `Capture` shard modules (`Captured.Shard_000..{K-1}`) with zero `Proof.*` `.olean`s mounted? | **`PROBED: confirmed`.** Passed on both `6`-shard cyclic call-graph (`1,197` replayed decls) and `5`-shard verbatim `zerocopy_100` (`1,325` replayed decls, `587` `subjectClosure` decls). | Eliminates any need to modify `TrustedBoundary.lean`'s role lattice (`C+3`). |
| **`P6` (`TrustedBoundary` Target `isModule` Support on `origin/main`)** | Does `origin/main` `TrustedBoundary.lean` already admit `isModule = true` on target `Capture`/`Proof` modules? | **`PROBED: falsified` on `origin/main` (`TrustedBoundary.lean:5615,5650`); `PROBED: confirmed` for Lean `v4.34.1` compiler & `v4.35.0` `leanexport` when `.olean.private` is mounted.** | Isolates target `module` activation cleanly as staged Decision D4 without blocking classic single-`.olean` sharding. |

## 2. Eliminated Architectural Alternatives

| Candidate Architecture | Summary of Mechanism | Elimination Basis (`Absolute Disqualification` vs. `Comparative Dominance`) |
| :--- | :--- | :--- |
| **A0 — Brownfield Incumbent (`origin/main` Monolithic Linear `Captured.lean` + `Proof.lean`)** | Single `Captured.lean` (`16`-element `bodies_chunk_k` list tree) + linear `BodiesVerified` + quadratic `bodiesHaveUniqueIdentities := rfl`. | **Absolutely disqualified (`C+2`, `C+6`, `P1`, `P4`):** Fails `maxRecDepth = 512` at $N = 250$ on short names (`94.5s`), reaches `2,237.61 MiB` RSS at $N = 100$, and fails at $N = 50$ (`1,532.78 MiB`) on verbatim `101`-byte `zerocopy` trait-impl identities. |
| **A1 — Unsharded Monolithic `BinChunkTree` + `ByteDecisionTree`** | Keep single `Captured.lean` and single `Proof.lean`, replacing linear list scans with `BinChunkTree` + `ByteDecisionTree`. | **Absolutely disqualified (`C+2`, `C+5`, `P2`):** Exceeds `<300 MiB` ceiling at $N = 50$ (`338.48 MiB`), hits `1,099.48 MiB` at $N = 250$, fails with `whnf` heartbeat timeout (`2,019.10 MiB`) at $N = 500$, and forces full-crate recompilation (`75.83s` at $N = 250$) on 1-body edits. |
| **A2 — Arbitrary Lexicographic or Hash-Modulus Chunking (`DefId % K` or Fixed-Slice Alphabetical)** | Slice sorted `Body` list into fixed chunks of 20 without Tarjan call-graph condensation. | **Absolutely disqualified (`C+4`) & comparatively dominated:** Splits mutually recursive SCCs ($u \leftrightarrow v$) across distinct shards (`Shard_a <-> Shard_b`), creating cyclic Lean `import` requirements for interprocedural proofs and scrambling topological callee-before-caller `DefId` stability. |
| **A3 — Per-Function Fine-Grained `.olean` Sharding ($1$ Body = $1$ `.olean`)** | Emit `Captured/Body_0000.lean` and `Proof/Body_0000.lean` for every MIR body ($4,545 \times 2 = 9,090$ `.olean` modules for `zerocopy`). | **Absolutely disqualified (`C+4` on cyclic SCCs) & comparatively dominated on build overhead:** Cannot compile mutually recursive cycles without merging SCCs anyway, and pays $9,090 \times \sim 0.10\text{s}$ process startup + `~150 MiB` base runtime load overhead (`>15 min` CPU overhead vs. `~230` coarsened 20-body shards). |
| **A4 — Binary `.olean` Post-Processing Stubbing (`thmInfo -> axiomInfo` Binary Rewriting)** | Mutate compiled `Proof/Shard_k.olean` binaries to strip proof terms into `axiomInfo` headers before downstream imports. | **Absolutely disqualified (`C-2`, `C+3`):** Corrupts Lean 4 `module` `.olean`/`.olean.private` invariants and introduces custom axioms rejected by `nanoda_bin` (`unpermitted_axiom_hard_error: true`) and `TrustedBoundary.lean`. Native Lean 4 `module` mode (`9.5 KiB` `.olean` vs. `334.5 KiB` `.olean.private`) + `#4181` Option-B $\lambda$-lifting achieve smaller headers with zero binary mutation. |
| **A5 — Mandatory Upfront TCB Migration (`Program.bodies : BinChunkTree Body` inside `trusted/lean/`)** | Rewrite `Trusted.MirAst.Program` (`Body.lean:164`) and `Trusted.MirSemantics` to store a tree natively in TCB Lean. | **Comparatively dominated for initial rollout (`C+1`; retained as optional Phase-2 cleanup in Decision D2):** `0`-TCB `BinChunkTree` + `getElem?_toList_eq_get?` + `string_ofList_bytes_eq` already achieves `<256 MiB` RSS and `0.36s` root `Proof` assembly at $N = 500$ while adding **`0` LOC to `trusted/lean/`** and breaking zero existing `MirCorrespondence` or `MirWp` theorems. |

---

# Partition 3 — Open Decisions, Outcome Contract, and Epistemic Calibration

## 1. Crisp Open Decisions for Human Sign-Off

All four items below are **policy values or staged subsystem-integration boundaries** whose resolution triggers **zero** structural invalidation of Partition 1's Tarjan-SCC + `BinChunkTree` architecture:

### Decision D1 — Default Coarsening Budget `(N_min, B_max, A_max)` & Static-DAG Build-System Mode
- **Question:** What activation threshold `N_min` and per-shard ceiling `(B_max, A_max)` should `anneal-rustc-capture` ship by default, and how should static-DAG build systems (Bazel, GN/Ninja, Nix) declare shard outputs before `rustc` runs?
- **Options & Trade-Offs:**
  1. **(Recommended) Dynamic-by-default `(N_min = 20, B_max = 20, A_max = 2_500)` for `cargo-anneal` / Buck2 + Checked-In Nominal `anneal-shards.json` (`--verify-shard-plan`) for Static-DAG Build Systems:** Targets with $\le 20$ bodies keep the zero-churn single-file `Captured.lean` layout; crates with $>20$ bodies shard automatically under `<260 MiB` peak RSS (`255.89 MiB` measured at $N = 500$ with $B_{\max} = 20$). Static-DAG build systems check in a deterministic `anneal-shards.json` manifest (regenerated via `cargo anneal shard-plan --write` whenever cross-shard call topology changes) and fail closed with an exact regeneration command on drift.
  2. **Aggressive Coarse Budget `(N_min = 32, B_max = 32, A_max = 4_000)`:** Fewer `.olean` files (`~38%` fewer shards), but pushes proof-shard peak RSS to `~285–315 MiB` on complex `PureLift` / `TreeBorrows` proofs, leaving narrow headroom under the `<300 MiB` ceiling.
  3. **Fixed Pre-Allocated Bucket Count `--num-shards K_fixed` Only for Static Build Systems:** Avoids checking in `anneal-shards.json`, but either wastes empty shard actions on small targets or overflows `<300 MiB` as a crate grows without bumping `K_fixed`.
- **Recommendation, Confidence & Default:** **Option 1** (**High confidence**). Default runtime flags: `--shard-min-bodies=20 --shard-max-bodies=20 --shard-max-ast-nodes=2500`.
- **Blast Radius:** CLI flags and build-rule wiring in `anneal-rustc-capture` / `cargo-anneal`; zero Lean proof or TCB impact.

### Decision D2 — Pure `0`-TCB `theory/` Bridge vs. Targeted `trusted/lean/` `stringBeq` Cleanup
- **Question:** Should Anneal keep `100%` of the crate-scale lookup and long-string infrastructure in `0`-TCB `anneal/theory/Anneal/SccSharding/` (`BinChunkTree`, `ByteDecisionTree`, `string_ofList_bytes_eq`), or also make a surgical 3-line cleanup in `Trusted/MirSemantics/Enum.lean:44`?
- **Options & Trade-Offs:**
  1. **(Recommended) Ship Pure `0`-TCB `Anneal.SccSharding` Immediately (`0` TCB LOC) + Optional Follow-Up PR Simplifying `Enum.lean:stringBeq`:** `Anneal.SccSharding.BinChunkTree` (`getElem?_toList_eq_get?` + `string_ofList_bytes_eq`) already solves all three walls (`N = 500` cyclic crates and `101`-byte `zerocopy` paths) with **`0` edits to `trusted/lean/`** and **`0` breakage** across `MirWp` and `MirCorrespondence`. A separate optional 3-line follow-up replacing `a.toByteArray.data.toList` with `List.beq a.data b.data` (`Char.val == Char.val`) in `Trusted/MirSemantics/Enum.lean:44` removes the `String.toByteArray` trap at the root so even naive `rfl` proofs on `100+`-byte names never need `string_ofList_bytes_eq`.
  2. **Keep `Enum.lean` Permanently Frozen:** Zero TCB churn ever; target proof generators simply emit `bodyStaticIntrinsic_of_ofList` / `checkBodyIdentityAt_of_ofList` (already 1-line wrappers).
  3. **Migrate `Program.bodies` from `List Body` to `BinChunkTree Body` Inside `Trusted.MirAst.Body`:** Eliminates `Captured.program.bodies` list concatenation (`56 KiB` at $N = 500$), but ripples across `19` `trusted/lean/` files and `16` `MirCorrespondence` files for negligible gain (`0.359s` root `Proof` already).
- **Recommendation, Confidence & Default:** **Option 1** (**High confidence**; ship `0`-TCB `Anneal.SccSharding` first, evaluate the 3-line `Char`-list `stringBeq` simplification separately, and reject Option 3).
- **Blast Radius:** Option 1 Phase 1 touches `0` TCB files; the optional `Enum.lean:44` follow-up touches 1 function (`3` LOC) in `Trusted/MirSemantics/Enum.lean`.

### Decision D3 — Cross-Shard Proof Coupling: Direct Acyclic `Proof.Shard` Imports vs. `#4181` `M3` $\lambda$-Lifted Contract Linking
- **Question:** When `u ∈ Shard_k` calls `v ∈ Shard_j` ($j < k$), should `Proof/Shard_k.lean` directly `import Proof.Shard_j` along the condensation DAG, or verify against `Spec`'s contract for `v` and link via `#4181` (`M3` $\lambda$-lifting + `Deriv.linkAxioms`)?
- **Options & Trade-Offs:**
  1. **(Recommended) Support Direct Acyclic `Spec`/`Proof.Shard_j` Imports in Stage 1, Promoting to `#4181` `M3` Contract Decoupling Once `#4181` Lands:** Direct imports along $G_{\text{SCC}}$ work today on `origin/main` with zero linker dependencies (and with Lean 4 `module` mode, `Proof.Shard_j.olean` is only `9.5 KiB`!). Once `#4181` merges, switching `Proof/Shard_k.lean` to assume `Spec`'s contract for `v` (checked by `#4181` Tier-4 Union Tarjan-SCC and stitched to `0` axioms by `Deriv.linkAxioms`) makes **both** `Captured.Shard_*` and `Proof.Shard_*` strictly `D = 1` parallel and prevents callee *proof-only* edits from invalidating caller proof shards!
  2. **Direct `Proof.Shard_k -> Proof.Shard_j` Imports Only:** Simpler pipeline, but sequentializes `Proof.Shard_*` compilation along the call-DAG critical path (`depth(G_SCC)`).
- **Recommendation, Confidence & Default:** **Option 1** (**High confidence**).
- **Blast Radius:** Confined to `Proof/Shard_k.lean` header generation in `cargo-anneal`; `capture_shards.json` (`callee_shards`) already records the exact condensation edges needed by both modes.

### Decision D4 — Activating Lean 4 `module` Mode (`#4139` Phase 2) on Sharded Target Modules
- **Question:** Should sharded target modules (`Captured.Shard_*`, `Proof.Shard_*`, `Captured`, `Proof`) emit classic single-`.olean` files initially or enable `module` (`isModule: true`) immediately by extending `TrustedBoundary.lean:5615,5650`?
- **Options & Trade-Offs:**
  1. **(Recommended) Two-Step Rollout — Ship Sharding in Classic `.olean` Mode Immediately, Flip `isModule: true` in `#4139` Phase 2:** Classic `.olean` sharding already passes live `TrustedBoundary.lean` `"target-export"` + `"target-audit"` (`<256 MiB` RSS at $N = 500$) and `v4.35.0` `5a`–`5c` NDJSON (`nanoda_bin` + `con-ron`) today with **zero** `TrustedBoundary.lean` edits. Once `#4139` Phase 2 admits `isModule = true` on target roles (and mounts `.olean.server`/`.olean.private` in `5b` `export_ndjson_proof` while keeping `5a` strictly proof-free), flipping `use_lean_module = true` shrinks `Proof.Shard_k.olean` public headers by **`35.2x`** (`334.5 KiB -> 9.5 KiB`), keeping Partition 1's compositional Lean surface (`public section` + `toList_branch`/`wf_branch`/`allIdx_branch`) unchanged.
  2. **Block Sharding Rollout on `#4139` Phase 2:** Delays crate-scale verification unnecessarily while coupling capture/runner changes to `TrustedBoundary.lean` audit changes in a single PR.
- **Recommendation, Confidence & Default:** **Option 1** (**High confidence**).
- **Blast Radius:** Zero rework—Partition 1's non-unfolding root `Proof.lean` is already verified clean under both classic `prelude` and `module` (`isModule: true`) modes (`benchmark_results.json`).

---

## 2. Full Outcome Contract Ledger `(C+, C-)` & Mandatory Pre-Delivery Audit

### 2.1 Sealed Outcome Contract `(C+, C-)`

- **Confirmed Positive Obligations (`C+`):**
  - **`C+1` (Zero Required `trusted/lean/` Growth & 3-Axiom Ceiling):** Achieve crate-scale body lookup, identity uniqueness, and shard aggregation without requiring `trusted/lean/` semantic additions, using strictly `{propext, Classical.choice, Quot.sound}` (`[propext]` achieved), `0` `sorryAx`, `0` `unsafe`/`partial`/`._unsafe_rec`, and `0` `set_option` overrides.
  - **`C+2` (`<300 MiB` Per-Process RSS & Multi-Hundred-Body Scaling):** Partition and verify `50`, `100`, `250`, and `500` interdependent MIR bodies below `<300 MiB` peak `ru_maxrss` per `lean` process (`236.68–255.89 MiB` achieved).
  - **`C+3` (`TrustedBoundary`, `ExecSeal`, Lean 4 `module`, and `5a`–`5c` NDJSON Compatibility):** Preserve `"target-audit"` `Proof`-free `subjectClosure` verification, `module`-mode non-`@[expose]` proof hiding, and `nanoda_bin` + `con-ron --verified` multi-kernel replay.
  - **`C+4` (Mutual-Recursion Cycle Soundness & Deterministic Naming/Ordering):** Condense arbitrary call-graph cycles via Tarjan SCCs with permutation-invariant canonical shard ordering and naming (`Shard_000 .. Shard_{K-1}`).
  - **`C+5` ($O(1)$-Shard Single-Function Incremental Rebuilds):** Restrict single-body implementation-edit recompilation to the owning shard plus thin $O(K)$ roots (`7.23–7.56s` constant rebuild time across $N = 50..500$).
  - **`C+6` (First-Customer Real `zerocopy` Coverage):** Exercise and pass end-to-end compilation and `TrustedBoundary` auditing on verbatim `google/zerocopy` (`src/`) multi-ten/hundred-body captures (`50` and `100` real bodies verified).
- **Confirmed Exclusions & Non-Goals (`C-`):**
  - **`C-1`:** No edits to live production repository files, branches, or CI during architectural specification and isolated prototyping.
  - **`C-2`:** No binary `.olean` post-processing mutation (`thmInfo -> axiomInfo`) or `unsafe` `.olean` parsing in Rust verdict code.
  - **`C-3`:** No splitting of mutually recursive SCCs across cyclic `.olean` imports and no custom `axiom` declarations in external kernel streams.
  - **`C-4`:** No `set_option maxRecDepth` / `maxHeartbeats` overrides to mask quadratic elaboration or string-conversion blowups.

### 2.2 Stage 2 Mandatory Pre-Delivery Read-Only Audit

| Audit Gate | Check Result | Verification Basis |
| :--- | :---: | :--- |
| **1. Direct Compliance with Sealed `C+` and `C-`** | **PASS** | `C+1`–`C+6` and `C-1`–`C-4` satisfied across `BinChunkTree.lean`, `InterprocCallCanary.lean`, `scc_sharder.py`, and `benchmark_results.json`. |
| **2. No Hardcoded Sealed Domain-Invariant Boundary** | **PASS** | Shard budgets `(N_min, B_max, A_max)` and `use_lean_module` are parameterized cleanly (`scc_sharder.py`) and surfaced as Decision D1 / D4. |
| **3. Clause-to-Machinery Attribution for Confirmed Cliffs** | **PASS** | `ByteDecisionTree` attributed to `C+2` (`P1`); `toList_branch`/`wf_branch`/`allIdx_branch` attributed to `C+2`/`C+3` (`P3`); `string_ofList_bytes_eq` attributed to `C+4`/`C+6` (`P4`). |
| **4. No Leaked Unfactored Policy Choice or Runtime Knob** | **PASS** | All four policy/staging choices (`D1`–`D4`) are isolated in Partition 3 §1 with explicit defaults and blast radii. |
| **5. No Hidden Unaccepted `superset-taxed boundary`** | **PASS** |Targets with $N \le N_{\text{min}}$ retain the single-file `Captured.lean` fast path with zero sharding manifest tax. |
| **6. No `PROBED: falsified` Claim Treated as Viable** | **PASS** | Incumbent linear (`P1`), monolithic `BinChunkTree` (`P2`), root `rfl` unfolding (`P3`), raw `String.ofList` `rfl` (`P4`), and unpatched `origin/main` target `isModule` (`P6`) are explicitly recorded as falsified/gated. |

---

## 3. Epistemic Calibration & Verification Inventory

- **Stopping Status & Deliverability:** Core structural model converged (`local convergence` after completion-boundary conceptual simplification review accepting zero further conceptual-model changes); emitted as a **Standalone Pre-Implementation RFC** with zero tracked-repo edits so human policy choices `D1`–`D4` remain explicitly human-owned.
- **Primary Evidence Summary:**
  - `[kernel-checked proof]`: `Anneal.SccSharding.BinChunkTree` (`getElem?_toList_eq_get?`, `toList_branch`, `size_branch`, `wf_branch`, `allIdx_branch`, `allIdx_leaf`, `bodiesHaveUniqueIdentities_of_decisionTree`, `string_ofList_bytes_eq`, `checkBodyIdentityAt_of_ofList`, `bodyStaticIntrinsic_of_ofList`, `programVerified_of_shardedTree`), `InterprocCallModel`, and `InterprocCallCanary` — compiled with `-Ddebug.skipKernelTC=false -DwarningAsError=true`, `0` `sorry`, `0` `._unsafe_rec`, axioms `["propext"]`.
  - `[real measurement]`: Full matrix (`N = 50, 100, 250, 500`), verbatim `zerocopy/src/` (`50` and `100` bodies), incremental 1-body rebuilds, genuine `TrustedBoundary.olean` `"target-export"` + `"target-audit"` (`0` `Proof` `.olean`s in `"target-audit"`), Lean 4 `module` 3-part `.olean*` sizes, and Lean `v4.35.0` `leanexport` + `nanoda_bin` + `con-ron --verified`.
- **What Was *Not* Exercised (Explicit Scope Boundaries):**
  1. Verbatim `zerocopy` captures exercised the `100` bodies currently admitted by `origin/main` MIR Profile v1 (`TryFromBytes::only_derive_is_allowed_to_implement_this_trait` and `PointerMetadata::{from,to}_elem_count`); capturing all `4,545` `zerocopy` bodies end-to-end additionally depends on landing generic/polymorphic and raw-pointer MIR capture beyond Profile v1, though the $N = 500$ cyclic call-graph benchmark (`26` shards, `255.89 MiB` max shard RSS, `0.359s` root `Proof`) directly validates the shard-count and root-aggregation scaling regime (`4,545` bodies $\approx 228$ shards, projected root `Proof` `<3s` and `<260 MiB`/shard).
  2. Multi-kernel NDJSON replay exercised `nanoda_bin` and `con-ron --verified` on Lean `v4.35.0`; paranoid-quorum `con-leche` and `lean4lean --import` share the identical zero-custom-axiom `NDJSON 3.1.0` stream (`#4181`).
  3. Peer workflow note: Single-agent conceptual minimization and clarity reviews were executed directly in-context over primary compiler/kernel probes; multi-reviewer blind-holdout isolation was not invoked because all discriminating architectural premises (`P1`–`P6`) were resolved directly by deterministic Lean kernel and `TrustedBoundary` execution.

---

*Authored by an AI agent acting on joshlf's behalf.*
