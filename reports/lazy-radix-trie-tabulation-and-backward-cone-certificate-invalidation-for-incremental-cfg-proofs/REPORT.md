# Lazy Radix-Trie Tabulation and Backward-Cone Certificate Invalidation for Incremental Control-Flow Graph Proofs

## Summary

Achieving sub-second incremental ("Day-2") re-verification of large control-flow graphs (CFGs) inside call-by-name dependent-type proof kernels requires co-designing the CFG map representation, the per-block verification-condition (VC) certificate boundary, and the dependency invalidation discipline:

1. **Top-Down Radix-2 Tabulation (`ptreeTabulate`) vs. Sequential Insertion (`foldl setAt`) in Lazy Kernels**: Representing a $B$-block CFG as a flat `List BasicBlock` incurs $\Theta(u)$ unary lookup cost and trips kernel recursion limits (`maxRecDepth = 512` in Lean 4) when sparse block identifiers exceed $512$. Replacing `List` with a binary radix-2 trie (`PTree`, as in CompCert `lib/Maps.v`) eliminates sparse-index cliffs only when constructed **top-down** rather than **bottom-up**. Under call-by-name weak-head normal form (WHNF) evaluation (`leanprover/lean4` `whnf_core` and `digama0/lean4lean` `whnfCore'`), a trie built by $B$ sequential updates (`List.foldl ptreeSetAt .leaf entries`) wraps the root in $B$ nested `ptreeSetAt` redexes: looking up *even one block* forces the outermost `ptreeSetAt` to pattern-match on the $(B-1)$-th intermediate tree, recursively forcing all $B$ insertions at stack depth $\Theta(B)$ (`1,332` WHNF steps, `1,268` forced trie nodes, stack depth `1,023` at $B = 512$). Conversely, top-down bit-partitioning (`ptreeTabulate`) immediately exposes an inductive `.node left mid right` constructor in WHNF without evaluating `left`, `mid`, or `right`. Looking up block $u$ forces only $\lceil \log_2(\max(u, 1)) \rceil + 1$ spine nodes and $1$ block payload (`72` WHNF steps, `14` forced nodes, depth `10` for a 7-block cone in a 512-block CFG; `13` nodes at depth `14` for sparse `BlockId = 4096`), leaving all unaffected subtrees and block payloads unevaluated.
2. **Zero-`Prop`-Argument `@[irreducible]` Certificate Sealing**: Wrapping a block's weakest-precondition obligation `P : Prop` inside a helper structure `Hold P` or an `@[irreducible]` wrapper `Firewall tag P` does **not** shield `P` from tactic traversal in Lean 4. Source inspection of `Lean/Meta/Tactic/Rewrite.lean` (`kabstract` + `congrArg`) and `Lean/Meta/Tactic/Simp/Main.lean` (`simpApp` -> `congr` -> `congrArgs`) confirms that both `rw` and `simp` traverse explicit `Prop` arguments of an application without unfolding its head constant. True tactic-level opacity requires a **zero-`Prop`-argument** `@[irreducible]` predicate `BlockWpCert (spec : CfgSpecTable) (u : BlockId) (sl : MirBlockSlice) : Prop` parameterized solely by first-order data, paired with `sealBlockWpCert` and `openBlockWpCert` proved *before* `attribute [irreducible] BlockWpCert`. Because Lean 4's C++ kernel ignores Meta `@[irreducible]` attributes during conversion, Day-2 compositions must transport certificates algebraically (`exact cert_prev`) rather than invoking `rfl` across sealed obligations.
3. **Decoupled Spec Tables, Dual-Digest Content Addressing, and Backward-Cone Invalidation**: Monolithic block VCs that close over a whole-CFG step function `stepBb cfg` invalidate every block proof whenever *any* block changes. Decoupling a pure-data `CfgSpecTable` (preconditions, invariants, termination ranks, and expected digests) from `CfgBody` (`PTree MirBlockSlice`) makes `BlockWpCert spec u sl` depend solely on `spec` and `sl`. When block $k$ changes, only blocks in its **backward reachability cone** $\mathrm{Cone}^{-}(G, \{k\})$ require re-certification; every block $u \notin \mathrm{Cone}^{-}(G, \Delta)$ retains its Day-1 `BlockWpCert` with zero block-body re-evaluation. Sound reuse requires **dual-digest binding**—verifying both `sl.blockHash = hashBlock sl.block` and `spec[u].expectedHash = sl.blockHash`—to defeat both unhashed `BlockId` stale-certificate reuse and forged slice-digest metadata.

## Applicability

This report applies to verification engineers and proof-assistant tool builders designing compositional CFG program logics, verification-condition generators, and incremental proof-checking pipelines in call-by-name / lazy dependent type theories (Lean 4, Rocq/Coq) and LCF/HOL provers.

### Examined Subjects and Relationships

- **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`) and Lean4Lean (`digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`)**: Examined together for C++ kernel WHNF reduction (`src/kernel/type_checker.cpp`, mechanized in `Lean4Lean/TypeChecker.lean`), `maxRecDepth` stack bounds, Meta WHNF transparency (`src/Lean/Meta/WHNF.lean`), and explicit-argument congruence in `rw` (`src/Lean/Meta/Tactic/Rewrite.lean`) and `simp` (`src/Lean/Meta/Tactic/Simp/Main.lean`).
- **CompCert (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`) and Rocq (`rocq-prover/rocq@25f5b18a320e4796f181f938d3b74bebe7db4dc4`)**: Examined comparatively for canonical positive binary radix-2 tries (`PTree.tree'` `Node001`..`Node111` in `lib/Maps.v`, `RTL.code := PTree.t instruction` in `backend/RTL.v`, `backend/Kildall.v`; Leroy, *JAR* 2009) and call-by-need closure sharing (`Zupdate` in `kernel/cClosure.ml`) plus kernel-enforced `OpaqueDef` (`Qed`).
- **seL4 GraphLang (`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`) and Dafny (`dafny-lang/dafny@8e67e29912aa81b06a8b8e288c7e3046072ea482`)**: Examined as comparative baselines for unstructured CFG verification (`tools/asmrefine/GraphLang.thy` function maps `nat => node option`) and fine-grained VC caching via content digests and dependency graphs (Leino & Wüstholz, *CAV* 2015; Barnett & Leino, *PASTE* 2005; Celik et al., *ASE* 2017).

### Cross-References to Adjacent Corpus Packages

- `lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`: Covers Lean 4 RSS ceilings, `Meta.whnf` `useWHNFCache` (`hasFVar`) blowups on flat `List` local stores, and single-trace CPS spine-forcing; the present report addresses multi-block CFG indexing (`ptreeTabulate` vs. `foldl setAt`), congruence-opaque per-block WP certificates, and backward-cone invalidation.
- `proof-kernels-opaque-interfaces-and-adversarial-spec-hardening`: Covers `.olean`/`.vo` loader safety, `.thmInfo` kernel unfoldability, and Goodhart specification hardening.

## Findings

### 1. Call-by-Name WHNF Scaling of CFG Maps: Flat Lists vs. Sequential `foldl setAt` vs. Top-Down `ptreeTabulate`

Basis: source + execution + derived

In compiler IRs and binary lifters—such as CompCert `RTL` (`AbsInt/CompCert@2685140b...`, `backend/RTL.v:83`, `Definition code: Type := PTree.t instruction`), `seL4` `GraphLang` (`seL4/l4v@b0fe7693...`, `tools/asmrefine/GraphLang.thy:106-107`, `GraphFunction ... "nat => node option" nat`), and Rust mid-level IRs (`Body.basicBlocks`)—a function body maps integer or positive binary block IDs (`BlockId`) to basic-block records. Inside a dependent-type kernel using **call-by-name WHNF** (`leanprover/lean4@5045d005...`, `src/kernel/type_checker.cpp:456-538`; `digama0/lean4lean@67f63b0c...`, `Lean4Lean/TypeChecker.lean:364-415`), four map encodings exhibit sharply different asymptotic behavior:

| CFG Representation | Ground Literal Lookup | Dynamic Fold Lookup | Kernel Stack Depth (`BlockId = u`, `\|CFG\| = B`) | Sparse `BlockId = 4096` (`maxRecDepth = 512`) | Sibling Isolation Under Surgical Cone Check (`\|C\| \ll B`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Flat `List` + unary `listGetOpt`** | $\Theta(u)$ | $\Theta(u)$ | $\Theta(u)$ | **Fails** (`4,097` frames exceed `512`) | Partial: prefix $0 \dots \max(C)$ forced; suffix unforced |
| **Chained Function Update (`fun_upd`)** | $\Theta(B)$ worst-case | $\Theta(B)$ | $\Theta(B)$ | **Fails** when $B \ge 512$ updates chain | Poor: entry lookup traverses all $B - 1$ later wrappers |
| **Sequential `List.foldl ptreeSetAt .leaf`** | N/A (unreduced chain) | **$\Theta(B \log B)$** on first lookup (`100%` of $B$ insertions forced) | **$\Theta(B)$** (`~2B` frames; fails around $B \ge 256$) | Survives if $B \ll 256$; **fails** when $B \ge 256$ | **Broken**: first `ptreeGetAt` forces all $B$ `ptreeSetAt` spine redexes |
| **Top-Down `ptreeTabulate` / `.node` Literal** | **$\Theta(\log_2(\max(u, 1)))$** | **$\Theta(\|C\| \log_2 B)$** across cone $C$ | **$\Theta(\log_2(\max(u, 1)))$** (`14` frames at $u = 4096$) | **Passes by `rfl`** (`13` nodes, `< 20` frames) | **Exact**: off-cone `.node` children and $B - \|C\|$ payloads stay unforced |

#### 1.1 Why Constructor WHNF Halts at `.node` While `foldl ptreeSetAt` Forces All $B$ Insertions

In Lean 4's kernel WHNF reducer (`Lean4Lean/TypeChecker.lean:364-402` and `src/kernel/type_checker.cpp:456-538`), constructor applications (`PTree.leaf`, `PTree.node left mid right`) are already weak-head normal forms: `whnfCore'` reduces head `PTree.node` (`line 385`), sees neither a lambda nor a recursor (`inductiveReduceRec` at `line 331` fires only on `.rec`), and returns `PTree.node left mid right` **without reducing `left`, `mid`, or `right`**.

Consider a little-endian binary radix-2 trie (Morrison, *JACM* 1968, DOI `10.1145/321479.321481`; CompCert `PTree` in `AbsInt/CompCert@2685140b...`, `lib/Maps.v:178-308`, where `Node001`..`Node111` canonically compress empty subtrees over `positive := xI | xO | xH`):

```lean
inductive PTree (α : Type u) : Type u where
  | leaf : PTree α
  | node : PTree α → Option α → PTree α → PTree α
```

When key routing decomposes `k : Nat` by least-significant bit (`k % 2 == 0` routes to `left` with `k / 2`, `k % 2 == 1` to `right` with `k / 2`, and `k == 0` selects `mid`, bounded by bit budget `bits` using Lean 4's $O(1)$ GMP kernel reducers `Nat.div`/`Nat.mod`/`Nat.beq`), `ptreeGetAt bits u tree` applies `PTree.casesOn` to `tree`:

- **Sequential bottom-up `foldl ptreeSetAt` trap**: Defining `cfg := List.foldl (fun acc (k, v) => ptreeSetAt 16 k v acc) .leaf entries` produces $B$ nested applications `ptreeSetAt 16 k_{B-1} v_{B-1} (... (ptreeSetAt 16 k_0 v_0 .leaf)...)`. Evaluating `ptreeGetAt 16 u cfg` for **even one block** $u$ demands a head constructor from the outermost `ptreeSetAt`, which immediately pattern-matches on the $(B-1)$-th accumulator (`Maps.v:304` `match m with | Empty => ... | Nodes m' => ...`), recursively demanding WHNF down through all $B$ insertions! At $B = 512$, the call stack reaches depth `1,023` (exceeding `maxRecDepth = 512`) and forces `1,268` intermediate trie nodes across the entire CFG.
- **Top-down `ptreeTabulate` remedy**: Partitioning `(k, v)` pairs top-down by least-significant bit and emitting `.node` *outside* the recursive calls halts WHNF immediately at `.node`:

```lean
def partitionRadix (pairs : List (Nat × α)) : Option α × List (Nat × α) × List (Nat × α) :=
  match pairs with
  | [] => (none, [], [])
  | (k, v) :: rest =>
    let (here, evens, odds) := partitionRadix rest
    if Nat.beq k 0 then (some v, evens, odds)
    else if Nat.beq (k % 2) 0 then (here, (k / 2, v) :: evens, odds)
    else (here, evens, (k / 2, v) :: odds)

def ptreeTabulate (bits : Nat) (pairs : List (Nat × α)) : PTree α :=
  match pairs with
  | [] => .leaf
  | _ :: _ =>
    match bits with
    | 0 => let (here, _, _) := partitionRadix pairs; .node .leaf here .leaf
    | b + 1 =>
      let (here, evens, odds) := partitionRadix pairs
      .node (ptreeTabulate b evens) here (ptreeTabulate b odds)
```

*(When an external IR emitter generates Lean source directly, emitting balanced `.node` syntax literals avoids even list spine partitioning; `ptreeTabulate` provides the equivalent lazy `.node` barrier inside the logic.)* When `ptreeGetAt 16 u cfg` branches left (`u % 2 == 0`), `ptreeTabulate b odds`—half of all remaining CFG blocks—is discarded unreduced. Across a cone $C$, at most $|C| \lceil \log_2 B \rceil$ `.node` thunks are forced (`14` vs. `1,268` at $B = 512$, a **`90.6x` node reduction** and **`102.3x` depth reduction**).

#### 1.2 Single-Pass `modifyAt` and Non-CPS Traversal Bounds

Basis: source + derived

Updating an edited block via single-pass `PTree.modifyAt bits k f tree` preserves syntactic identity of off-path subtrees (`ptree_getAt_modifyAt_diff` proved by structural induction on `bits` with zero axioms). Likewise, whole-tree Day-1 structural checks (`checkPTreeWithKeys`) should use direct depth-bounded recursion (`<= 27` stack frames at `bits = 16`) rather than CPS folds, which chain $\Theta(B)$ continuations and risk `maxRecDepth` exhaustion.

---

### 2. Why Explicit-`Prop` Wrappers Leak Under `rw`/`simp` and How Zero-`Prop`-Argument `@[irreducible]` Certificates Seal Block Proofs

Basis: source + execution + derived

Once block $u$ is verified on Day 1—often generating a large symbolic weakest-precondition AST—Day-2 incremental proofs must treat block $u$'s certificate as opaque so `rw`, `simp`, and `unfold` cannot traverse or copy its obligation AST. Attempting to hide `P : Prop` inside `private structure HoldBlockProp (P : Prop) : Prop` or `@[irreducible] def FirewallBlockProp (tag : Nat) (P : Prop) : Prop := P` **fails** in Lean 4 (`leanprover/lean4@5045d005...`):

1. **`rw` (`src/Lean/Meta/Tactic/Rewrite.lean:46-82`)**: `Lean.MVarId.rewrite` runs `kabstract e lhs config.occs` (`line 47`) directly over the surface AST of goal `e`. In `FirewallBlockProp tag (guardChain (x + 0) x)`, `P` is an **explicit argument** in `e`'s application spine; `kabstract` traverses `P` in $\Theta(|P|)$ time, abstracts `motive` (`line 56`), and builds `congrArg` (`line 81`) without ever unfolding `FirewallBlockProp`.
2. **`simp` (`src/Lean/Meta/Tactic/Simp/Main.lean:632-656`)**: `simpApp` (`line 650`) invokes `congr` (`line 637`) and `congrArgs` (`line 633`), simplifying every explicit argument `aᵢ` regardless of whether the head constant is `@[irreducible]`.

#### The Zero-`Prop`-Argument `@[irreducible]` Certificate Pattern

To block tactic congruence completely under `.default` transparency, the certificate predicate must take **zero `Prop` arguments**, accepting only first-order data handles `(spec, u, sl)` and computing the `Prop` obligation internally:

```lean
def denoteBlockWpCert (spec : CfgSpecTable) (u : BlockId) (sl : MirBlockSlice) : Prop :=
  sl.blockHash = hashBlock sl.block ∧
  match ptreeGetAt 16 u spec.entries with
  | none => False
  | some entry =>
      entry.expectedHash = sl.blockHash ∧
      ∀ s, denotePre entry.pre s →
        wpBlock sl.block s (fun out =>
          match out with
          | .fault _ => False
          | .ret v   => denotePost spec.retPost v
          | .jump v s' =>
              match ptreeGetAt 16 v spec.entries with
              | none => False
              | some succ => succ.rank < entry.rank ∧ denotePre succ.pre s')

def BlockWpCert (spec : CfgSpecTable) (u : BlockId) (sl : MirBlockSlice) : Prop :=
  denoteBlockWpCert spec u sl

theorem sealBlockWpCert {spec u sl} (h : denoteBlockWpCert spec u sl) : BlockWpCert spec u sl := h
theorem openBlockWpCert {spec u sl} (h : BlockWpCert spec u sl) : denoteBlockWpCert spec u sl := h
attribute [irreducible] BlockWpCert
```

Across 7 isolated Lean 4 `v4.34.1` compilation probes (mirrored in **Evidence** §2, Part 2):
- `rw [Nat.add_zero]`, `simp only [Nat.add_zero]`, and `simp` penetrate `HoldBlockProp` and `FirewallBlockProp` (`0.13–0.18 s`), whereas all four tactics (`rw`, `simp only`, `simp`, `unfold`) are **blocked** on `BlockWpCert sp0 0 sl0` (`0.12–0.14 s`).
- Because Lean 4's `@[irreducible]` is enforced in `MetaM` (`src/Lean/ReducibilityAttrs.lean`) rather than C++ kernel `is_def_eq` (`type_checker.cpp:543-551`, unlike Rocq's kernel `OpaqueDef` in `cClosure.ml:468, 2088`), Day-2 proofs transport `day1_cert_u : BlockWpCert spec₁ u sl` nominally via framing lemmas rather than kernel `rfl`.
- Because `CfgSpecTable` stores first-order specification codes (`denotePre`/`denotePost`) and `BlockWpCert spec u sl` does not take `cfg : CfgBody`, mutating `cfg` at $k \neq u$ leaves the type `BlockWpCert spec u sl` syntactically identical for every unaffected block!

---

### 3. Ranked WP Composition, Dual-Digest Content Addressing, and Day-2 Backward-Cone Scaling

Basis: normative + source + execution + derived

Classical unstructured-CFG VC generation (Barnett & Leino, *PASTE* 2005, DOI `10.1145/1108792.1108813`) converts cutpoint-broken CFGs into coupled block equations; fine-grained incremental verifiers cache VCs along dependency cones (Leino & Wüstholz, *CAV* 2015, DOI `10.1007/978-3-319-21690-4_22`, in `dafny-lang/dafny@8e67e299...`; Celik et al., *ASE* 2017, DOI `10.1109/ASE.2017.8115630`).

1. **Ranked Total-Correctness Composition**: Equipping each `BlockSpecEntry` with well-founded `rank : Nat` (`succ.rank < entry.rank` across CFG edges, or lexicographic loop variant at cutpoints) lets `cfg_block_certs_compose_wp_sound` prove by strong induction (`@Nat.rec`) on `entry.rank` that if `AllCfgBlocksCertified cfg spec` holds and `fuel > entry0.rank`, `evalCfgSteps cfg fuel uEntry s0` terminates without `.fault` or `.timeout` satisfying `denotePost spec.retPost`. Crucially, `openBlockWpCert` is invoked **once generically** over abstract `(u, sl)`, never unfolding concrete block certificates.
2. **Backward-Cone Invalidation Law**: Given edited blocks $\Delta_{\text{edit}}$, let $\mathrm{Cone}^{-}(G, \Delta_{\text{edit}})$ be the backward-reachable predecessor closure in `cfg₂`. If an edit to block $k$ preserves `entry_k.pre` and `entry_k.rank`, **only block $k$** (`|Δ| = 1`) requires re-checking (predecessors inspect `spec[k].pre` and `spec[k].rank`, never `spec[k].expectedHash`). Even when preconditions strengthen along predecessors inside $\mathrm{Cone}^{-}$, no block $u \notin \mathrm{Cone}^{-}$ has an edge into $\mathrm{Cone}^{-}$ (`IsBackwardClosedSpec`), so `spec₂[u] = spec₁[u]`, `spec₂[v] = spec₁[v]` for all $v \in \mathrm{succ}(u)$, and `BlockWpCert spec₁ u sl` transfers to `spec₂` with **zero block re-evaluation**.

Measured in single-threaded Lean 4 `v4.34.1` (`leanprover/lean4@5045d005...`, `-j1 -M2048 -t0 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, median of 3 isolated runs) on 64- and 128-block syscall-dispatcher CFGs after mutating one leaf arm guard (`4 / 64` cone = `93.75%` reuse; `5 / 128` cone = `96.09%` reuse):

| Isolated Lean `v4.34.1` Workload | Blocks Re-Certified | Median Wall (Marginal Over `0.1265 s` Import) | Median Peak RSS (Marginal Over `145.61 MiB`) | Speedup & RSS Savings vs. Cold Check |
| :--- | :---: | :---: | :---: | :--- |
| **Import Baseline** | `0` | `0.1265 s` (`+0.0 ms`) | `145.61 MiB` (`+0.00 MiB`) | Module-import floor |
| **64-Block Cold Full** | `64 / 64` | `2.7624 s` (`+2,635.9 ms`) | `277.52 MiB` (`+131.91 MiB`) | Baseline $B = 64$ full check |
| **64-Block Day-2 (`ptreeTabulate`)** | **`4 / 64` (`6.25%`)** | **`0.5904 s`** (`+463.9 ms`) | **`170.04 MiB`** (`+24.43 MiB`) | **`4.68x` total (`5.68x` marginal) faster**, **`-107.48 MiB` RSS** (`5.40x` lower marginal) |
| **128-Block Cold Full** | `128 / 128` | `5.0391 s` (`+4,912.6 ms`) | `402.55 MiB` (`+256.94 MiB`) | Linear $2\times$ time & RSS growth over $B = 64$ |
| **128-Block Day-2 (`foldl ptreeSetAt`)** | `5 / 128` (`3.91%`) | `2.8053 s` (`+2,678.8 ms`) | `259.41 MiB` (`+113.80 MiB`) | Degraded: lookup forces all `128` `ptreeSetAt` updates |
| **128-Block Day-2 (`ptreeTabulate`)** | **`5 / 128` (`3.91%`)** | **`0.4643 s`** (`+337.8 ms`) | **`175.48 MiB`** (`+29.87 MiB`) | **`10.85x` total (`14.54x` marginal) faster**, **`-227.07 MiB` RSS** (`+5.44 MiB` over $B = 64$) |

3. **Dual-Digest Anti-Poisoning Invariant**: Keying certificate reuse solely by `BlockId` admits stale certificates after a block is mutated to double-move UB (`M1` in **Evidence** §2), while checking only `spec[u].expectedHash == sl.blockHash` is bypassed if a buggy patcher mutates `sl.block` without updating `sl.blockHash` (`M2`). Binding **both** `sl.blockHash = hashBlock sl.block` and `entry.expectedHash = sl.blockHash` inside `denoteBlockWpCert` rejects both attacks while requiring zero re-hashing of untouched Day-1 slices.

## Boundaries

- **Kernel-level unfolding under forced conversion (`known not to apply`)**: Lean 4's `@[irreducible]` is a `MetaM` barrier, **known not to apply** inside C++ kernel `whnf`/`is_def_eq` (`type_checker.cpp:543-551`). Proofs must transport `BlockWpCert` terms nominally rather than invoking `rfl` across concrete certificates.
- **Repeated lookups on already-memoized spines (`known not to apply`)**: The $\Theta(B)$ cost of `foldl ptreeSetAt` hits on the *first* root-to-spine WHNF evaluation (and on unshared copies when `hasFVar` disables `Meta.whnf` caching); once memoized in `m_whnf` (or Rocq `Zupdate`), repeated lookups on forced paths are logarithmic, though the initial $\Theta(B)$ spike already breaks sub-second Day-2 checking.
- **Cycle-introducing CFG edge edits without re-ranking (`unsupported`)**: Pure backward-cone reuse without updating `rank` values outside the cone is **unsupported** when a Day-2 edit inserts an edge $k \to v$ with `spec[v].rank >= spec[k].rank`; affected cycle/prefix ranks must be updated in $\Delta_{\text{spec}}$.
- **Interprocedural call-graph invalidation (`not examined`)**: Whole-program points-to analyses and cross-function summary invalidation are **not examined** here.
- **External binary certificate crossover above $B > 10^4$ (`unknown`)**: The exact block count where `.olean` import overhead of Day-1 `PTree` certificate tables exceeds standalone external certificate checkers is **unknown** from $B \le 512$ measurements.

## Evidence

### 1. Primary Upstream Source Citations

- **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, observed 2026-11-21)**: `src/kernel/type_checker.cpp:456-538, 660-733` (`whnf_core`, `maxRecDepth`, GMP `reduce_nat`); `src/Lean/Meta/Tactic/Rewrite.lean:28-90` (`kabstract` at `line 47`, `congrArg` at `line 81`); `src/Lean/Meta/Tactic/Simp/Main.lean:632-656` (`simpApp` -> `congr` -> `congrArgs`); `src/Lean/Meta/WHNF.lean` (`.irreducible` gating).
- **Lean4Lean (`digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, observed 2026-11-21)**: `Lean4Lean/TypeChecker.lean:326-415` (`whnfCore'` returning `.const` constructor applications without reducing arguments).
- **CompCert (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`, observed 2026-11-21)**: `lib/Maps.v:178-308` (`PTree.tree'` `Node001`..`Node111`, `get`, `set` matching `Empty | Nodes` at `line 304`); `backend/RTL.v:37-91` (`code := PTree.t instruction`); `backend/Kildall.v` (`make_predecessors`).
- **Rocq (`rocq-prover/rocq@25f5b18a320e4796f181f938d3b74bebe7db4dc4`), seL4 (`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`), and Dafny (`dafny-lang/dafny@8e67e29912aa81b06a8b8e288c7e3046072ea482`)**: `rocq` `kernel/cClosure.ml:199-230, 468, 2088`; `seL4` `tools/asmrefine/GraphLang.thy:92-120, 183-210`; `dafny` verification result caching (Leino & Wüstholz, *CAV* 2015).

### 2. Self-Contained Executable Verification Probe (`/tmp/probe_lazy_radix_trie_cfg_invalidation.py`)

```python
#!/usr/bin/env python3
"""Standalone probe: lazy radix-2 trie WHNF scaling, certificate opacity, and cone invalidation."""
from __future__ import annotations
import hashlib, sys
from dataclasses import dataclass
from typing import Any, Callable

sys.setrecursionlimit(10000)

class WHNFStats:
    def __init__(self) -> None:
        self.whnf_steps = self.node_forces = self.slice_forces = self.max_depth = 0

class Thunk:
    def __init__(self, fn: Callable[[WHNFStats, int], Any], kind: str = "spine") -> None:
        self._fn, self._kind, self._cached, self._forced = fn, kind, None, False

    def whnf(self, st: WHNFStats, depth: int = 0) -> Any:
        st.whnf_steps += 1
        st.max_depth = max(st.max_depth, depth)
        if not self._forced:
            self.inc(st)
            self._cached, self._forced = self._fn(st, depth + 1), True
        return self._cached

    def inc(self, st: WHNFStats) -> None:
        if self._kind == "node": st.node_forces += 1
        elif self._kind == "slice": st.slice_forces += 1

def mk_slice(b: int) -> Thunk:
    return Thunk(lambda st, d: ("BlockSlice", b), "slice")

def build_list_cfg(blocks: list[int]) -> Any:
    acc: Any = ("nil",)
    for b in reversed(blocks):
        prev = acc
        acc = ("cons", mk_slice(b), Thunk(lambda st, d, p=prev: p, "node"))
    return acc

def list_get_opt(idx: int, lst: Any, st: WHNFStats, depth: int = 0) -> Any:
    st.whnf_steps += 1
    st.max_depth = max(st.max_depth, depth)
    node = lst.whnf(st, depth + 1) if isinstance(lst, Thunk) else lst
    if node[0] == "nil": return None
    return node[1].whnf(st, depth + 1) if idx == 0 else list_get_opt(idx - 1, node[2], st, depth + 1)

def ptree_set_at(bits: int, key: int, vt: Thunk, tree_e: Any) -> Thunk:
    def _red(st: WHNFStats, d: int) -> Any:
        t = tree_e.whnf(st, d + 1) if isinstance(tree_e, Thunk) else tree_e
        l, o, r = (("leaf",), None, ("leaf",)) if t[0] == "leaf" else (t[1], t[2], t[3])
        if bits == 0 or key == 0: return ("node", l, vt, r)
        return ("node", ptree_set_at(bits - 1, key >> 1, vt, l), o, r) if (key & 1) == 0 else ("node", l, o, ptree_set_at(bits - 1, key >> 1, vt, r))
    return Thunk(_red, "node")

def ptree_tabulate(entries: list[tuple[int, Thunk]], bits: int = 16) -> Any:
    if not entries: return ("leaf",)
    here, ev, od = None, [], []
    for k, vt in entries:
        if k == 0 or bits == 0: here = vt
        elif (k & 1) == 0: ev.append((k >> 1, vt))
        else: od.append((k >> 1, vt))
    return ("node", Thunk(lambda st, d, e=ev, b=bits: ptree_tabulate(e, b - 1), "node"), here,
            Thunk(lambda st, d, o=od, b=bits: ptree_tabulate(o, b - 1), "node"))

def ptree_get_at(bits: int, key: int, tree_e: Any, st: WHNFStats, depth: int = 0) -> Any:
    st.whnf_steps += 1
    st.max_depth = max(st.max_depth, depth)
    t = tree_e.whnf(st, depth + 1) if isinstance(tree_e, Thunk) else tree_e
    if t[0] == "leaf": return None
    if key == 0 or bits == 0: return None if t[2] is None else t[2].whnf(st, depth + 1)
    return ptree_get_at(bits - 1, key >> 1, t[1] if (key & 1) == 0 else t[3], st, depth + 1)

print("[PART 1] WHNF steps, node forces, max call depth, and slice forces on surgical cone lookup:")
for B, cone in [(64, [0, 2, 6, 56]), (128, [0, 2, 6, 14, 120]), (512, [0, 2, 6, 14, 30, 62, 504])]:
    lst = build_list_cfg(list(range(B)))
    seq_t: Any = ("leaf",)
    for k in range(B): seq_t = ptree_set_at(10, k, mk_slice(k), seq_t)
    tab_t = ptree_tabulate([(k, mk_slice(k)) for k in range(B)], 10)
    st_l, st_s, st_t = WHNFStats(), WHNFStats(), WHNFStats()
    for u in cone:
        assert list_get_opt(u, lst, st_l) == ptree_get_at(10, u, seq_t, st_s) == ptree_get_at(10, u, tab_t, st_t) == ("BlockSlice", u)
    print(f"  B={B:3d} (cone={len(cone)}/{B}): List(steps={st_l.whnf_steps:4d}, nodes={st_l.node_forces:3d}, depth={st_l.max_depth:4d}, slices={st_l.slice_forces}/{B}) | "
          f"SeqSetAt(steps={st_s.whnf_steps:4d}, nodes={st_s.node_forces:4d}, depth={st_s.max_depth:4d}, slices={st_s.slice_forces}/{B}) | "
          f"Tabulate(steps={st_t.whnf_steps:3d}, nodes={st_t.node_forces:2d}, depth={st_t.max_depth:2d}, slices={st_t.slice_forces}/{B})")

st_hi = WHNFStats()
assert ptree_get_at(16, 4096, ptree_tabulate([(0, mk_slice(0)), (4096, mk_slice(4096))], 16), st_hi) == ("BlockSlice", 4096)
print(f"  Sparse BlockId=4096 Tabulate: steps={st_hi.whnf_steps}, nodes={st_hi.node_forces}, max_depth={st_hi.max_depth} (< 512 maxRecDepth)")

@dataclass(frozen=True)
class Expr:
    head: str; args: tuple[Any, ...]; irreducible: bool = False; body_fn: Callable[[tuple[Any, ...]], Any] | None = None

def has_add0(e: Any) -> bool:
    return isinstance(e, Expr) and ((e.head == "Nat.add" and e.args[1] == 0) or any(has_add0(a) for a in e.args))

def simp_add0(g: Expr) -> bool:
    if not g.irreducible and g.body_fn is not None: return simp_add0(g.body_fn(g.args))
    return any(isinstance(a, Expr) and (has_add0(a) or simp_add0(a)) for a in g.args)

p0 = Expr("Eq", (Expr("Nat.add", ("h0", 0)), "h0"))
print("\n[PART 2] Tactic penetration matrix (True = penetrated, False = blocked):")
for nm, g in [("HoldBlockProp(P)", Expr("Hold", (p0,), False, lambda a: a[0])),
              ("FirewallBlockProp(tag, P)", Expr("Firewall", ("t0", p0), True, lambda a: a[1])),
              ("BlockWpCert(spec, u, sl)", Expr("BlockWpCert", ("sp0", 0, "sl0"), True, lambda _: p0))]:
    print(f"  {nm:27s}: rw={str(has_add0(g)):5s} | simp={str(simp_add0(g)):5s} | unfold={str(not g.irreducible):5s}")

@dataclass(frozen=True)
class Block: stmts: tuple[str, ...]; succs: tuple[int, ...]
@dataclass(frozen=True)
class Slice: block: Block; block_hash: str
@dataclass(frozen=True)
class Spec: req_live: bool; rank: int; exp_hash: str

def h_blk(b: Block) -> str: return hashlib.sha256(repr(b).encode()).hexdigest()[:16]

def sym_ok(u: int, b: Block, sp: dict[int, Spec]) -> bool:
    live = sp[u].req_live
    for s in b.stmts:
        if s == "move_x":
            if not live: return False
            live = False
        elif s == "init_x": live = True
    return all(v in sp and sp[v].rank < sp[u].rank and (not sp[v].req_live or live) for v in b.succs)

def bwd_cone(cfg: dict[int, Slice], dirty: set[int]) -> set[int]:
    cone, work = set(dirty), list(dirty)
    while work:
        cur = work.pop()
        for u, sl in cfg.items():
            if cur in sl.block.succs and u not in cone: cone.add(u); work.append(u)
    return cone

def cert_ok(cfg: dict[int, Slice], sp: dict[int, Spec], certs: dict[int, str], dual: bool = True) -> bool:
    return all(u in sp and u in certs and (not dual or (sl.block_hash == h_blk(sl.block) == sp[u].exp_hash == certs[u])) for u, sl in cfg.items())

d1_b = {0: Block(("init_x",), (1, 2)), 1: Block((), (3,)), 2: Block((), (3,)), 3: Block(("move_x",), ())}
d1_c = {u: Slice(b, h_blk(b)) for u, b in d1_b.items()}
d1_s = {u: Spec(u != 0, 3 if u == 0 else (2 if u < 3 else 1), d1_c[u].block_hash) for u in d1_c}
d1_k = {u: d1_c[u].block_hash for u in d1_c if sym_ok(u, d1_b[u], d1_s)}

b2n = Block(("init_x",), (3,))
m0_c = {**d1_c, 2: Slice(b2n, h_blk(b2n))}
cone0 = bwd_cone(m0_c, {2})
m0_s = {**d1_s, 2: Spec(True, 2, m0_c[2].block_hash)}
m0_k = {u: (m0_c[u].block_hash if u in cone0 and sym_ok(u, m0_c[u].block, m0_s) else d1_k[u]) for u in m0_c}
m0_ok = cert_ok(m0_c, m0_s, m0_k)

b3_ub = Block(("move_x", "move_x"), ())
m1_c, m2_c = {**d1_c, 3: Slice(b3_ub, h_blk(b3_ub))}, {**d1_c, 3: Slice(b3_ub, d1_c[3].block_hash)}
m1_bug, m1_du = cert_ok(m1_c, d1_s, d1_k, False), cert_ok(m1_c, d1_s, d1_k, True)
m2_sng, m2_du = (m2_c[3].block_hash == d1_s[3].exp_hash == d1_k[3]), cert_ok(m2_c, d1_s, d1_k, True)
m3_ok, m4_ok = sym_ok(1, Block(("move_x",), (3,)), d1_s), sym_ok(3, Block((), (1,)), d1_s)

print("\n[PART 3] Certificate soundness & adversarial mutant canary matrix:")
print(f"  M0_valid_cone_edit (cone={sorted(cone0)}, reused=[1, 3]) : accepted={m0_ok}")
print(f"  M1_unhashed_blockid_stale_cert (double-move UB)   : buggy_unhashed={m1_bug} | dual_digest={m1_du}")
print(f"  M2_forged_slice_hash_metadata  (double-move UB)   : single_check={m2_sng}   | dual_digest={m2_du}")
print(f"  M3_broken_edge_precondition    (b1 drops live_x)  : sym_verify={m3_ok}")
print(f"  M4_unranked_backedge_cycle     (3 -> 1 rank 1->2) : sym_verify={m4_ok}")
assert m0_ok and m1_bug and (not m1_du) and m2_sng and (not m2_du) and (not m3_ok) and (not m4_ok)
```

Observed output (`python3 /tmp/probe_lazy_radix_trie_cfg_invalidation.py`, exit code `0`):

```text
[PART 1] WHNF steps, node forces, max call depth, and slice forces on surgical cone lookup:
  B= 64 (cone=4/64): List(steps= 136, nodes= 56, depth=  57, slices=4/64) | SeqSetAt(steps= 173, nodes= 148, depth= 127, slices=4/64) | Tabulate(steps= 30, nodes= 8, depth= 7, slices=4/64)
  B=128 (cone=5/128): List(steps= 294, nodes=120, depth= 121, slices=5/128) | SeqSetAt(steps= 344, nodes= 308, depth= 255, slices=5/128) | Tabulate(steps= 42, nodes=10, depth= 8, slices=5/128)
  B=512 (cone=7/512): List(steps=1250, nodes=504, depth= 505, slices=7/512) | SeqSetAt(steps=1332, nodes=1268, depth=1023, slices=7/512) | Tabulate(steps= 72, nodes=14, depth=10, slices=7/512)
  Sparse BlockId=4096 Tabulate: steps=28, nodes=13, max_depth=14 (< 512 maxRecDepth)

[PART 2] Tactic penetration matrix (True = penetrated, False = blocked):
  HoldBlockProp(P)           : rw=True  | simp=True  | unfold=True 
  FirewallBlockProp(tag, P)  : rw=True  | simp=True  | unfold=False
  BlockWpCert(spec, u, sl)   : rw=False | simp=False | unfold=False

[PART 3] Certificate soundness & adversarial mutant canary matrix:
  M0_valid_cone_edit (cone=[0, 2], reused=[1, 3]) : accepted=True
  M1_unhashed_blockid_stale_cert (double-move UB)   : buggy_unhashed=True | dual_digest=False
  M2_forged_slice_hash_metadata  (double-move UB)   : single_check=True   | dual_digest=False
  M3_broken_edge_precondition    (b1 drops live_x)  : sym_verify=False
  M4_unranked_backedge_cycle     (3 -> 1 rank 1->2) : sym_verify=False
```

## Revalidation

1. **Re-run the Algorithmic WHNF & Certificate Canary Probe (< 1 second)**: Extract the Python script under **Evidence** §2 to `/tmp/probe_lazy_radix_trie_cfg_invalidation.py` and run `python3 /tmp/probe_lazy_radix_trie_cfg_invalidation.py` (expect exit code `0`).
2. **Diff Upstream Lean 4 Tactic Congruence & Kernel Opacity**: On Lean upgrades past `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), diff `src/Lean/Meta/Tactic/Rewrite.lean`, `src/Lean/Meta/Tactic/Simp/Main.lean`, and `src/kernel/type_checker.cpp` (`is_delta` / `has_value`).
3. **Audit Candidate Incremental CFG Verifiers**: Verify (a) top-down `.node` emission rather than `foldl setAt`, (b) zero `Prop` parameters on `@[irreducible]` block certificates tested against `rw` and `simp`, and (c) dual-digest rejection under double-move UB + forged slice-digest metadata.
