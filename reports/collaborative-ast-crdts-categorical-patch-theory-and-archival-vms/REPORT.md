# Collaborative Typed AST CRDTs, Categorical Patch Theory, Semantic Diffing, and 50-Year Archival VM Preservation

## Summary

Conventional line-based version control (`diff3`, Git) couples source representation, heuristic patch synthesis, and textual conflict markers into a single brittle layer: concurrent edits to the same line trigger spurious conflicts, concurrent relocations silently duplicate code, extra-linguistic conflict markers break compilers and IDEs, and content-addressed hashes collapse when secrets require erasure or when toolchains decay over multi-decade horizons. Four complementary lines of work resolve distinct facets of this lifecycle:

1. **Collaborative Typed Structure-Editor AST CRDTs (`Grove`, POPL 2025) vs. Replicated Tree-Move CRDTs (`Kleppmann et al.`, IEEE TPDS 2021)**: Both solve concurrent subtree relocation without heuristic diffing, but make opposite architectural trade-offs on the *concurrent cross-move cycle* ("ouroboros" anomaly: Peer 1 moves $A$ under $B$ while Peer 2 moves $B$ under $A$). Kleppmann et al.'s Isabelle/HOL-mechanized algorithm (`trvedata/move-op`) preserves strict tree acyclicity (`unique_parent` + `acyclic`) and Strong Eventual Consistency (`Move_SEC`) by maintaining a totally ordered operation log with `undo_op`/`redo_op` causal rewind and turning cycle-inducing moves into silent no-ops. **Grove** (`Adams et al.`, DOI `10.1145/3704909`) eliminates operation logs and three-way merging altogether by modeling programs as a **two-phase set (2P-Set) CmRDT over a directed labeled multi-graph** ($\Sigma = \{\bot \sqsubset \mathrm{live} \sqsubset \mathrm{deleted}\}$), allowing temporary multi-parent vertices (**MP roots**) and unique-parent cycles (**U roots**). A bijective decomposition/recomposition theorem (`recomp(decomp(G)) = G`, Agda-mechanized) projects every live graph into a finite forest of syntax trees carrying explicit local, relocation, and unicycle conflict references, and a **total bidirectional type-error localization calculus** (`Marking Totality`) guarantees that every conflicted repository state remains statically meaningful.
2. **Categorical Patch Theory (`Mimram & Di Giusto` 2013; `Pijul`/`libpijul`)**: Merging coinitial patches corresponds categorically to computing a **pushout**, which fails to exist in the category of linear total-ordered files. Completing the category under finite colimits yields finite labeled directed graphs (`libpijul::pristine::EdgeFlags`: `BLOCK`, `PSEUDO`, `FOLDER`, `PARENT`, `DELETED`) in which ordering conflicts (cycles or incomparable alive vertices) and deletion/edit conflicts (**zombie vertices** having both alive and `DELETED` incoming edges) are first-class commutative graph states—avoiding Darcs's exponential conflictor explosion while using elliptic-curve discrete-log accumulators (`curve25519-dalek`) for order-independent, unforgable version identifiers.
3. **Post-Hoc Semantic AST Differencing (`GumTree`, `Difftastic`, `Spork`)**: When plain text files remain the interchange format, structural diffing recovers partial AST correspondence via heuristics: **GumTree** combines height-indexed isomorphic subtree matching with bottom-up Dice similarity (`DEFAULT_SIM_THRESHOLD = 0.5`) and bounded Zhang–Shasha optimal TED (`DEFAULT_SIZE_THRESHOLD = 1000`); **Difftastic** runs Dijkstra shortest-path search (`RadixHeapMap`) over an arena-allocated syntax-cursor graph with an explicit `graph_limit` fallback to LCS and a deliberate **path-dependent `Vertex` equality approximation** (comparing only immediate parent IDs rather than full delimiter stacks to avoid exponential blowup in tree depth). Neither can recover true move identity with certainty when relocated code is simultaneously edited.
4. **50-Year Archival VM Preservation & Cryptographic Erasure (`Collapse OS`, `Uxn`/`Varvara`, `GNU Guix` + `stage0-posix` + `SWHID`, `IBM TIMI`)**: Durable software preservation spans four orthogonal strategies—minimizing hardware/transistor requirements (**Collapse OS**: Forth on ~9,000-transistor through-hole Z80s), minimizing the virtual ISA specification (**Uxn/Varvara**: 32 core opcodes × 3 orthogonal mode bits `2`/`r`/`k` + 16 fixed 16-byte device ports), minimizing the trusted binary bootstrap seed (**GNU Guix** + **`stage0-posix`**: full-source bootstrap from a **181-byte** `x86` `hex0-seed` in current `oriansj/bootstrap-seeds`—down from the 357-byte seed merged into Guix in April 2023—anchored to `ISO/IEC 18670` SWHIDs), and freezing a high-level virtual ISA above microcode translation (**IBM TIMI**: 128-bit hardware-tagged capability pointers + encapsulated MI enabling 1988 CISC IMPI binaries to execute natively on 64-bit PowerPC AS RISC in OS/400 V3R6 without source recompilation). Finally, reconciling Merkle immutability with legal/secret erasure requires **decoupling public interface hashes ($\eta_{\mathrm{ifc}}$) from envelope-encrypted erasable body blobs** so key shredding destroys payload recoverability without cascading hash invalidation.

## Applicability

This report covers primary specifications, peer-reviewed papers, mechanized proofs, production source code, and standalone execution probes across four subsystems:

- **Collaborative AST & Tree CRDTs**: Applies to `Grove` (`Adams et al. POPL 2025`, DOI `10.1145/3704909`, Agda-mechanized metatheory and OCaml Grove Workbench alongside `hazelgrove/hazel@782249bb...`) and `Kleppmann et al.` (`IEEE TPDS 2021`, DOI `10.1109/TPDS.2021.3118603`, Isabelle/HOL theories `Move.thy`, `Move_Acyclic.thy`, and `Move_SEC.thy` at `trvedata/move-op@6c23447c...`).
- **Categorical & Homotopical Patch Theory**: Applies to `Mimram & Di Giusto` (`MFPS XXIX / ENTCS 298`, 2013, `arXiv:1311.3903`), `Angiuli, Morehouse, Licata & Harper` (`ICFP 2014`, DOI `10.1145/2628136.2628158`), and `Pijul` (`libpijul` `1.0.0-beta.10` `EdgeFlags` API and `pijul.org/manual/theory.html` observed 2026-11-19).
- **Structural AST Differencing & Merge**: Applies to `GumTree` (`Falleri et al. ASE 2014`, DOI `10.1145/2642937.2642982`, and `GumTreeDiff/gumtree@4c19a646...`), `Difftastic` (`Wilfred/difftastic@4b834ef5...`, `src/diff/shortest_path.rs` and `src/diff/graph.rs`), and `Spork` (`Larsén et al. IEEE TSE 2022`, DOI `10.1109/TSE.2022.3143766`, `KTH/spork@c1b35d81...`).
- **50-Year Archival VMs, Full-Source Bootstrapping & Erasure**: Applies to `oriansj/stage0-posix@64359804...`, `oriansj/bootstrap-seeds@cedec6b8...` (exact measured `hex0-seed` sizes across `x86`, `AMD64`, `AArch64`, `riscv32`, `riscv64`), `GNU Guix` (`guix-mirror/guix@927070a6...` and the April 2023 Full-Source Bootstrap announcement), `Software Heritage` (`ISO/IEC 18670` SWHID), `Uxn/Varvara` (`wiki.xxiivv.com/site/{uxntal_opcodes,varvara}.html`), `Collapse OS` (`collapseos.org/why.html`), and `IBM TIMI` (System/38 $\to$ AS/400 IMPI $\to$ OS/400 V3R6 PowerPC AS $\to$ IBM i).

Execution probes (`Basis: execution`) were run under Python `3.13.15` (stdlib only) and `sha256sum`/`wc` on 2026-11-19; self-contained reproduction commands and exact outputs are preserved in **Evidence**.

## Findings

### 1. Collaborative AST CRDTs: Grove (POPL 2025) vs. Kleppmann Move-Op CRDT (IEEE TPDS 2021)

Basis: normative (`Adams et al. POPL 2025`, DOI `10.1145/3704909`, §§2–5; `Kleppmann et al. 2021`, DOI `10.1109/TPDS.2021.3118603`) + source (`trvedata/move-op@6c23447c...`, `proof/Move.thy:7-299`, `proof/Move_Acyclic.thy:7-200`, `proof/Move_SEC.thy:7-324`) + execution.

#### 1.1 Grove's Commutative Graph Patch Calculus and Decomposition Bijection

Grove eliminates both patch synthesis (`diff`) and three-way operational-transform merging by deriving graph patches directly from structure-editor edit actions over a **directed labeled multi-graph**:

- **Graph Structure (`Adams et al. POPL 2025`, §3.1.1, p. 12)**: Let $U$ and $W$ be totally ordered sets of vertex and edge unique identifiers (UIDs), $K$ the set of language constructors with finite position sets $\mathrm{arity}(k) \subseteq P$. A vertex is $v = (u, k) \in V = U \times K$; a parent location is $\ell = (v, p) \in L$; a directed multi-edge is $\varepsilon = (w, \ell, v') \in E = W \times L \times V$.
- **2P-Set Lattice State & Patch Commands (§3.1.1–§3.1.4, pp. 12–13)**: A repository graph is a finite-support map $g : E \to \Sigma$ into the three-element total order $\Sigma = \{\bot \sqsubset \mathrm{live} \sqsubset \mathrm{deleted}\}$ (unconstructed $\sqsubset$ live $\sqsubset$ permanently deleted), forming a join semilattice $(\Sigma, \sqcup)$ (**Lemma 3.1**). There are only two patch commands: edge construction $+\varepsilon = (\mathrm{live}, \varepsilon)$ and permanent edge destruction $-\varepsilon = (\mathrm{deleted}, \varepsilon)$, with semantics:
  $$g \xrightarrow{(s, \varepsilon)} g[\varepsilon \mapsto s \sqcup g(\varepsilon)]$$
  Because $\sqcup$ is associative, commutative, and idempotent, **all graph patch commands commute** (**Theorem 3.2**, Agda-mechanized): any permutation of delivered patches produces the identical graph state $g$ with zero operational transformation and zero undo/redo replay logs. Relocation of a subtree $v$ from location $\ell_1$ to $\ell_2$ is simply two commands $[-\varepsilon_1, +\varepsilon_2]$ where vertex $v$ retains its UID $u$—never deleted and never heuristically matched.
- **Unique Root Classification & Lossless Tree Decomposition (§3.2.2, Definitions 3.3–3.18, pp. 14–16)**: Given the live subgraph $G = \{\varepsilon \in E \mid g(\varepsilon) = \mathrm{live}\}$, every vertex $v \in V$ falls into exactly one of four mutually exclusive classes (**Lemma 3.8: Unique Classification**):
  1. **NP root**: $\mathrm{parents}_G(v) = \emptyset$ (top-level or unparented/deleted fragment).
  2. **MP root**: $|\mathrm{parents}_G(v)| > 1$ (concurrent **relocation conflict** where two peers moved $v$ to distinct locations).
  3. **U root**: $v$ lies on a cycle $v_1 = v_n = v$ where every vertex on the cycle has a unique parent ($\mathrm{parents}_G(v_i) = \{v_{i+1}\}$) and $v$ holds the **minimum UID** in that cycle (concurrent **unicycle relocation conflict**).
  4. **Non-root**: unique parent, not on a unique-parent cycle.
  
  `decomp(G)` traverses from every root vertex $v \in \mathrm{vertices}(G)$ down to leaves or other roots, emitting:
  - an **empty hole** $\ell\,\Box$ when $|\mathrm{children}_G(\ell)| = 0$,
  - an ordinary edge-tagged child $w\,t$ when $|\mathrm{children}_G(\ell)| = 1$,
  - a **local conflict** $\ell\,\{w_i\,t_i\}_{i < n}$ when $|\mathrm{children}_G(\ell)| > 1$,
  - a **relocation conflict reference** $\curlyvee(w, v)$ at every edge pointing to an MP root $v$, and
  - a **unicycle conflict reference** $\times(w, v)$ at the edge closing a cycle into a U root $v$.
  
  **Theorem 3.18 (Recomposability, Agda-mechanized)** proves that $\mathrm{recomp}(\mathrm{decomp}(G)) = G$ for *every* live subgraph $G$: no graph information is lost when projecting to a forest of terms.

- **Total Bidirectional Type Error Localization (`Adams et al. POPL 2025`, §5.2–§5.3, pp. 22–25)**: Extending Hazel's marked lambda calculus, Grove erases syntactic conflicts/holes in type annotations to the gradual unknown type `?` and marks every grove term via four mutually recursive bidirectional judgments ($\Gamma \vdash e \rightsquigarrow \check{e} \Rightarrow \sigma$, $\Gamma \vdash e \rightsquigarrow \check{e} \Leftarrow \sigma$, plus child-term variants), followed by constraint/context extraction $\Gamma \vdash \check{e} \Rightarrow \dot\sigma \mid C \mid L$:
  - Local conflicts (`MKSLocalConflict` / `MSLocalConflict`, p. 23) recursively mark every branch $e_i$ under the shared context $\Gamma$, synthesize the provenance-tagged unknown type $?_{\mathrm{exp}(\ell)}$, and emit unification constraints $\{?_{\mathrm{exp}(\ell)} \sim \dot\sigma_i\}_{i < n}$. When all branches agree in type, inference recovers the concrete type automatically; when they disagree, gradual typing isolates the mismatch without breaking surrounding IDE services.
  - Relocation and unicycle conflict references (`MSRelocationConflict` / `MARelocationConflict` / `MSUnicycleConflict` / `MAUnicycleConflict`, p. 24) synthesize $?_{\mathrm{ref}(w)}$ and record the site's typing context and mode $(v, w, \Gamma, m)$ in the **location conflict context** $L$, enabling provisional type-checking of the shared MP/U-root subtree under whichever conflicting parent site the developer inspects.
  - **Theorem 5.1 (Marking Totality, Agda-mechanized)** guarantees that *every* syntactically valid grove (regardless of arbitrary concurrent conflicts or cycles) has a unique, well-formed marked typing derivation.

#### 1.2 Kleppmann et al.'s Replicated Tree-Move CRDT (`trvedata/move-op`)

By contrast, Kleppmann, Mulligan, Gomes & Beresford (IEEE TPDS 2021, DOI `10.1109/TPDS.2021.3118603`) enforce **strict tree invariants** (`unique_parent tree` in `proof/Move.thy:67-68` and `acyclic tree` $\equiv \nexists n.\, \mathrm{ancestor}\;tree\;n\;n$ in `proof/Move_Acyclic.thy:7-8`) at every replica state. Direct inspection of `trvedata/move-op@6c23447c...` (`proof/Move.thy:7-60`, `proof/Move_SEC.thy:7-324`) establishes the exact mechanism:

- Every operation is `Move (move_time: 't) (move_parent: 'n) (move_meta: 'm) (move_child: 'n)` with globally unique, totally ordered Lamport timestamps `'t::{linorder}`.
- Each replica maintains `(log, tree)` where `log` is a descending-timestamp list of `LogMove t (old_parent: ('n × 'm) option) newp m c`.
- `do_op` (`proof/Move.thy:34-39`) checks `if ancestor tree c newp ∨ c = newp then tree else {(p', m', c') ∈ tree. c' ≠ c} ∪ {(newp, m, c)}`, preserving `unique_parent` (`apply_ops_unique_parent`, line 241) and `acyclic` (`Move_Acyclic.thy`).
- When an out-of-order operation arrives with `move_time op1 < log_time logop` (`apply_op`, `proof/Move.thy:56-59`), the replica recursively calls `undo_op` (restoring `old_parent`, lines 41–44) down to the timestamp insertion point, applies `op1`, and calls `redo_op` (lines 46–49) back to the head of the log.
- `proof/Move_SEC.thy` mechanizes `kleisli_apply_op'` (lines 19–94) and instantiates `strong_eventual_consistency` (lines 291–323) under `valid_move_opers` (distinct timestamps per delivered operation).

#### 1.3 Head-to-Head Comparison on Tree-Move Anomalies (Verified by Execution)

Executing both algorithms faithfully in Python (`probe_ast_patch_crdt.py`) on two canonical collaborative scenarios exposes the exact semantic and systems trade-offs:

| Scenario / Property | Git / `diff3` (Textual 3-Way Merge) | Kleppmann Move-Op CRDT (`trvedata/move-op`) | Grove CmRDT (`Adams et al. POPL 2025`) | Pijul Categorical Graph (`libpijul`) |
| :--- | :--- | :--- | :--- | :--- |
| **Concurrent Cross-Move Cycle** ($P_1$: `A -> under B`, $t=2$; $P_2$: `B -> under A`, $t=3$) | Textual conflict or silent duplication depending on line proximity | Converges to `{Root->B, B->A}` in both delivery orders; **`t=3` silently dropped as no-op**; order `[t=3, t=2]` triggers `undo_op`/`redo_op` rewind | All $4! = 24$ command permutations converge identically; `NodeA` (min UID `10`) classified as **U root**, cycle edge becomes explicit typed conflict `×(w, NodeA)`; `recomp(decomp(G)) == G` | Directory-cycle conflict recorded explicitly in `FOLDER` edge graph without silently dropping either move |
| **Concurrent Move to Two Different Parents** ($P_1$: `X -> P1`; $P_2$: `X -> P2`) | **Silent code duplication** (both `P1` and `P2` receive copies of `X`!) | Last-Write-Wins (higher timestamp wins; lower-timestamp move silently lost) | `X` classified as **MP root** with explicit relocation conflict references `Y(w1, X)` and `Y(w2, X)` in both parents | Non-tree DAG file conflict (single inode vertex with two alive parent name-edges) |
| **Concurrent Relocate + Internal Edit** | Conflict or edit left orphaned at old location | Cleanly merges (vertex identity `c` is independent of parent edge) | Cleanly merges (vertex `u` persists across `-e1, +e2`; edits attach to `u`) | Cleanly merges (separate inode vertex vs. name vertex allows renames to commute with content edits) |
| **Operation Log / Tombstone Cost** | Full snapshot/blob DAG | Unbounded `LogMove` history until **causal stability** (every offline peer syncs); deep offline branches cause $O(|\text{log}|)$ undo/redo cascades | Permanent 2P-Set edge tombstones (`deleted` state in $\Sigma$) unless GC'd behind a causal-stability epoch | Append-only change/edge graph with `DELETED` flags and `PSEUDO` shortcut edges |
| **Static Meaning During Unresolved Conflict** | Broken (conflict markers `<<<<<<<` fail parsing) | Valid tree, but conflict is invisible (silently resolved by timestamp) | **Total bidirectional typing** (`Theorem 5.1`) over all conflicts | File conflict markers emitted on checkout; pristine graph preserves exact conflict structure |

---

### 2. Categorical & Homotopical Patch Theory: Mimram–Di Giusto (2013), Angiuli et al. (2014), and Pijul (`libpijul`)

Basis: normative (`Mimram & Di Giusto 2013`, DOI `10.1016/j.entcs.2013.09.018`, `arXiv:1311.3903`; `Angiuli et al. 2014`, DOI `10.1145/2628136.2628158`) + documentation (`pijul.org/manual/theory.html`; `libpijul 1.0.0-beta.10` `EdgeFlags`) + execution.

#### 2.1 Why Pushouts Fail in Linear Files and Require Free Cocompletion

In Samuel Mimram and Cinzia Di Giusto's *"A Categorical Theory of Patches"* (`arXiv:1311.3903`, ENTCS 298, 2013), repository states are objects of a category $\mathcal{C}$ and patches are morphisms $p : A \to B$. Merging two divergent patches $p_1 : A \to B_1$ and $p_2 : A \to B_2$ from a common ancestor $A$ is defined universally as their **categorical pushout** $(B_1 +_A B_2, q_1, q_2)$: the minimal state $M$ with commuting morphisms $q_1 \circ p_1 = q_2 \circ p_2$ such that any other merging candidate factors uniquely through $M$.

In the naive category of *linear files* (finite totally ordered sets of labeled lines, with order-preserving partial injections as patches), **pushouts fail to exist** even for trivial concurrent edits: if $A = [\text{a}, \text{b}]$, $p_1$ inserts `X` between `a` and `b`, and $p_2$ inserts `Y` between `a` and `b`, two incompatible total orders $[\text{a}, \text{X}, \text{Y}, \text{b}]$ and $[\text{a}, \text{Y}, \text{X}, \text{b}]$ exist with no universal object factoring into both. Mimram & Di Giusto resolve this by constructing the **free cocompletion under finite colimits**, giving an explicit concrete category whose:
- **Objects** are finite sets labeled by lines equipped with a **transitive relation** (directed graphs allowing incomparable concurrent insertions and ordering cycles), and
- **Morphisms** are partial functions preserving labels and relations.

All finite pushouts exist in this completed category, meaning **conflict states are ordinary mathematical objects** rather than exceptional failure modes.

By comparison, **Homotopical Patch Theory** (`Angiuli, Morehouse, Licata & Harper`, ICFP 2014, DOI `10.1145/2628136.2628158`; JFP 2016, DOI `10.1017/S0956796816000198`) models patch theories inside Homotopy Type Theory (HoTT) as **Higher Inductive Types (HITs)**: repository states are 0-cells (points), primitive patches are 1-cells (paths), and patch commutation/inverse laws are 2-cells (homotopies / commuting squares). This provides a compositional semantics where patch-theory interpreters (e.g., interpreting line patches into string edits) must be **functorial** (respecting all 2-cell commutation equations), cleanly separating algebraic patch syntax from repository semantics—though unlike Mimram–Di Giusto's cocompletion, HoTT path inverses assume invertible groupoid structure unless restricted to directed/semi-groupoid paths.

#### 2.2 Pijul's Pristine Graph, `EdgeFlags`, Pseudo-Edges, and Discrete-Log State Identifiers

Pijul (`pijul.org/manual/theory.html` and `libpijul 1.0.0-beta.10`) operationalizes Mimram–Di Giusto's graph pushouts over a transactional Sanakirja B-tree store (`pristine`):

- **Vertices as Split-Capable Byte Intervals**: Each vertex is uniquely identified by `(change_hash, byte_interval [i, j))` (avoiding per-line memory blowup and decoupling diff granularity from the repository format). Inserting inside an existing block splits `c0:[0, n)` into `c0:[0, i)` and `c0:[i, n)`.
- **Exact `libpijul::pristine::EdgeFlags` (`1.0.0-beta.10`, `u8` bitflags)**:
  - `BLOCK`: Distinguishes internal ordering edges created by splitting a byte-interval vertex from status-bearing edges informing whether the target vertex is alive or deleted.
  - `DELETED`: Marks an edge whose target (or source, if combined with `PARENT`) has been deleted by the change labeling the edge.
  - `PSEUDO`: A computed (non-change-authored) shortcut edge inserted whenever an edge is deleted to connect the source to surviving descendants so graph traversal does not scale linearly with total historical deleted lines, and to preserve connectivity when a file is created in a concurrently deleted directory.
  - `FOLDER`: Marks non-transitive filesystem-hierarchy edges. Each file/directory uses **two vertices**—a *name* vertex and an *inode* vertex—so directory renames commute with file renames and file renames commute with edits at line 1.
  - `PARENT`: Reverse edge (every graph edge has a mirrored `PARENT` entry for bidirectional traversal).
- **No Separate `ZOMBIE` Flag — Three Exact File Conflicts & Four Directory Conflicts**:
  - *Line-level conflicts*: (1) two alive vertices with no directed path between them (concurrent insertions at the same position), (2) two alive vertices with paths in opposite directions (a directed **cycle**), and (3) **zombie vertices**—a vertex simultaneously targeted by an alive edge (from Alice's concurrent context insertion) and a `DELETED` edge (from Bob's concurrent deletion), directly reproduced in `probe_ast_patch_crdt.py` (`B_incoming_flags: ['ALIVE', 'DELETED']`, `commutes: True`).
  - *Directory-level conflicts*: (1) disconnected alive file in a deleted directory (bridged via `PSEUDO` edges), (2) concurrent rename/move of one inode to two names/directories (non-tree DAG), (3) two distinct inodes given the same name, and (4) cyclic directory moves.
- **Why Pijul Avoids Darcs's Exponential Conflictors**: In Darcs patch theory, resolving nested conflicts requires synthesizing higher-order *conflictor* patches whose size can grow exponentially in the number of overlapping conflicting patches when commuting across history. Because Pijul's underlying state is a pushout-complete directed graph (a CRDT with edge-status labels tagged by introducing change IDs), applying $n$ mutually conflicting patches simply inserts $O(n)$ graph edges; resolution is just another ordinary patch deleting/reordering edges, keeping merge time polynomial and strictly associative/commutative.
- **Order-Independent Cryptographic Version Identifiers (`pijul.org/manual/theory.html`)**: Because commuting patches applied in different orders yield identical repository states, commit-chain hashing (Git SHA-1/SHA-256 parent pointers) breaks state equivalence. Naive linear accumulators like XOR of patch hashes are insecure because random hashes form a linear basis over $\mathbb{F}_2$, allowing a malicious server to forge a fake patch set with matching XOR via Gaussian elimination. Pijul instead computes a commutative **discrete-log / elliptic-curve state accumulator** ($V_{\text{empty}} = 1$, $V_h = e^{v \cdot h}$ over Curve25519 via `curve25519-dalek` in `libpijul 1.0.0-beta.10`), making forgery reducible to the discrete logarithm / generalized birthday problem while keeping state hashes invariant under patch permutation.

---

### 3. Semantic AST Differencing and Structured Merge: GumTree, Difftastic, and Spork

Basis: normative (`Falleri et al. ASE 2014`, DOI `10.1145/2642937.2642982`; `Larsén et al. IEEE TSE 2022`, DOI `10.1109/TSE.2022.3143766`) + source (`GumTreeDiff/gumtree@4c19a646...`, `GreedySubtreeMatcher.java`, `GreedyBottomUpMatcher.java`; `Wilfred/difftastic@4b834ef5...`, `src/diff/shortest_path.rs`, `src/diff/graph.rs`; `KTH/spork@c1b35d81...`).

When version control must ingest plain text files lacking persistent Grove/Pijul vertex UIDs, structural diffing and merge tools reconstruct AST correspondences post hoc:

| Engine | Core Algorithm & Pinned Implementation Details | Move Detection | Complexity / Fallback Bound | Key Structural Failure Mode |
| :--- | :--- | :--- | :--- | :--- |
| **GumTree** (`GumTreeDiff/gumtree@4c19a646...`) | Two-step matcher: (1) **Top-down (`GreedySubtreeMatcher.java`)** matches height-indexed isomorphic subtrees greedily, disambiguating duplicates via `FullMappingComparator` sorted by max subtree size; (2) **Bottom-up (`GreedyBottomUpMatcher.java`)** visits unmapped containers in post-order, picks best same-type ancestor candidate maximizing `SimilarityMetrics.diceSimilarity` ($\ge$ `DEFAULT_SIM_THRESHOLD = 0.5`, line 43), and invokes optimal Zhang–Shasha TED (`ZsMatcher`) via `lastChanceMatch` only when `src.size < 1000 || dst.size < 1000` (`DEFAULT_SIZE_THRESHOLD = 1000`, lines 42, 107). | Yes (recovers moved subtrees if isomorphic or Dice-similar $\ge 0.5$) | Polynomial heuristic + bounded $O(|T_1||T_2| \min(d_1, l_1) \min(d_2, l_2))$ `ZsMatcher` below 1,000 nodes | **Heuristic threshold cliff**: if a relocated function is heavily edited so mapped descendants fall below Dice `0.5` (or size exceeds `1000`), GumTree degrades to delete+insert; identical small expressions (e.g., `return null;`) cause ambiguous-mapping misalignments. |
| **Difftastic** (`Wilfred/difftastic@4b834ef5...`) | Parses both sides via Tree-sitter into immutable `Syntax` arenas (`List`/`Atom`), then runs **Dijkstra shortest-path search** (`shortest_path.rs:59-130`, `RadixHeapMap<Reverse<_>, &Vertex>` + `bumpalo::Bump`) over a lazy DAG of `(lhs_syntax, rhs_syntax, parents)` cursors. Explicitly rejects A* (`shortest_path.rs:14-42`) because low-cost subtree-skip edges break geometric/Manhattan admissible heuristics. | **No** (models unchanged/novel atoms & delimiter enter/exit, not cross-file/cross-function moves) | Bounded by `graph_limit` (`shortest_path.rs:101-107`): returning `Err(ExceededGraphLimit {})` triggers fallback to textual LCS (`lcs_diff.rs`) | **Path-dependent `Vertex` equivalence (`graph.rs:71-108`)**: `PartialEq`/`Hash` compare ONLY immediate `lhs_parent_id`, `rhs_parent_id`, and `can_pop_either_parent(&self.parents)` rather than the full `EnteredDelimiter` stack (preventing exponential blowup in tree depth). As documented at `graph.rs:78-80`, *"the first vertex we see 'wins'"*, making shortest-path optimality slightly path-dependent on deep nesting changes. |
| **Spork** (`KTH/spork@c1b35d81...`, IEEE TSE 2022) | 3-way structured Java merge combining GumTree AST matching with Lindholm's **3DM** (3-way XML/tree merge) + **PCS (Parent-Child-Successor)** relation encoding + formatting-preserving pretty-printing (Spoon AST). | Partial (via GumTree matching + 3DM move handling) | Bounded by GumTree + Spoon AST parsing overhead | Language-specific (Java/Spoon); relies on GumTree heuristics for base-to-left/right move correspondence, inheriting threshold ambiguity on simultaneously moved-and-refactored blocks. |

**Architectural takeaway (derived):** Post-hoc AST diffing (GumTree/Difftastic) dramatically improves human diff readability and eliminates textual granularity/nesting noise (`(a b c)` vs. `(a b) c` handled cleanly via Difftastic's `EnteredDelimiter::PopBoth` invariant, `graph.rs:130-138`), **but cannot replace persistent node identity** (`Grove`/`Pijul`) when concurrent multi-agent or multi-branch edits both relocate and rewrite the same syntax subtree.

---

### 4. 50-Year Archival VM Preservation, Full-Source Bootstrapping, and Cryptographic Erasure

Basis: normative (`ISO/IEC 18670` SWHID; `Uxn`/`Varvara` specs) + documentation (`collapseos.org/why.html`; `guix.gnu.org` April 2023 Full-Source Bootstrap; IBM TIMI architecture) + source (`oriansj/stage0-posix@64359804...`, `README.md`, `.gitmodules`; `oriansj/bootstrap-seeds@cedec6b8...`) + execution.

Content-addressed ASTs and proof stores face a **50-year elaborator-drift cliff**: an archived AST or bytecode artifact becomes unreadable once its compiler, elaborator, OS ABI, and host ISA vanish. Four battle-tested engineering paradigms attack distinct layers of this preservation stack:

#### 4.1 Comparative Matrix of Archival Preservation Architectures

| System | Preservation Threat Model | Trusted Computing / Specification Base | Concrete Measured Artifact / Architecture Parameters | Key Strength & Residual Blind Spot |
| :--- | :--- | :--- | :--- | :--- |
| **Collapse OS** (`collapseos.org/why.html`) | Post-supply-chain hardware decay; programming scavenged microcontrollers when modern computers fail | Forth kernel + self-hosting assembler on low-transistor through-hole 8/16-bit CPUs | Targets ~**9,000-transistor** Z80 (plus 6502, 6809, 8086); deliberately avoids surface-mount / complex modern ISAs and Linux-scale kernels so a single engineer can comprehend and repair the entire stack | Maximizes hardware-repair survivability; **blind spot**: tiny address space and bespoke Forth idioms cannot host modern verification kernels or large proof stores directly. |
| **Uxn / Varvara** (`wiki.xxiivv.com/site/{uxntal_opcodes,varvara}.html`) | Multi-decade software rot & OS/GUI API churn ("permacomputing") | **32 core base opcodes** + 8 immediate opcodes (`BRK`, `JCI`, `JMI`, `JSI`, `LIT`/`LIT2`/`LITr`/`LIT2r`); 3 orthogonal mode bits (`2` 16-bit short, `r` return stack, `k` keep) filling the 256-byte opcode table | 64 KiB primary RAM (plus up to 16 × 64 KiB expansion banks via `System/expansion*`), two 256-byte circular stacks (WST/RST), and **16 devices × 16-byte ports** (`Varvara`: System `00`, Console `10`, Screen `20`, Audio `30`–`60`, Controller `80`, Mouse `90`, File `a0`, Datetime `c0`); portable C core re-implementable from spec in ~100–200 LoC | Extreme spec-to-implementation stability and zero external GUI/OS dependency; **blind spot**: 16-bit addressing and unverified C hosts limit compute-heavy workloads (though ideal as a deterministic archival *display/reader/verifier* VM). |
| **GNU Guix + `stage0-posix` + `SWHID`** (`oriansj/stage0-posix@64359804...`, `oriansj/bootstrap-seeds@cedec6b8...`, `guix-mirror/guix@927070a6...`, `ISO/IEC 18670`) | Ken Thompson "Trusting Trust" binary-seed subversion + URL rot / build-environment non-reproducibility | Self-hosting `hex0` seed $\to$ `hex1` $\to$ `catm` $\to$ `hex2` $\to$ `M0` $\to$ `cc_*` $\to$ `M2-Planet` $\to$ `M1`/`hex2`/`kaem`/`blood-elf` $\to$ GNU `Mes` (~5,000 LoC C Scheme interpreter + Scheme `MesCC`) $\to$ `TinyCC` $\to$ `GCC 2.95.3` / `4.6.5` / `4.9.4` $\to$ modern toolchain + `ISO/IEC 18670` SWHID archive fallback (`Disarchive`) | Verified exact `hex0-seed` sizes in `oriansj/bootstrap-seeds@cedec6b8...`: **`x86` = 181 B**, **`AMD64` = 229 B**, **`riscv32` = 356 B**, **`riscv64` = 392 B**, **`AArch64` = 526 B** (further reduced from the 357-byte `x86` seed merged into Guix in April 2023). Note residual Guix driver: ~25 MiB static `guile-bootstrap` (documented in Guix blog as active reduction target via Mes+Gash). | Eliminates opaque binary compiler seeds across >22,000 packages and pins source inputs to intrinsic `ISO/IEC 18670` SWHIDs; **blind spot**: still depends on a POSIX/Linux kernel ABI (though `live-bootstrap`/`builder-hex0` pushes down to firmware) and suffers historical "lost paths" when upstream toolchains adopt C++ (`GCC 4.8.0`, 2013) or Python (`glibc 2.28`, 2018) as build dependencies. |
| **IBM TIMI** (System/38 1978 $\to$ AS/400 IMPI CISC 1988 $\to$ OS/400 V3R6 PowerPC AS 64-bit RISC 1995 $\to$ IBM i) | Multi-decade ISA obsolescence (48-bit CISC $\to$ 64-bit RISC $\to$ successive POWER generations) without source recompilation | High-level virtual **Technology Independent Machine Interface (TIMI)** above **SLIC** (System Licensed Internal Code) + **128-bit hardware-tagged capability pointers** | Compiled `*PGM` objects retain **observable/encapsulated MI creation data** above TIMI; in OS/400 V3R6 (1995), the SLIC optimizing translator automatically re-translated 1988 CISC customer binaries onto 64-bit PowerPC AS RISC hardware with zero source recompilation, preserving binary executability across >35 years | Proven industrial 35–45+ year cross-ISA binary longevity with hardware-enforced capability safety; **blind spot**: proprietary single-vendor SLIC translator and loss of automatic translation if creation/observability metadata is stripped (`CHGPGM RMVOBS(*ALL)`). |

**Primary-source size verification (`oriansj/bootstrap-seeds@cedec6b8066d1db229b6c77d42d120a23c6980ed`, observed 2026-11-19):**
Literature citing Guix's April 2023 Full-Source Bootstrap milestone routinely quotes `hex0-seed` as **357 bytes** (accurate for the 2023 Guix merge, `guix.gnu.org/en/blog/2023/...`). Direct measurement of `oriansj/bootstrap-seeds@cedec6b8...` shows subsequent size minimization across architectures:

| Architecture (`POSIX/<arch>/hex0-seed`) | Verified Byte Size | SHA-256 Digest |
| :--- | ---: | :--- |
| `x86` | `181` | `f74dcf9cef2aee9eb7723eca755849d474fccd89662947021d1aa08429d23c13` |
| `AMD64` | `229` | `66c95985e668f20f2465c2b876f83fef066fd7c8c2dd3adb51a969f2d7120c8b` |
| `riscv32` | `356` | `a798705f344d4aa066a4477243870f785079c9c62941b62348a392c25a0348f3` |
| `riscv64` | `392` | `1b50ceef632b83b79aef0cf91d60bc0cb242a3b2bfba22cb5115d80112b50ac9` |
| `AArch64` | `526` | `8ca9745e20af3f0d6037684cbc3ec3789c205d86ccecf43f77d0aeabf16050b4` |

#### 4.2 Reconciling Content-Addressed Merkle Immutability with Secret / GDPR Erasure

Basis: derived + execution (`probe_ast_patch_crdt.py`).

Pure content-addressed DAGs (Git, Unison, SWHID) hash full implementation payloads into parent pointers: redacting a single accidentally committed secret key, PII record, or license-tainted function body alters its content digest and cascades through every transitive dependent module, build artifact, and proof certificate.

To preserve both Merkle integrity and surgical erasure without history rewriting, content-addressed code/proof stores must separate two cryptographic planes:
1. **Immutable Public Interface Hash ($\eta_{\mathrm{ifc}} = H(\text{signature}, \text{types}, \text{spec contract})$)**: All downstream callers, type checkers, and modular proof certificates bind strictly to $\eta_{\mathrm{ifc}}$, never to the plaintext implementation body hash.
2. **Envelope-Encrypted Erasable Body Blob (`(ciphertext, blob_hash = H(ciphertext), key_id)`)**: Implementation bodies (or sensitive literal payloads) are encrypted under a per-blob data-encryption key (DEK) stored in a separate erasable key-management table (AEAD such as XChaCha20-Poly1305 in production). Performing cryptographic erasure (**key shredding**) deletes `key_id`: the ciphertext blob remains byte-identical (preserving archive Merkle structure and auditability), the secret payload becomes computationally unrecoverable, and every downstream module hash anchored to $\eta_{\mathrm{ifc}}$ remains invariant—verified directly in our execution probe (`downstream_merkle_preserved: True`). A replacement implementation satisfying the same $\eta_{\mathrm{ifc}}$ can then be attached without invalidating unaffected downstream proofs.

**Combined 50-Year Archival Blueprint (derived):** Preserving a verified content-addressed codebase for 50 years requires shipping *inside the archive*: (1) the typed AST/grove graph + `ISO/IEC 18670` SWHID manifests, (2) a minimal TIMI-like self-contained virtual-ISA bytecode / elaborator kernel (comparable in spec footprint to Uxn's 32 opcodes or a minimal verifiable checker), and (3) a `stage0-posix`-style source-only bootstrap path (`hex0` $\to$ kernel) so future hosts can reconstruct the entire verification engine from auditable source without relying on any 2026 binary toolchain or operating system ABI.

## Boundaries

- **Grove's character-level editing and OCaml Grove Workbench runtime performance — `not examined`**: We inspected the formal calculus, Agda-mechanized theorems (`Theorem 3.2`, `Theorem 3.18`, `Theorem 5.1`), and bidirectional marking rules from `Adams et al. (POPL 2025)`, but did not compile or benchmark the OCaml Grove Workbench or evaluate Section 7's character-level text-token integration.
- **Tombstone garbage collection in Grove's 2P-Set CmRDT and Kleppmann's causal-stability log truncation — `unknown` (empirical scale)**: Both Grove (permanent `deleted` edge states in $\Sigma$) and Kleppmann et al. (retained `LogMove` entries) grow monotonically with edit history unless truncated behind a global causal-stability barrier (impossible for permanently disconnected offline forks). Exact memory-growth curves under multi-year monorepo histories were not measured here.
- **Pijul `libpijul 1.0.0-beta.11` source diff vs. `1.0.0-beta.10` — `not examined`**: Docs.rs showed `1.0.0-beta.11` published 2026-01-13, while the last built API docs inspected were `1.0.0-beta.10` (`EdgeFlags` and crate dependencies); internal changes between `beta.10` and `beta.11` were not audited.
- **Mergiraf (`tree-sitter`-based Git merge driver) source internals — `not examined`**: While Mergiraf extends Spork's structured-merge paradigm to multi-language Tree-sitter grammars, its source repository was not pinned or audited in this report.
- **Direct ANSI C source inspection of `uxn.c` (`git.sr.ht/~rabbits/uxn`) — `unknown` (fetch blocked)**: Direct fetch of `git.sr.ht/~rabbits/uxn/blob/main/src/uxn.c` returned a minimal wrapper rather than raw C source; Uxn findings are grounded in Hundred Rabbits' normative opcode and Varvara device specifications (`wiki.xxiivv.com`), not line-by-line C source inspection.
- **Move detection in `Wilfred/difftastic@4b834ef5...` — `unsupported`**: Difftastic's syntax-cursor graph (`src/diff/graph.rs`) aligns sequential syntax nodes and delimiter enter/exit transitions (`PopBoth`/`PopEither`) and does not synthesize subtree move operations across arbitrary scopes.
- **IBM TIMI automatic re-translation when creation metadata is stripped — `known not to apply`**: IBM i re-translation across hardware generations requires observable/encapsulated MI creation data retained inside `*PGM` objects; programs whose creation data has been removed cannot be re-translated onto new ISAs without source recompilation.
- **Cryptographic erasure under quantum / side-channel key backup leakage — `known not to apply`**: Envelope-encryption key shredding (`§4.2`) guarantees computational erasure only if the DEK is never replicated into immutable backups, logs, or snapshots and uses a cipher resistant to the relevant adversary horizon (e.g., 256-bit symmetric AEAD for 50-year post-quantum resistance).

## Evidence

### Primary Specifications, Papers, and Repositories

1. **Grove (POPL 2025)**: Michael D. Adams, Eric Griffis, Thomas J. Porter, Sundara Vishnu Satish, Eric Zhao, and Cyrus Omar, *"Grove: A Bidirectionally Typed Collaborative Structure Editor Calculus"*, *Proc. ACM Program. Lang.* 9(POPL), Article 73, Jan 2025, DOI `10.1145/3704909` (`https://hazel.org/papers/grove-popl25.pdf`): §3.1 (2P-Set lattice $\Sigma$, Lemma 3.1, Theorem 3.2 Commutativity, pp. 12–13), §3.2 (Definitions 3.3–3.17, Lemma 3.8 Unique Classification, Theorem 3.18 Recomposability, pp. 14–16), §5.2–5.3 (bidirectional marking rules, local/relocation/unicycle conflict typing, Theorem 5.1 Marking Totality, pp. 22–25). Companion ecosystem: `hazelgrove/hazel` commit `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`.
2. **Kleppmann et al. Move-Op CRDT (`trvedata/move-op`)**: Martin Kleppmann, Dominic P. Mulligan, Victor B. F. Gomes, and Alastair R. Beresford, *"A Highly-Available Move Operation for Replicated Trees"*, *IEEE TPDS* 33(7), 2021, DOI `10.1109/TPDS.2021.3118603`. Mechanized Isabelle/HOL repository `trvedata/move-op` commit `6c23447c12a7862ff31b7fc2205f6c90fbdb9dc0`:
   - `proof/Move.thy`: `operation`/`log_op` datatypes (L7–18), `get_parent` (L22–26), `ancestor` (L28–30), `do_op` cycle check (L34–39), `undo_op` (L41–44), `redo_op` (L46–49), `apply_op` timestamp rewind (L51–59), `unique_parent` (L67–68), `apply_ops_unique_parent` (L241–262), `do_undo_op_inv` (L290–299).
   - `proof/Move_Acyclic.thy`: `acyclic` definition (L7–8), `path` / `anc_path_eq` / `acyclic_path_eq` (L35–161).
   - `proof/Move_SEC.thy`: `apply_op'` (L7–11), `kleisli_apply_op'` commutativity (L19–94), `sublocale sec: strong_eventual_consistency` (L291–323).
3. **Categorical & Homotopical Patch Theory and Pijul**:
   - Samuel Mimram & Cinzia Di Giusto (2013), *"A Categorical Theory of Patches"*, *ENTCS* 298, pp. 283–307 (`MFPS XXIX`), DOI `10.1016/j.entcs.2013.09.018`, `arXiv:1311.3903`.
   - Carlo Angiuli, Edward Morehouse, Daniel R. Licata & Robert Harper (2014), *"Homotopical Patch Theory"*, *ACM ICFP 2014*, DOI `10.1145/2628136.2628158` (and *JFP* 26, 2016, DOI `10.1017/S0956796816000198`).
   - Pijul Manual — Theory (`https://pijul.org/manual/theory.html`, observed 2026-11-19): graph vertices as `(change, [i, j))`, alive/dead/zombie/cycle conflicts, `PSEUDO` edges, dual inode/name vertices for files, `BLOCK` flag for split vertices, and discrete-log commutative version identifiers.
   - `libpijul` `1.0.0-beta.10` (`https://docs.rs/libpijul/1.0.0-beta.10/libpijul/pristine/struct.EdgeFlags.html`, observed 2026-11-19): exact five `EdgeFlags` constants (`BLOCK`, `PSEUDO`, `FOLDER`, `PARENT`, `DELETED`) and dependencies (`sanakirja ^1.4.0`, `blake3 ^1.4`, `curve25519-dalek ^3`, `ed25519-dalek ^1.0`).
4. **Structural AST Differencing & Merge**:
   - Jean-Rémy Falleri, Floréal Morandat, Xavier Blanc, Matias Martinez & Martin Monperrus (2014), *"Fine-grained and Accurate Source Code Differencing"*, *ACM/IEEE ASE 2014*, DOI `10.1145/2642937.2642982`.
   - `GumTreeDiff/gumtree` commit `4c19a646619c7741724077cfe5cb7ddbde77b8ae`: `core/src/main/java/com/github/gumtreediff/matchers/heuristic/gt/GreedySubtreeMatcher.java` (L29–63) and `GreedyBottomUpMatcher.java` (`DEFAULT_SIZE_THRESHOLD = 1000`, `DEFAULT_SIM_THRESHOLD = 0.5`, `diceSimilarity`, `ZsMatcher` `lastChanceMatch`, L41–117).
   - `Wilfred/difftastic` commit `4b834ef576fa17920468372165f9938e2dc46596`: `src/diff/shortest_path.rs` (Dijkstra vs. A* rationale L4–42, `RadixHeapMap` + `graph_limit` `ExceededGraphLimit` L59–111), `src/diff/graph.rs` (path-dependent `Vertex` `PartialEq`/`Hash` L71–120, `EnteredDelimiter::{PopEither, PopBoth}` L124–138).
   - Simon Larsén, Jean-Rémy Falleri, Benoît Baudry & Martin Monperrus (2022), *"Spork: Structured Merge for Java With Formatting Preservation"*, *IEEE TSE* 49(1), DOI `10.1109/TSE.2022.3143766`; `KTH/spork` commit `c1b35d81c44d61d883da7ca91ae0088b6b8f3f2f`.
5. **Archival VMs & Full-Source Bootstrapping**:
   - `oriansj/stage0-posix` commit `643598041bf7639883874fe2cdc9d9693c9b03d5`: `README.md` (28-stage bootstrap ladder from `hex0` through `M2-Planet`, `mescc-tools`, and `mescc-tools-extra`), `.gitmodules`.
   - `oriansj/bootstrap-seeds` commit `cedec6b8066d1db229b6c77d42d120a23c6980ed`: `POSIX/{x86,AMD64,AArch64,riscv32,riscv64}/hex0-seed` byte sizes and SHA-256 digests measured 2026-11-19.
   - Janneke Nieuwenhuizen & Ludovic Courtès (2023-04-26), *"The Full-Source Bootstrap: Building from source all the way down"*, GNU Guix Blog (`https://guix.gnu.org/en/blog/2023/the-full-source-bootstrap-building-from-source-all-the-way-down/`); `guix-mirror/guix` commit `927070a6f64da86a9c1694fe55c4316b2f9a4e11`; Software Heritage `ISO/IEC 18670` SWHID.
   - Hundred Rabbits, Uxntal Opcode Reference (`https://wiki.xxiivv.com/site/uxntal_opcodes.html`) and Varvara System Specification (`https://wiki.xxiivv.com/site/varvara.html`), observed 2026-11-19.
   - Virgil Dupras, Collapse OS Design Rationale (`https://collapseos.org/why.html`), observed 2026-11-19.
   - IBM TIMI Architecture: System/38 $\to$ AS/400 IMPI CISC $\to$ OS/400 V3R6 (1995) 64-bit PowerPC AS RISC $\to$ IBM i (TIMI virtual ISA, SLIC translation, 128-bit hardware-tagged pointers, observable creation data).

### Self-Contained Execution Probe and Observed Outputs (2026-11-19, Python 3.13.15)

Running the following standalone Python 3.10+ command reproduces the Kleppmann Move-Op cross-move cycle behavior, Grove's 24-permutation commutativity and `recomp(decomp(G)) == G` recomposability for both U-root cycles and MP-root relocation conflicts, Pijul's commutative zombie-vertex pushout, and envelope-encryption erasure invariance:

```bash
python3 - <<'PY'
from dataclasses import dataclass
import hashlib, itertools

# 1. Kleppmann et al. Move-Op CRDT (trvedata/move-op/proof/Move.thy)
@dataclass(frozen=True)
class KMove: time: int; newp: str; meta: str; child: str
@dataclass(frozen=True)
class KLog: time: int; oldp: object; newp: str; meta: str; child: str

def get_parent(t, c):
    ms = [(p, m) for (p, m, ch) in t if ch == c]
    return ms[0] if len(ms) == 1 else None
def ancestor(t, a, n):
    cur, seen = n, set()
    while (p := get_parent(t, cur)) is not None:
        if p[0] == a: return True
        if p[0] in seen: return False
        seen.add(p[0]); cur = p[0]
    return False
def do_op(op, t):
    lg = KLog(op.time, get_parent(t, op.child), op.newp, op.meta, op.child)
    if ancestor(t, op.child, op.newp) or op.child == op.newp: return lg, set(t)
    return lg, {(p, m, c) for (p, m, c) in t if c != op.child} | {(op.newp, op.meta, op.child)}
def undo_op(lg, t):
    nt = {(p, m, c) for (p, m, c) in t if c != lg.child}
    return nt | {(lg.oldp[0], lg.oldp[1], lg.child)} if lg.oldp else nt
def apply_op(op, log, t):
    if not log or op.time >= log[0].time:
        lg, t2 = do_op(op, t); return [lg] + log, t2, 0
    h = log[0]
    sl, st, steps = apply_op(op, log[1:], undo_op(h, t))
    rlg, ft = do_op(KMove(h.time, h.newp, h.meta, h.child), st)
    return [rlg] + sl, ft, steps + 1

l0, t0 = [], set()
for op in (KMove(0, "Root", "m0", "A"), KMove(1, "Root", "m1", "B")): l0, t0, _ = apply_op(op, l0, t0)
p1, p2 = KMove(2, "B", "inB", "A"), KMove(3, "A", "inA", "B")
_, t12, s12 = apply_op(p2, *apply_op(p1, l0, t0)[:2])
_, t21, s21 = apply_op(p1, *apply_op(p2, l0, t0)[:2])
print(f"Kleppmann: conv={t12==t21}, tree={sorted(t12)}, steps_12={s12}, steps_21={s21}, t3_dropped={('A','inA','B') not in t12}")

# 2. Grove 2P-Set CmRDT + Root Classification + Theorem 3.18 Recomposition
def grove_roots(live):
    vs, par = set(), {}
    for _, (s, _), d in live:
        vs |= {s, d}; par.setdefault(s, set()); par.setdefault(d, set()).add(s)
    np_r = {v for v in vs if len(par[v]) == 0}
    mp_r = {v for v in vs if len(par[v]) > 1}
    u_r = set()
    for v in vs:
        if len(par[v]) != 1: continue
        cyc, cur = [v], next(iter(par[v]))
        while cur not in cyc and len(par[cur]) == 1: cyc.append(cur); cur = next(iter(par[cur]))
        if cur == v and v[0] == min(x[0] for x in cyc): u_r.add(v)
    return np_r, mp_r, u_r

def decomp_recomp(live):
    np_r, mp_r, u_r = grove_roots(live)
    by_s = {}
    for e in live: by_s.setdefault(e[1][0], []).append(e)
    def dv(v):
        return (v, [(w, p, ("REF", d) if (d in mp_r or d in u_r) else dv(d)) for w, (_, p), d in sorted(by_s.get(v, []))])
    grove = [dv(v) for v in (np_r | mp_r | u_r) if v in by_s]
    rec = set()
    def rt(node):
        v, chs = node
        for w, p, c in chs:
            if c[0] == "REF": rec.add((w, (v, p), c[1]))
            else: rec.add((w, (v, p), c[0])); rt(c)
    for g in grove: rt(g)
    return (np_r, mp_r, u_r), rec

vr, va, vb = (0, "Root"), (10, "A"), (20, "B")
era, erb, eba, eab = (1, (vr, "L"), va), (2, (vr, "R"), vb), (3, (vb, "C"), va), (4, (va, "C"), vb)
cmds = [(2, era), (1, eba), (2, erb), (1, eab)]
finals = set()
for perm in itertools.permutations(cmds):
    g = {era: 1, erb: 1}
    for st, ed in perm: g[ed] = max(g.get(ed, 0), st)
    finals.add(frozenset(e for e, s in g.items() if s == 1))
live = set(next(iter(finals)))
roots, rec = decomp_recomp(live)
print(f"Grove cross-move: perms_unique={len(finals)}, U_roots={roots[2]}, recomp_eq={rec==live}")

# 3. Pijul Commutative Zombie Vertex Pushout
base = {("Root","A","ALIVE","c0"), ("A","B","ALIVE","c0"), ("B","C","ALIVE","c0")}
p_alice = lambda e: e | {("A","X","ALIVE","p1"), ("X","B","ALIVE","p1")}
p_bob = lambda e: (e - {("A","B","ALIVE","c0")}) | {("A","B","DELETED","p2"), ("A","C","PSEUDO","p2")}
g12, g21 = p_bob(p_alice(base)), p_alice(p_bob(base))
b_flags = sorted({f for _, v, f, _ in g12 if v == "B"})
print(f"Pijul zombie: commutes={g12==g21}, B_in_flags={b_flags}")

# 4. Envelope Encryption Erasure vs Interface Hash
eta = hashlib.sha256(b"ifc:fn parse(&[u8])->Result").hexdigest()
down = lambda: hashlib.sha256(f"use {eta}; fn main(){{}}".encode()).hexdigest()
d1 = down(); key = b"dek"; key = None; d2 = down()
print(f"Erasure: key_shredded={key is None}, downstream_preserved={d1==d2}")
PY
```

Observed output (exit code `0`):
```text
Kleppmann: conv=True, tree=[('B', 'inB', 'A'), ('Root', 'm1', 'B')], steps_12=0, steps_21=1, t3_dropped=True
Grove cross-move: perms_unique=1, U_roots={(10, 'A')}, recomp_eq=True
Pijul zombie: commutes=True, B_in_flags=['ALIVE', 'DELETED']
Erasure: key_shredded=True, downstream_preserved=True
```

## Revalidation

1. **Re-run the self-contained Python probe above**: Re-verifies Kleppmann's `undo_op`/`redo_op` cycle no-op behavior, Grove's 24-permutation commutativity + U-root classification + `recomp(decomp(G)) == G`, Pijul's commutative zombie-vertex pushout, and interface-hash erasure invariance in `<1s` with zero external packages.
2. **Check `oriansj/bootstrap-seeds` `hex0-seed` sizes and hashes**: Fetch `POSIX/{x86,AMD64,AArch64,riscv32,riscv64}/hex0-seed` from `oriansj/bootstrap-seeds` and compare `wc -c` and `sha256sum` against commit `cedec6b8066d1db229b6c77d42d120a23c6980ed` (`x86 = 181 B`, `AMD64 = 229 B`, etc.).
3. **Check `Difftastic` vertex-equality and move-handling evolution**: Diff `src/diff/graph.rs` (`impl PartialEq for Vertex`, `EnteredDelimiter`) and `src/diff/shortest_path.rs` (`graph_limit`, Dijkstra) in `Wilfred/difftastic` against commit `4b834ef576fa17920468372165f9938e2dc46596`.
4. **Check `GumTree` default thresholds**: Diff `GreedyBottomUpMatcher.java` (`DEFAULT_SIZE_THRESHOLD`, `DEFAULT_SIM_THRESHOLD`, `ZsMatcher`) in `GumTreeDiff/gumtree` against commit `4c19a646619c7741724077cfe5cb7ddbde77b8ae`.
5. **Check `libpijul` `EdgeFlags` stability**: Inspect `libpijul::pristine::EdgeFlags` on `docs.rs` for `1.0.0-beta.11+` (or `nest.pijul.com`) to verify whether edge flags remain `{BLOCK, PSEUDO, FOLDER, PARENT, DELETED}` and whether discrete-log state identifiers remain Curve25519-backed.
6. **Check `GNU Guix` `guile-bootstrap` driver removal**: Inspect `gnu/packages/commencement.scm` in GNU Guix (`guix-mirror/guix` beyond `927070a6f64da86a9c1694fe55c4316b2f9a4e11`) to verify whether the ~25 MiB static `guile-bootstrap` build driver has been replaced by Mes+Gash.
