# Incremental SMT Proof Repair, Certificate Diffing, and Modular Proof Caching

## Summary

Sustaining sub-second Day-2 verification turnaround as verified codebases evolve requires decoupling **proof search** (unstable and superlinear in background context) from **certificate validation and reuse** (linear, content-addressed, and local to edited regions). Across production verifiers and proof checkers, naive caching fails under routine edits for three structural reasons: (1) linear proof formats (positional `(depth, index)` references in Alethe and monotonic integer clause IDs in LRAT) suffer cascading renumbering when a single prefix clause is inserted; (2) environment-wide query hashes invalidate every downstream proof when an unrelated upstream declaration is added; and (3) unscoped memoization of hash-consed terms across quantifier binders is unsound under bound-variable permutation.

Five mechanisms govern sound, high-hit-rate incremental proof maintenance:

1. **Content-addressed Merkle proof DAGs with De Bruijn canonicalization:** Lifting linear Alethe or LRAT scripts into directed acyclic graphs (`ProofNodeForest` in Carcara) and keying sub-derivations by bottom-up Merkle digests over locally-nameless (De Bruijn) and equality-normalized clauses eliminates positional renumbering misses while avoiding the binder-capture soundness bug documented in `carcara/src/ast/polyeq.rs:86–111` (where unscoped pointer-pair caching equates non-$\alpha$-equivalent formulas).
2. **Pre-SMT transitive symbol and trigger pruning:** Auto-active verifiers isolate blast radius *before* solver invocation: Verus partitions modules (`BucketId::Module`) and `#[verifier::spinoff_prover]` functions (`BucketId::Fun`) over a fixed-point worklist (`vir/src/prune.rs`) that activates `broadcast use` axioms only when every symbol/type in a trigger tuple is reached; Dafny pairs AST entity/dependency checksums with `{:id ...}` UNSAT-core dependency tracking (`ProofDependencyManager.cs`); and current F* (`FStarC`) has replaced legacy `.hints` UNSAT-core files with lazy `.checked` pruning summaries (`SolverState.fst` `Given_lazy` + `prune_decls`) and `(push)/(pop)` `goal_tree` leaf-selective fuel escalation (`Solver.fst`).
3. **Two-command parser lookback and scoped async cancellation:** Interactive elaborators such as Lean 4 (`src/Lean/Language/Lean.lean`) step back **two commands** before `firstDiffPos?` to handle docstring-backtracking grammar shifts, reuse `IO.Promise`-backed `SnapshotTree` prefixes while syntax and `InfoTree` positions match (`withNarrowedArgTacticReuse`), and cancel only invalidated async subtrees (`SnapshotTask.cancelRec`).
4. **Punctured sub-certificate repair across LRAT/LIDRUP, Alethe, and `SplitDBM`:** Under local CFG edits, backward cone-of-influence slicing (`carcara/src/slice.rs`) replaces invalidated subtrees with `:rule "hole"` obligations filled by targeted `hole_solver`/`lia_solver` passes (`elaborator/mod.rs`); incremental SAT (`LIDRUP`) guards block clauses behind assumption literals and weaken/restore rules; and abstract-interpretation fixpoints (`Crab` `split_dbm_domain`) store Bellman-Ford vertex potentials $\pi$ (`potential`) enabling $O(|E|)$ consistency checking and Cotton-Maler incremental closure over `unstable` vertices, guarded by explicit modular-arithmetic bounds (`BvNoWrapEdgeGuard`).
5. **Spec-vs-certificate module separation:** Keeping solver-emitted certificates outside human-audited specification modules ensures local certificate repair never invalidates caller contracts.

## Applicability

This report characterizes incremental proof reuse, certificate diffing, and blast-radius isolation across seven pinned upstream subjects in `REPORT.json`:

- **Certificate Checkers & Abstract Domains:** `ufmg-smite/carcara` (`819f30914665019898cbad7e09d3962053b6f97a`, `v1.1.0`), `leanprover/lean4` (`7438ab3d3f79465e36114caa82254540fa007fc7`, `Language/Lean.lean` and `BVDecide` LRAT), and `seahorn/crab` (`b1eeb1a9402ab0664e962f26f89d923f8514284c`, `split_dbm.hpp`).
- **Modular Verifiers & Proof-Repair Engines:** `verus-lang/verus` (`0dab219272ac2353320bd177ebb3929453b90a9e`), `dafny-lang/dafny` (`75de7486da5a473a5aba2add8ff80fc5bbe8337f`), `FStarLang/FStar` (`fc1776afe592ed8eef352c6610614a70d77b3b66`), and `uwplse/pumpkin-pi` (`a7743d4665d8c7a0ebfd9d39e1247ee7804d402b`).

**Corpus Scope & F\* Version Qualification:** Baseline Alethe rule syntax, Carcara's two-layer checker/elaborator pipeline, and standalone LRAT checking are covered in `smt-sat-alethe-carcara-and-numerical-proof-certificate-reconstruction` and `sat-inprocessing-drat-lrat-frat-checkers-maxsat-and-qbf-skolem-certificates`; SMT E-matching instability root causes are covered in `proof-fragility-smt-instability-and-verification-scaling-walls`. Without duplicating Alethe syntax, this report focuses on **post-edit invalidation, diffing, slicing, and modular caching**. Note that while older F* releases used VCS-tracked `<Module>.fst.hints` Z3 UNSAT-core files, `FStarC` at `fc1776afe592ed8eef352c6610614a70d77b3b66` has removed `FStarC.Hints.fst` in favor of `.checked`-embedded pruning summaries (`SolverState.fst`) and IDE `Solver.Cache`; both designs are contrasted below.

## Findings

### 1. Structural Certificate Diffing and Proof-Term Content Hashing

#### 1.1 Positional Address Fragility vs. Unpooled `ProofNodeForest` Identity

In linear Alethe (`Vec<ProofCommand>`) and LRAT scripts, premises use **positional coordinates**: `(depth, index)` frame offsets in Carcara (`src/ast/node.rs:287–296`) and integer clause IDs `cid` in LRAT. Inserting $k$ prefix clauses (e.g., adding an early guard in a function) shifts every subsequent index by $+k$, causing positional caches to miss on **100%** of unchanged derivations.

`Basis: source + execution + derived`

Carcara's `ProofNodeForest` (`src/ast/node.rs:4–32, 244–363`) lifts command lists into an `Rc<ProofNode>` DAG tracking cross-scope dependencies in `SubproofNode::outbound_premises` (`node.rs:69–80, 235–237`). However, `impl Rc<ProofNode>::new` (`node.rs:114–126`) documents a crucial invariant:
- **Terms are pooled; proof nodes are not:** `Term`s are hash-consed in `ast::pool::Pool`, whereas `Rc<ProofNode>::new` calls `Rc::new_raw(value)` without pooling; identical proof steps built in separate runs have **distinct `PartialEq`/`Hash` identities** (`node.rs:117–120`).
- **Bottom-Up Merkle Step Digest:** Cross-run reuse therefore requires computing an explicit postorder digest (`Rc<ProofNode>::traverse`, `node.rs:129–178`):
  $$M(\text{Assume}(\varphi)) = H_2(\texttt{"assume"}, \hat{h}(\varphi)), \quad M(\text{Step}(r, C, A, P, D)) = H_2\!\Big(\texttt{"step"}, r, \operatorname{sort}\{\hat{h}(l) \mid l \in C\}, [\hat{h}(a) \mid a \in A], [M(p) \mid p \in P], [M(d) \mid d \in D]\Big)$$
  Sorting clause literals absorbs implicit clause reorderings and duplicate literals (`ElaborationPass::{Uncrowd, Reordering}` in `src/elaborator/mod.rs:77–82`), while keeping rule arguments $A$ ordered.

#### 1.2 The Unscoped Alpha-Equivalence Cache Soundness Trap

Compiler capture passes routinely rename bound variables or flip `=` operands across edits. Carcara's `Polyeq` (`src/ast/polyeq.rs:61–118`) documents why naive global pair caching over pooled `Rc<Term>` pointers is **unsound** under $\alpha$-equivalence (`polyeq.rs:86–111`):

```text
a := (and (forall ((x Int) (y Int)) (< x y)) (forall ((x Int) (y Int)) (< x y)))
b := (and (forall ((x Int) (y Int)) (< x y)) (forall ((y Int) (x Int)) (< x y)))
```

`Basis: source + execution + derived`

Because `(< x y)` has free names `"x"` and `"y"`, a hash-consed `Pool` allocates all four inner bodies at the **same** `Rc<Term>` pointer $p$. Comparing the first `forall` maps `(x -> $0, y -> $1)` on both sides and caches `(p, p) -> Equal`. Comparing the second `forall`—where `b` maps `(y -> $0, x -> $1)`—hits `(p, p)` and **falsely accepts `a` $\equiv_\alpha$ `b`**! Carcara fixes this via `HashMapStack` (`push_scope`/`pop_scope` on every binder, `polyeq.rs:221, 228`), trading away cross-binder cache reuse. Canonicalizing bound variables to **locally nameless De Bruijn indices (`bvar(k)`)** and sorting symmetric `Operator::Equals` child digests at interning time restores sound `O(1)` global Merkle sharing.

---

### 2. Blast-Radius Isolation Across Function, Module, and Tactic Boundaries

#### 2.1 Comparative Blast-Radius Matrix Across Production Verifiers

`Basis: source + documentation + derived`

| System & Source | Isolation Unit | Pruning / Caching Mechanism | Survives Unrelated Upstream Edits? | Primary Invalidation Cliff |
| :--- | :--- | :--- | :--- | :--- |
| **Verus** (`buckets.rs:16–119`, `prune.rs:69–236`) | `BucketId::Module(Path)` default; `BucketId::Fun(Path, Fun)` via `#[verifier::spinoff_prover]`. | Worklist reachability over `Fun`, `ReachedType`, `TraitImpl`, `RevealGroup`; trigger-gated `broadcast use` (`L211–225`). | Opaque callee body edits; unreached items and broadcast axioms with unreached triggers. | Without `spinoff_prover`, sibling edits in the same module mutate the shared module bucket's Z3 context. |
| **Dafny / Boogie** (`ProofDependencyManager.cs:15–88`; CAV 2015) | Procedure / Lemma & `vcsSplits` blocks. | AST Entity + transitive Dependency Checksums; `{:id "idN"}` UNSAT-core mapping. | Comment/whitespace edits; sibling body edits outside transitive spec dependencies. | Editing any transitively referenced `function` or `ensures` invalidates caller checksums even if unused in the UNSAT core. |
| **F\* (`FStarC`)** (`SolverState.fst:33–56, 251–350`, `Solver.fst:121–167`, `Cache.fst:30–50`) | `.checked` module summary + `goal_tree` `(push)/(pop)` leaves. | Lazy `.checked` `ld_sums` pruning (`prune_decls`) + leaf-only fuel retry (`ask_configs`) + IDE `hash (g, q)`. | Unreached upstream `.checked` `DeclFun`/`DefineFun`/`Assume` entries are **never deserialized** (`L35–39`). | `Solver.Cache` (`Cache.fst:38`) hashes full `env` `g` alongside `q`, missing on any earlier declaration in the open module. |
| **Lean 4** (`Language/Lean.lean:22–273`) | Command (2-command lookback) + opt-in tactic `SnapshotTree`. | Persistent `Environment` + `IO.Promise` `SnapshotBundle` (`withNarrowedArgTacticReuse`) + `SnapshotTask.cancelRec`. | Commands $> 2$ slots above `firstDiffPos?`; unchanged `cdot`/non-wildcard `induction` prefixes. | Edits shift byte offsets in trailing `Syntax`, invalidating tactics that record span positions in `InfoTree` (`L132–136`). |
| **CoqHammer / Sledgehammer** (JAR 2018) | Reconstructed kernel script (`sauto` / `metis`). | ATP/SMT extracts minimal premise core once and freezes finite lemma names in source text. | **100% immune** to ambient library additions (10,000 new lemmas cannot enter frozen call). | Renaming or changing the statement of a listed premise breaks local reconstruction. |
| **PUMPKIN Pi** (`uwplse/pumpkin-pi`, PLDI 2021) | CIC proof term across type equivalences. | Decompiles proof over `(DepConstr, DepElim, Iota)` configuration + equivalence transport. | Transports inductive proofs across datatype representation changes (`Nat <-> Pos`) **without search**. | Requires explicit/discovered type equivalence $(\alpha \simeq \beta)$; non-isomorphic spec changes do not lift. |

#### 2.2 Quantifier Instability and F\*'s Migration from `.hints` to `SolverState` Pruning

Zhou et al. (*Mariposa*, FMCAD 2023) showed across Dafny, F\*, Komodo, and Verus that semantics-preserving symbol renamings, assertion permutations, and Z3 seed changes induce substantial verification instability via E-matching trigger competition. In `FStarLang/FStar` (`fc1776afe592ed8eef352c6610614a70d77b3b66`), this drove replacing legacy `.hints` files (which suffered VCS merge conflicts on `query_index` shifts, Z3 version core-selection drift, and timeout cliffs on cold fallback) with two deterministic mechanisms:
1. **Lazy `.checked` Symbol Pruning (`SolverState.fst:251–299`):** `give_delay_assumptions` indexes `Assume`/`DeclFun`/`DefineFun` dependencies in `Pruning.pruning_state` from compact `.checked` `ld_sums` (`Given_lazy ld`), pruning background context *before* Z3 runs—even on brand-new or edited queries.
2. **Goal-Tree Leaf Fuel Escalation (`Solver.fst:121–167, 566–582`):** `emit_goals` wraps shared context in `(push)/(pop)` and retries *only* failed leaf `goal_id`s at higher `fuel`/`ifuel`.

`Basis: source + documentation + derived`

#### 2.3 Lean 4's Two-Command Lookback and Scoped Async Cancellation

`leanprover/lean4/src/Lean/Language/Lean.lean` establishes two interactive reuse invariants:
1. **Two-Command Lookback (`Lean.lean:35–79`):** Editing strictly *after* an earlier command can alter two prior parse trees: in `structure Signature where \n /-- doc -/ \n Sort : Type`, `Sort` fails as a field and backtracks across `/-- doc -/`, producing `structure Signature where` ($C_{k-1}$) plus `/-- doc -/ <missing>` ($C_k$); appending `s` (`Sorts : Type`) absorbs both into $C_{k-1}$. Stepping back two commands before `firstDiffPos?` is necessary and sufficient.
2. **Subtree-Scoped Cancellation (`Lean.lean:184–230`):** Because a finished prefix tactic may store an asynchronous kernel-checking `Task` inside its `Snapshot`, cancelling a document-global token upon edit would corrupt reusable snapshots; `SnapshotTask.cancelRec` therefore cancels *only* subtrees rejected for reuse (`L207–215`).

`Basis: source + derived`

---

### 3. Sub-Certificate Invalidation and Repair for LRAT, Alethe, and `SplitDBM`

#### 3.1 Clause-Content LRAT Replay, `LIDRUP`, and Tseitin `BitBlastGate` Coupling

`Basis: source + documentation + execution + derived`

1. **Clause-Content Merkle Replay:** Indexing LRAT `addRup(cid, C, hints)` steps by canonical sorted-literal digests $h(C)$ rather than numeric `cid` allows any pre-edit RUP step whose antecedent digests $\{h(C_i)\}$ remain present post-edit to replay in linear time under renumbered IDs. In our 2-block benchmark (**Evidence**), a `+3` prefix clause insertion yields `0/5` positional hits vs. `3/5` (`100%` of unchanged Block 1) Merkle DAG hits.
2. **Assumption-Guarded `LIDRUP` (Fazekas et al. LPAR 2024):** Guarding per-block clauses with activation literals $(\neg \alpha_B \lor C)$ and emitting **LIDRUP** steps (addition, RUP hints, clause **weakening** on edited blocks, and clause **restoration** on unedited blocks) preserves solver learned clauses and linear checking across incremental edits.
3. **Verified Tseitin `BitBlastGate`:** Cached CNF refutations prove a bitvector VC only if coupled to a kernel-checked Tseitin gate relation (`(\neg z \lor a) \land (\neg z \lor b) \land (z \lor \neg a \lor \neg b)` for $z \leftrightarrow a \land b$, checking `varId < maxVars` and duplicate-safe unit propagation).

#### 3.2 Alethe Cone Slicing and Hole-Guided Sub-Solver Repair

In `carcara` (`src/slice.rs:14–372`, `src/elaborator/mod.rs:30–255`):
1. **Cone-of-Influence Slicing (`slice.rs:64–92, 148–327`):** Forward tainting from modified `Assume` nodes marks only dependent `StepNode`s dirty; `get_transitive_premises` slices sub-cones via BFS, replacing outside steps with `:rule "hole" :args ("trust")` (`L253–264`) while preserving `Subproof` `assume`/discharge envelopes (`L151–179`).
2. **Punctured Hole Filling (`elaborator/mod.rs:149–160, 202–223`):** Invalidated internal steps whose premise clauses $P_1, \dots, P_m$ survive are converted into local `hole` / `lia_generic` / `sat_refutation` obligations concluding `cl`; `Elaborator::elaborate_hole` invokes external solvers strictly on $\bigwedge P_j \land \neg \text{cl}$ and splices the checked sub-proofs back into `ProofNodeForest`.

`Basis: source + derived`

#### 3.3 Incremental `SplitDBM` Fixpoint Certificates and Modular Wraparound Guards

In `seahorn/crab` (`include/crab/domains/split_dbm.hpp:66–140`, Gange et al. SAS 2016; Cotton & Maler SAT 2006), loop invariants $v - u \le w_{uv}$ store `std::vector<Wt> potential` (`L121`) and `vert_set_t unstable` (`L122`):
1. **$O(|E|)$ Potential Witness:** Checking $\pi(u) + w_{uv} - \pi(v) \ge 0$ across edges certifies negative-cycle freedom in **$O(|E|)$ additions** (avoiding $O(|V|^3)$ Floyd-Warshall in the TCB) and warm-starts incremental Dijkstra closure on non-negative reduced weights over `unstable` vertices after local block edits.
2. **Vertex Sum Type & `BvNoWrapEdgeGuard`:** Checkers must separate zero-reference vertex $v_0$ (`DbmVertex.zeroConst`) from MIR local `_0` (`.localVar 0`), fail closed (`none`) on OOB locals, and enforce $0 \le \text{expr}_{\mathbb{Z}} < 2^W$ (`BvNoWrapEdgeGuard`) on $W$-bit machine integers (`u64::MAX + 1` wraps to `0`, refuting unguarded $\mathbb{Z}$-invariants `tail - head <= 0`).

`Basis: source + execution + derived`

---

### 4. Engineering Day-2 Edit Locality in Kernel-Checked Certificate Pipelines

Five design rules synthesize these mechanisms for proof-producing Rust/Lean pipelines: (1) shard obligations and certificates per Rust item outside human-audited spec modules; (2) prune reachable symbols/triggers *before* computing query cache hashes; (3) key subproof caches on locally-nameless + sorted-`=` Merkle digests; (4) repair punctured `:rule "hole"` cones before falling back to whole-VC search; and (5) export $O(|E|)$ `SplitDBM` potentials and Tseitin gates for linear kernel replay:

```lean
import Init.Data.Int.Basic
import Init.Data.List.Basic

namespace IncrementalCertKernel

def posPart : Int → Nat | .ofNat n => n | .negSucc _ => 0
def negPart : Int → Nat | .ofNat _ => 0 | .negSucc n => n + 1
def intBle (a b : Int) : Bool := Nat.ble (posPart a + negPart b) (posPart b + negPart a)

inductive DbmVertex where
  | zeroConst
  | localVar (idx : Nat)

structure DbmEdge where
  src : DbmVertex
  dst : DbmVertex
  wt  : Int -- `val(dst) - val(src) <= wt`

def lookupOpt : List Int → Nat → Option Int
  | [], _ => none | x :: _, 0 => some x | _ :: xs, k + 1 => lookupOpt xs k

def evalVertex (env : List Int) : DbmVertex → Option Int
  | .zeroConst => some 0 | .localVar i => lookupOpt env i

def checkDbmPotentialWitness (pi : List Int) (edges : List DbmEdge) : Bool :=
  edges.all (fun e => match evalVertex pi e.src, evalVertex pi e.dst with
    | some pu, some pv => intBle pv (pu + e.wt) | _, _ => false)

def checkDbmStateBounded (widthBits : Nat) (env : List Int) (edges : List DbmEdge) : Bool :=
  let mod2W : Int := Int.ofNat (Nat.shiftLeft 1 widthBits)
  env.all (fun v => intBle 0 v && intBle (v + 1) mod2W) &&
  edges.all (fun e => match evalVertex env e.src, evalVertex env e.dst with
    | some u, some v => intBle (v - u) e.wt | _, _ => false)

theorem dbm_potential_ok :
    checkDbmPotentialWitness [0, 16] [⟨.localVar 0, .localVar 1, 16⟩, ⟨.localVar 1, .localVar 0, 0⟩] = true := rfl
theorem dbm_oob_rejected :
    checkDbmStateBounded 64 [10] [⟨.localVar 99, .zeroConst, 0⟩] = false := rfl
theorem dbm_wrap_rejected :
    checkDbmStateBounded 8 [255, 256] [⟨.localVar 0, .localVar 1, 16⟩] = false := rfl

end IncrementalCertKernel
```

`Basis: derived`

---

## Boundaries

- **`not examined` — Distributed Remote Proof CAS Protocols & Neural Premise Rankers:** Networked build caches (`deterministic-distributed-verification-and-remote-build-cache-integration`, `mathlib-cache-protocol-artifact-format-and-pruning`) and embedding-based premise selectors whose rankings drift across model retraining were **not examined**.
- **`unknown` — Optimal Craig-Interpolant / Activation-Literal Granularity on Monolithic CDCL Proofs:** Without per-block activation literals or interpolant cuts, CDCL conflict clauses can mix literals across all basic blocks, widening the `slice.rs` invalidation cone; the solver-overhead vs. post-edit Merkle hit-rate Pareto frontier on large Rust crates remains **unknown**.
- **`known not to apply` — Unscoped $\alpha$-Equivalence Caching and `Rc<ProofNode>` Pointer Deduplication:** Global `(Rc<Term>, Rc<Term>)` caching across binders (`polyeq.rs:86–111`) and cross-run deduplication via `HashSet<Rc<ProofNode>>` (`node.rs:116–126`) are **known not to apply**.
- **`unsupported` — Slicing `assume` Commands and Subproof-Nested `lia_generic` Extraction in Carcara `1.1.0`:** `carcara::slice::slice` on `ProofCommand::Assume` returns `None` (`slice.rs:149`), and `generate_lia_smt_instances` inside nested subproofs (`iter.depth() > 0`) is explicitly **unsupported** (`src/lib.rs:279–282`).

---

## Evidence

### Primary Upstream Source Coordinates (`2026-11-20`)

| Repository | Revision (40-char SHA) | Examined Paths & Lines | Verified Facts |
| :--- | :--- | :--- | :--- |
| `ufmg-smite/carcara` | `819f30914665019898cbad7e09d3962053b6f97a` | `src/lib.rs:165–304`; `src/ast/{node.rs:4–363, polyeq.rs:61–251}`; `src/slice.rs:14–372`; `src/elaborator/mod.rs:30–255` | Unpooled `Rc<ProofNode>` vs. pooled `Rc<Term>`; `Polyeq` `HashMapStack` binder scope fix; BFS `:rule "hole"` slicing; `Hole`/`SatRefutation` elaboration. |
| `verus-lang/verus` | `0dab219272ac2353320bd177ebb3929453b90a9e` | `source/rust_verify/src/buckets.rs:16–119`; `source/vir/src/prune.rs:24–250` | `BucketId::{Module, Fun}` (`spinoff_prover`); worklist pruning and multi-trigger `broadcast use` gating. |
| `dafny-lang/dafny` | `75de7486da5a473a5aba2add8ff80fc5bbe8337f` | `Source/DafnyCore/Verifier/ProofDependencyManager.cs:15–88` | `{:id "idN"}` Boogie AST labeling and UNSAT-core mapping to structured call/invariant dependencies. |
| `FStarLang/FStar` | `fc1776afe592ed8eef352c6610614a70d77b3b66` | `src/smtencoding/FStarC.SMTEncoding.{SolverState.fst:33–350, Solver.fst:49–850, Solver.Cache.fst:30–50}` | Removal of `.hints` in favor of `.checked` `ld_sums` lazy pruning (`prune_decls`), `goal_tree` leaf fuel retry, and IDE `hash (g, q)`. |
| `leanprover/lean4` | `7438ab3d3f79465e36114caa82254540fa007fc7` | `src/Lean/Language/Lean.lean:22–273`; `src/Std/Tactic/BVDecide/LRAT/Checker.lean:1–30` | Two-command parser lookback; `IO.Promise` `SnapshotTree` reuse; `InfoTree` span hazard; `SnapshotTask.cancelRec`. |
| `seahorn/crab` | `b1eeb1a9402ab0664e962f26f89d923f8514284c` | `include/crab/domains/split_dbm.hpp:1–140` | `split_dbm_domain` Bellman-Ford `potential` vector and `unstable` vertex set. |
| `uwplse/pumpkin-pi` | `a7743d4665d8c7a0ebfd9d39e1247ee7804d402b` | Coq proof-repair plugin | Configuration-based CIC proof-term transport across type equivalences. |

### Literature and Execution Record

- **Peer-Reviewed Papers:** B. Andreotti, H. Lachnitt, & H. Barbosa, *TACAS 2023*, DOI `10.1007/978-3-031-30823-9_19`; K. R. M. Leino & V. Wüstholz, *CAV 2015*, DOI `10.1007/978-3-319-21690-4_22`; Y. Zhou et al., *FMCAD 2023*, DOI `10.34727/2023/isbn.978-3-85448-060-0_26`; K. Fazekas, F. Pollitt, M. Fleury, & A. Biere, *LPAR 2024*, DOI `10.29007/pdcc`; T. Ringer et al., *PLDI 2021*, DOI `10.1145/3453483.3454033`; Ł. Czajka & C. Kaliszyk, *JAR* 61, 2018, DOI `10.1007/s10817-018-9458-4`.
- **Execution (`2026-11-20`, Python `3.13.15`, `linux` `x86_64`):** Standalone probe exited `0`, reproducing the unscoped $\alpha$-cache bug vs. De Bruijn Merkle separation, `0/5` positional vs. `3/5` Merkle DAG step hits under a `+3` clause-ID shift, and $O(|E|)$ `SplitDBM` potential + $2^{64}$ wrap checks.

---

## Revalidation

Run the following standard-library Python 3 probe (< 1 second) to revalidate De Bruijn Merkle hashing, Clause-Content Merkle DAG reuse, and `SplitDBM` potential/wraparound checks:

```bash
python3 - <<'PY'
import hashlib

shared_lt = ("lt", ("var", "x"), ("var", "y"))
ta = ("and", ("forall", ["x", "y"], shared_lt), ("forall", ["x", "y"], shared_lt))
tb = ("and", ("forall", ["x", "y"], shared_lt), ("forall", ["y", "x"], shared_lt))

def unscoped_buggy_eq(a, b, e1=(), e2=(), memo=None):
    memo = set() if memo is None else memo
    if (id(a), id(b)) in memo: return True
    if a[0] != b[0]: return False
    if a[0] == "var": ok = e1.index(a[1]) == e2.index(b[1])
    elif a[0] in ("lt", "and"):
        ok = unscoped_buggy_eq(a[1], b[1], e1, e2, memo) and unscoped_buggy_eq(a[2], b[2], e1, e2, memo)
    else:
        ok = unscoped_buggy_eq(a[2], b[2], tuple(a[1]) + e1, tuple(b[1]) + e2, memo)
    if ok: memo.add((id(a), id(b)))
    return ok

def debruijn_merkle(t, env=()):
    k = t[0]
    if k == "var": s = f"b:{env.index(t[1])}" if t[1] in env else f"f:{t[1]}"
    elif k == "eq":
        h1, h2 = sorted([debruijn_merkle(t[1], env), debruijn_merkle(t[2], env)])
        s = f"eq:{h1}:{h2}"
    elif k in ("lt", "and"): s = f"{k}:{debruijn_merkle(t[1], env)}:{debruijn_merkle(t[2], env)}"
    else: s = f"forall:{len(t[1])}:{debruijn_merkle(t[2], tuple(t[1]) + env)}"
    return hashlib.sha256(s.encode()).hexdigest()[:16]

assert unscoped_buggy_eq(ta, tb) is True and debruijn_merkle(ta) != debruijn_merkle(tb)
assert debruijn_merkle(("eq", ("var", "a"), ("var", "b"))) == debruijn_merkle(("eq", ("var", "b"), ("var", "a")))

pre_cls = {1: {1, 2}, 2: {-1, 3}, 3: {-2, 3}, 4: {-3, 4}, 5: {-4, 5}, 6: {-5}}
steps = [(7, {2, 3}, [1, 2]), (8, {3}, [7, 3]), (9, {4}, [8, 4]), (10, {5}, [9, 5]), (11, set(), [10, 6])]
post_cls = {1: {10, 11}, 2: {-10, 12}, 3: {-11, 12}, 4: {1, 2}, 5: {-1, 3}, 6: {-2, 3}, 7: {-3, 4}, 8: {-4, 6}, 9: {-6}}
ch = lambda c: hashlib.sha256((",".join(map(str, sorted(c)))).encode()).hexdigest()[:16]
id_map = {i: ch(c) for i, c in pre_cls.items()}
dag_cache = {ch(c): tuple(id_map.setdefault(sid, ch(c)) and id_map[h] for h in hs) for sid, c, hs in steps}
pos_hits = sum(1 for _, _, hs in steps if all(post_cls.get(h) == pre_cls.get(h) for h in hs if h in pre_cls))
avail, merkle_hits = {ch(c) for c in post_cls.values()}, 0
for _, c, _ in steps:
    if all(p in avail for p in dag_cache[ch(c)]): avail.add(ch(c)); merkle_hits += 1
assert pos_hits == 0 and merkle_hits == 3

edges, pi = [(1, 2, 16), (2, 1, 0)], {0: 0, 1: 0, 2: 16}
assert all(pi[u] + w - pi[v] >= 0 for u, v, w in edges)
assert not (((1 << 64) - 1) - (((1 << 64) - 1 + 1) & ((1 << 64) - 1)) <= 0)
print("REVALIDATION_OK")
PY
```

**Upstream Drift Watchpoints:** Check `carcara/src/{ast/node.rs,slice.rs}` for `ProofNode` pooling or nested `lia_generic` slicing, `FStarC.SMTEncoding.Solver.Cache.fst` for pruned-context hashing replacing `(g, q)`, `verus/source/rust_verify/src/buckets.rs` for function-level default buckets, and `lean4/src/Lean/Language/Lean.lean` for parser high-water-mark invalidation.
