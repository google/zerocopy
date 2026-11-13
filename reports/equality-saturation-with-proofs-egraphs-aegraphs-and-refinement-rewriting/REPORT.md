# Equality Saturation with Proofs: E-Graphs, Acyclic E-Graphs, and Directed Refinement Rewriting

## Summary

Equality saturation can serve as a high-throughput untrusted optimization and
instruction-selection oracle for a proof-producing compiler, **provided its
architecture respects three hard constraints** established by our empirical
`egg 0.11.0` benchmark (`support/egg_proof_bench.rs`,
`support/egg_proof_metrics.json`) and our standalone Lean `v4.34.1`
mechanization (`support/EGraphRefinementProofs.lean`):

1. **Symmetric E-Classes Are Unsound for Poison-Erasing Refinements
   (`symmetric_eclass_poison_unsound`):**
   In an IR with deferred undefined behavior (`PoisonOr (BitVec 64)`), rules
   that erase a potentially poisoned operand—such as $x \times 0 \sqsubseteq 0$,
   $x \ \& \ 0 \sqsubseteq 0$, $x - x \sqsubseteq 0$, or `select c v v` $\sqsubseteq v$—are
   **strictly directional refinements (`⊑`), not symmetric equalities**. Merging
   `mulZero x` and `const 0` into a symmetric e-class (`SymmEGraphEq`) allows the
   backward orientation `0 -> poison * 0` to rewrite a defined constant `0` into
   `.poison` (`symmetric_eclass_poison_unsound`).
2. **Sound Two-Stratum Decomposition (`BiEqRule` vs. `DirRefineRule`):**
   A proof-producing e-graph optimizer must partition rules into:
   - **Stratum A (`BiEqRule`, Poison-Exact Bidirectional Equalities):** Rules
     where both sides have identical poison footprints ($\llbracket \text{lhs} \rrbracket = \llbracket \text{rhs} \rrbracket$
     on `PoisonOr (BitVec 64)`, e.g., $x + 0 \leftrightarrow x$,
     $x \times 4 \leftrightarrow x \ll 2$, `(x << 2) + y <-> sh2add x y`,
     `x & ~y <-> andn x y`, commutativity/associativity). Only `BiEqRule`
     rewrites may union e-classes symmetrically.
   - **Stratum B (`DirRefineRule`, Directed Poison-Monotonic Refinements):**
     Rules where $\llbracket \text{lhs} \rrbracket \sqsubseteq \llbracket \text{rhs} \rrbracket$
     ($x \times 0 \to 0$, $x - x \to 0$). These are represented either as
     directed edges `(eclass_src -> eclass_dst)` in a colored/relational e-graph
     (`egglog`) or applied along a forward-only post-extraction spine, and
     verified by the Lean 4 certificate checker `checkDirectedRefinementTrace`
     (`checkDirectedRefinementTrace_sound`).
3. **Mandatory DAG-Shared `TreeExplanation` Certificates and Bounded Acyclic
   Saturation (`aegraphs`):**
   - **Proof Size:** When a sub-DAG is shared across $d$ levels (`dup`), unshared
     tree explanations (`FlatExplanation`) grow as $2^{d+3}-1$ steps, reaching
     **`319` steps (`289,986` bytes)** at depth `6` versus **`10` steps (`2,537`
     bytes, a `114.3x` reduction)** for `let`-shared `TreeExplanation` DAGs.
     Furthermore, Flatt et al.'s (FMCAD 2022) greedy proof-size shortcutting in
     `egg 0.11.0` (`without_explanation_length_optimization` vs. default) reduces
     congruence-chain DAG steps by **`4.0x` (`8` $\to$ `2` DAG steps, `16` $\to$
     `4` flat steps)**.
   - **Compile-Time Scaling:** Full AC (associativity + commutativity) saturation
     on a $k$-term sum blows up from `15` e-classes / `63` e-nodes (`123 us`) at
     $k=4$ to **`202` e-classes / `2,627` e-nodes (`3,593 us`)** at $k=7$. For
     whole-function compilation, **Cranelift-style acyclic e-graphs (`aegraphs`
     in `cranelift-codegen/src/egraph/`)** with bounded union-node fanout (`k=4..5`)
     and non-AC canonicalization achieve $O(N)$ pass scaling (`37–83 us`
     saturation, `50–109 us` proof extraction per expression) while emitting
     certificates that Lean 4 checks by `rfl` in `<1 ms`.

## Applicability

This report extends `isle-aegraphs-btl-symbolic-execution-and-dst-vtable-lowering-2026`
with quantitative proof-generation benchmarks on `egg 0.11.0` (compiled with
Rust `1.99.1`, `58cf8f9c35b355199727627d07ae34a4e2846d67`) and a standalone
Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) proof checker
(`support/EGraphRefinementProofs.lean`).

## Findings

### 1. Comparing `egg`, `egglog`, `lean-egg`, and Cranelift Acyclic E-Graphs (`aegraphs`)

Basis: source + documentation + execution (`support/egg_proof_metrics.json`).

| Engine | Core Data Structure | Proof / Explanation Generation | Cost Model & Extraction | Scaling on Real Compiler IR |
| :--- | :--- | :--- | :--- | :--- |
| **`egg` (`0.11.0`)** (Willsey et al. POPL 21; Flatt et al. FMCAD 22) | Mutable hash-consed e-graph with deferred `rebuild()` invariant restoration | Built-in `Runner::with_explanations_enabled()`; emits `TreeExplanation` (`let`-shared DAG) and `FlatExplanation` with FMCAD 22 greedy proof-size minimization | Bottom-up `Extractor` (`AstSize`, `AstDepth`, or custom `CostFunction`); cycles broken by monotonically non-decreasing node costs | Fast on basic-block expression trees (`37–88 us` without AC); degrades super-exponentially under unrestricted AC rules (`2,627` e-nodes at $k=7$) |
| **`egglog`** (Zhang et al. PLDI 23, `egraphs-good/egglog`) | Relational Datalog DB with congruence closure (`function` tables + `union` action) | Term-DAG provenance tracking (`explain` reconstructs rule derivations over Datalog tuples) | Weighted tree/DAG extraction over term tables | Handles relational context (dominance, type tables, directed `Refines(a, b)` relations) natively alongside equality classes |
| **Cranelift `aegraphs`** (`wasmtime` @ `87282b8f`, `cranelift/codegen/src/egraph/`) | **Scoped Acyclic E-Graph** embedded directly in CLIF `DataFlowGraph` via binary `Union(v1, v2)` nodes (capped at depth/fanout `5`) | No proof object emitted natively, but every `Union(v_old, v_new)` node is created immediately by an ISLE rule application `v_old -> v_new`, forming a direct $O(1)$-recoverable trace | Single-pass `elaborate.rs`: computes pure cost (`Cost::pure_op_cost`) bottom-up, selects lowest-cost branch of each `Union`, and schedules via LICM/rematerialization | **Production-grade $O(N)$ scaling**: runs in a single GVN + ISLE pass with no fixpoint rebuild loop and zero cyclic extraction hazards |
| **`lean-egg`** (`marcusrossel/lean-egg`) | Rust `egg` FFI backend called from Lean 4 `MetaM` tactic (`egg [...]`) | Parses `egg` `FlatExplanation` back into a chain of Lean `Eq.trans` / `congrArg` / `rw` proof steps | Uses `egg` `AstSize` to extract shortest intermediate rewrite chain | Effective for interactive algebraic goals ($\le 15$ steps), but reconstructing `Eq.trans`/`congrArg` terms in `MetaM` is too slow for thousands of IR blocks compared to reflected `checkDirectedRefinementTrace` |

### 2. Quantitative Proof-Generation and Extraction Benchmarks (`egg 0.11.0`)

Basis: execution of `support/egg_proof_bench.rs` on `x86_64-unknown-linux-gnu`
(Rust `1.99.1`), preserved in `support/egg_proof_metrics.json`.

#### 2.1 Compiler Expression Optimization & Proof Extraction Latency

| Benchmark Expression | AC Rules? | E-Classes / E-Nodes | Iters | Cost (`Start -> Best`) | Extracted Optimal Target Expression | DAG `let` Steps (Opt / Unopt) | Saturation Latency | Extraction Latency | Proof Explain Latency |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`dst_slice_addr`** (`base + ((hdr + (align-1)) & ~(align-1)) + idx*4`) | No | `15` / `18` | `2` | `16 -> 15` | `(+ (+ base (& (+ hdr (- align 1)) (- 0 align))) (* idx 4))` | `1` / `1` | `37 us` | `9 us` | `50 us` |
| **`dst_slice_addr`** (`Zba` `sh2add` + mask) | Yes | `17` / `34` | `4` | `16 -> 13` | `(+ base (sh2add idx (& (+ hdr (- align 1)) (- 0 align))))` | `5` / `5` | `88 us` | `6 us` | `102 us` |
| **`nested_zba_zbb`** (`((x & ~(m1 | m2)) * 8) + ((y * 4) + z)`) | No | `19` / `28` | `3` | `17 -> 9` | `(sh3add (andn x (\| m1 m2)) (sh2add y z))` | `7` / `7` | `40 us` | `5 us` | `77 us` |
| **`nested_zba_zbb`** | Yes | `21` / `69` | `5` | `17 -> 9` | `(sh2add y (sh3add (andn x (\| m1 m2)) z))` | `10` / `10` | `282 us` | `7 us` | `354 us` |
| **`deep_chain_8`** (cascaded `sh1add`/`sh2add`/`sh3add`) | No | `18` / `28` | `3` | `19 -> 9` | `(* (sh3add (sh2add (sh1add a b) c) d) 2)` | `8` / `8` | `44 us` | `5 us` | `109 us` |
| **`shared_dag_depth4`** (`dup^4((x & ~m1) << 2)`) | No | `13` / `24` | `4` | `14 -> 9` | `(dup (dup (dup (dup (* (andn x m1) 4)))))` | `3` / `3` | `45 us` | `5 us` | `83 us` |

#### 2.2 Exponential Blowup of Unshared `FlatExplanation` vs. Linear `TreeExplanation` (`let`-DAG)

When a common subexpression `(and x (not m1))` is rewritten to `(andn x m1)` at
the leaf of a $d$-deep binary DAG (`(dup e) := (+ e e)`), `TreeExplanation`
binds the sub-proof once via a `(let ...)` binding, whereas `FlatExplanation`
duplicates the subterm rewrite across every syntactic occurrence:

| Shared DAG Depth $d$ | `TreeExplanation` (`let`-DAG) Steps | `FlatExplanation` (Unshared) Steps | `TreeExplanation` S-Exp Bytes | `FlatExplanation` S-Exp Bytes | Byte Blowup Ratio (`Flat / DAG`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `1` | `5` | `9` | `628 B` | `693 B` | `1.10x` |
| `2` | `6` | `19` | `921 B` | `2,240 B` | `2.43x` |
| `3` | `7` | `39` | `1,262 B` | `7,198 B` | `5.70x` |
| `4` | `8` | `79` | `1,645 B` | `23,722 B` | `14.42x` |
| `5` | `9` | `159` | `2,070 B` | `81,266 B` | `39.26x` |
| **`6`** | **`10`** | **`319`** | **`2,537 B`** | **`289,986 B`** | **`114.30x`** |

#### 2.3 FMCAD 2022 Greedy Proof-Length Shortcutting & AC Saturation Blowup

- **Congruence Shortcutting (`flatt_fmcad2022_shortcut_demo`):** When an e-class
  can be reached either via an 8-step deep congruence chain or a 2-step direct
  shortcut rule, `egg`'s default FMCAD 2022 proof-size optimizer selects the
  **`2`-step DAG proof (`4` flat steps)** instead of the unoptimized **`8`-step
  DAG proof (`16` flat steps)** (`4.0x` reduction).
- **AC Combinatorial Blowup (`ac_scaling`):** Saturating $a_1 + a_2 + \dots + a_k$
  under unrestricted associativity and commutativity produces $2^{k}-1$
  e-classes:
  - $k=2$: `3` e-classes, `4` e-nodes, `27 us`;
  - $k=4$: `15` e-classes, `63` e-nodes, `123 us`;
  - $k=6$: `63` e-classes, `900` e-nodes, `2,222 us`;
  - $k=7$: **`202` e-classes, `2,627` e-nodes, `3,593 us`**.
  Consequently, a compiler e-graph pass should **never enable unrestricted AC
  rules during general saturation**; instead, flatten associative chains into
  sorted $n$-ary canonical forms before running non-AC pattern rules.

### 3. Rewriting by Refinement Rather Than Equality in the Presence of Poison (`EGraphRefinementProofs.lean`)

Basis: source + execution (`support/EGraphRefinementProofs.lean`, lines 28–395).

#### 3.1 Formal Proof that Symmetric E-Classes Are Unsound for Poison-Erasing Rules

In `support/EGraphRefinementProofs.lean` (lines 39–60), directional refinement on
`PoisonOr α` is defined by:

```lean
def Refines {α : Type} (src tgt : PoisonOr α) : Prop :=
  match src, tgt with
  | .poison, _ => True
  | .value v1, .value v2 => v1 = v2
  | .value _, .poison => False
```

For `mulZero x` ($x \times 0$), `(Expr.mulZero x).eval env ⊑ (Expr.const 0#64).eval env`
holds for all `env` (`mul_zero_refines_const_zero`, lines 125–130), because when
`x` evaluates to `.poison`, `.poison ⊑ .value 0#64` holds. However, if an
e-graph merges `mulZero x` and `const 0#64` into a symmetric e-class
(`SymmEGraphEq`), symmetry relates `const 0#64` to `mulZero .poison`, which
evaluates to `.poison`:

```lean
theorem symmetric_eclass_poison_unsound :
    ∃ (src tgt : Expr) (env : Env),
      SymmEGraphEq src tgt ∧
      src.eval env = .value 0#64 ∧
      tgt.eval env = .poison ∧
      ¬ (src.eval env ⊑ tgt.eval env)
```

#### 3.2 Sound Two-Stratum Rule Separation and Reflected Certificate Checker

To combine equality saturation with sound poison refinement, we partition the
rewrite rule catalog into two types (`support/EGraphRefinementProofs.lean`,
lines 161–251):

1. **`BiEqRule` (Bidirectional Poison-Exact Equalities):**
   `addZero` ($x + 0 \leftrightarrow x$), `mulFourShl` ($x \times 4 \leftrightarrow x \ll 2$),
   `sh2addFuse` ($(x \ll 2) + y \leftrightarrow \text{sh2add}(x, y)$),
   `andnFuse` ($x \ \& \ \sim y \leftrightarrow \text{andn}(x, y)$), and
   `addComm` ($x + y \leftrightarrow y + x$). Every `BiEqRule` preserves exact
   equality on `PoisonOr (BitVec 64)` (`applyBiEqForward_eq : e.eval env = e'.eval env`),
   so both forward (`.biFwd r`) and backward (`.biBwd r cand`) applications are
   sound inside symmetric e-classes.
2. **`DirRefineRule` (Forward-Only Poison-Monotonic Refinements):**
   `mulZero` ($x \times 0 \to 0$) and `subSelf` ($x - x \to 0$). These rules satisfy
   `applyDirRefine_refines : e.eval env ⊑ e'.eval env` and may only be applied in
   the forward direction (`.dirRef r`).

Because every operator in `Expr` is monotonic with respect to `⊑` (`map1_mono`,
`map2_mono`), applying any `CertAction` (`biFwd`, `biBwd`, or `dirRef`) at any
subterm path `p : List Dir` preserves directional refinement (`applyAtPath_refines`,
lines 324–338). This yields a linear-time boolean certificate checker
`checkDirectedRefinementTrace` verified by `checkDirectedRefinementTrace_sound`
(lines 339–362):

```lean
theorem checkDirectedRefinementTrace_sound (src : Expr) (trace : List DirectedRewriteStep) (dst : Expr)
    (h : checkDirectedRefinementTrace src trace dst = true) (env : Env) :
    src.eval env ⊑ dst.eval env
```

Using this theorem, Lean 4 kernel-checks the 4-step `Zba`/`Zbb` instruction
selection certificate `sampleTrace_verified` (lowering
`((v0 & ~v1) * 4) + (v2 + 0)` to `sh2add (andn v0 v1) v2`) via a single `rfl`
reduction using only `[propext, Quot.sound]`.

## Boundaries

- **Side-Effecting Memory and Control-Flow Operations:** Pure e-graphs and
  acyclic e-graphs (`aegraphs`) apply directly to pure, trap-free SSA expression
  trees (`PoisonOr (BitVec w)`). Operations that read/write memory or may trap
  (such as hardware division by zero on x86-64) must either be pinned outside the
  e-class union set (as Cranelift's `egraph` pass does via `has_side_effect` /
  `MemFlags` in `cranelift/codegen/src/egraph/mod.rs`) or carry explicit state/effect
  tokens (`Lean-MLIR` `EffectKind`).
- **Loop-Level Equality Saturation (`Peggy` $\theta$-Nodes):** While Peggy (POPL
  2009) embeds loop recurrences into cyclic PEGs via $\theta/\text{eval}/\text{pass}$
  operators, extracting sequential CFG code from a cyclic PEG requires solving an
  NP-hard ILP (`1.2–6.0 s` per method) and reconstructing cross-loop bisimulation
  invariants. Equality saturation in a fast verified Rust compiler should
  therefore be scoped to **Cranelift-style acyclic e-graphs over intra-block /
  dominator-scoped pure SSA expressions**, leaving loop transformations to
  dedicated pass certificates (Section 4 of `relational-logics-simulation-techniques-and-completeness-for-compiler-derivations`).

## Evidence

- **Standalone Lean 4.34.1 Mechanization:**
  `support/EGraphRefinementProofs.lean` (`395` lines, zero `sorry`, verified on
  Lean `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52` with `#guard_msgs in #print axioms`
  confirming `[propext, Quot.sound]` only) proves:
  - `refines_refl`, `refines_trans`, `refines_not_symm`, `map1_mono`, `map2_mono`
    (lines 47–82),
  - `mul_zero_refines_const_zero`, `mul_zero_not_symmetric_eq`, and
    `symmetric_eclass_poison_unsound` (lines 125–156),
  - `applyBiEqForward_eq` and `applyDirRefine_refines` (lines 195–251),
  - `applyAtPath_refines`, `checkDirectedRefinementTrace_sound`, and
    `sampleTrace_verified` (lines 324–382).
- **`egg 0.11.0` Quantitative Benchmark Suite:**
  - `support/egg_proof_bench.rs` (`275` lines of Rust) and
    `support/egg_proof_metrics.json` record exact e-class/e-node counts,
    iteration counts, saturation/extraction/explanation microsecond latencies,
    FMCAD 2022 proof-length shortcutting ratios, and shared-DAG `let` vs. flat
    explanation byte sizes across depths `1..6`.
- **Primary Upstream Sources:**
  - `bytecodealliance/wasmtime` at `87282b8fd77fa9fbba6caadb0be690bedec2dc64`
    (`cranelift/codegen/src/egraph/{mod.rs,cost.rs,elaborate.rs}`).
  - `egraphs-good/egg` (`v0.11.0`, Willsey et al., POPL 2021
    `doi:10.1145/3434304`; Flatt et al., FMCAD 2022
    `doi:10.34727/2022/isbn.978-3-85448-053-2_13`).
  - `egraphs-good/egglog` (Zhang et al., PLDI 2023 `doi:10.1145/3591239`).

## Revalidation

To re-verify the Lean `v4.34.1` refinement and certificate-soundness proofs:

```bash
anneal-lean-run --mode file --concurrency 4 -- \
  lake env lean reports/equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting/support/EGraphRefinementProofs.lean
```

To inspect the preserved `egg 0.11.0` proof-generation metrics:

```bash
python3 -m json.tool reports/equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting/support/egg_proof_metrics.json
```
