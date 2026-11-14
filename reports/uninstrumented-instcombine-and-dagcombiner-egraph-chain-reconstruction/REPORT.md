# Uninstrumented `InstCombine` and `DAGCombiner` E-Graph Chain Reconstruction via Bidirectional Meet-in-the-Middle Search

## Summary

In LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) bundled with `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `InstCombinerImpl` (`llvm/lib/Transforms/InstCombine/*.cpp`, `~1,200` algebraic, bitwise, and `ICmp` visit rules) and `DAGCombiner` (`llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp`) emit **zero YAML optimization remarks**, leaving a residual runtime and code-size gap in oracle-guided `MiniSSA`/`MiniMach` replay when expression rewrites exceed fixed depth-3 lookup tables (`untrusted-llvm-optimization-oracle-and-certificate-replay-architecture`, `llvm-oracle-guided-minissa-minimach-replay-prototype-and-parity`). Designing, implementing, and mechanizing **`ExprChainSynthesizer`** (`support/extract_ic_dag_cones.py`, `support/expr_chain_synthesizer.py`, `support/lean/ExprChainReconstruction.lean`) establishes:

1. **Sub-Millisecond Bidirectional Meet-in-the-Middle Reconstruction Across 500 `InstCombine` and `DAGCombiner` Cones (`support/ic_dag_500_cones.json`, `support/parity_gap_closure_results.json`):**
   - Partitioning pre-pass and post-pass SSA blocks into side-effect-free expression DAGs (**cones**) rooted at observable boundaries (stores, branch conditions, `SwitchInt` discriminants, call arguments, return values, and $\phi$-inputs) and anchored at shared leaf inputs (parameters, alias-epoch memory loads, and dominating $\phi$-nodes) yields cones of depth $d \in [2, 7]$, AST node count $|V| \in [5, 19]$, and leaf arity $|L| \in [1, 4]$.
   - Whereas naive forward associative-commutative (`AC`) equality saturation expands a mean of **`1,254.0` e-nodes** per cone before hitting distributive blowup, **bidirectional meet-in-the-middle saturation** ($k_f \le 3$ forward epochs from $e_{\text{pre}}$ intersected with $k_b \le 2$ backward canonicalization epochs from $e_{\text{post}}$ under `KnownBits64` + interval leaf assumptions) explores a mean of only **`55.5` e-nodes** (**`22.61x` e-node reduction**).
   - A compact library $\mathcal{R}_{\text{IC}}$ of **`168` parameterized axiom schemas** reconstructs **`494 / 500` (`98.80%`)** of cones directly into `Tier 1` (`Pure AEGraphCert`, `154` cones) and `Tier 2` (`AEGraphCert + BitDomainCert`, `340` cones), while the remaining **`6 / 500` (`1.20%`)** target-specific `DAGCombiner` bit-twiddling cones are closed by `Tier 3` (`BvDecideConeCert` over $\le 4$ leaf variables), achieving **`100.0%` (`500 / 500`)** verified coverage at **`0.2733 ms` median** (`0.4024 ms` p99) synthesis latency with **zero C++ edits to LLVM 23.1.1**.
2. **Zero-`sorry`, Zero-`native_decide` Lean `v4.34.1` Mechanization of Multi-Step `ConeChainCert` and `freeze` Bidirectional Guards (`support/lean/ExprChainReconstruction.lean`):**
   - Elaborating in **`2.26 s`** (`564.2 MB` peak RSS) under `anneal-lean-run` with axiom footprint `[propext, Quot.sound]`, `ExprChainReconstruction.lean` proves `checkConditionalStep_sound` and `checkConeChainCert_sound`.
   - The mechanization formalizes a subtle semantic distinction required for sound bidirectional search: **operand-erasing identities** (`e - e -> 0`, `e ^ e -> 0`, and `e & 0 -> 0`) are strictly **one-way poison refinements** (`e & 0 ⊑_poison 0`, because `.poison & 0 = .poison ≠ .val 0`), whereas variable-preserving identities (`e + 0 = e`, `e | 0 = e`, `e ^ 0 = e`, `e * 1 = e`, `a + b = b + a`, `e << 0 = e`, and `KnownBits`-guarded `addWrap -> addNuw` / `addWrap -> bitOr` on non-poison bounded leaves) are **bidirectional equalities** (`isBidirectionalStep = true`, proven in `bidirectionalStep_eq_sound`). Crossing inside a `.freeze d` node or backward search epoch strictly requires `isBidirectionalStep = true` (`canary_one_way_poison_under_freeze_rejected`).
3. **Closure of the Residual Scalar/Bitwise Parity Gap (`support/parity_gap_closure_results.json`):**
   - Replacing the fixed depth-3 `ConeCert` lookup table in `llvm-oracle-guided-minissa-minimach-replay-prototype-and-parity` with `ExprChainSynthesizer` raises geometric-mean speedup across `w5_o3_corpus.rs` and `full_mir_bench.rs` from **`11.53x` to `11.70x`** vs. stock LLVM `-O3` (`11.71x`), closing **`94.4%`** of the residual runtime gap (reducing the gap from `1.54%` to `0.09%`) while shrinking the `i686` `.text` size delta from `+174 B` to **`+12 B`** and eliminating the `aarch64` `.text` delta (`+12 B` $\rightarrow$ **`0 B`**).

## Applicability

- **Extends:** `untrusted-llvm-optimization-oracle-and-certificate-replay-architecture`, `llvm-oracle-guided-minissa-minimach-replay-prototype-and-parity`, `unified-farkas-knownbits-and-aegraph-side-condition-certificates`
- **Subjects and Scope:** Evaluated on Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `joshlf/anneal` (`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`).

## Findings

### 1. Structural Cone Extraction and 10-Family Distribution Across 500 `InstCombine` and `DAGCombiner` Rewrites

**Basis: source + execution (`support/extract_ic_dag_cones.py`, `support/ic_dag_500_cones.json`)**

Given a pre-pass SSA basic block $B_{\text{pre}}$ and post-pass SSA basic block $B_{\text{post}}$ captured via LLVM Channel B (`-print-before=instcombine -print-after=instcombine`) or between `MiniSSA` and post-`InstCombine` LLVM IR, `extract_diff_cones` slices each basic block at side-effecting and control-flow boundaries (stores, call arguments, branch/switch conditions, return values, and outgoing $\phi$-operands) and traces backward through pure arithmetic, bitwise, shift, cast, and `select` nodes until reaching shared leaf anchors (function parameters, memory loads at fixed `MemorySSA` alias epochs, and dominating $\phi$-nodes). Table 1 summarizes the 500 extracted expression-cone pairs across the 10 rewrite families:

| Family ID | Upstream LLVM 23.1.1 Pass Origin | Cones | Bidirectional (`=`) vs. Directed (`⊑_poison`) | Requires `KnownBits64` / Interval | Certificate Tier Emitted | Representative Rewrite Pattern |
| :--- | :--- | ---: | :--- | :---: | :--- | :--- |
| `F01_demorgan_bitwise` | `InstCombineAndOrXor.cpp` | `68` | Bidirectional (`=`) | No | `Tier 1` (`AEGraphCert`) | `(~x) & (~y) -> ~(x \| y)` |
| `F02_disjoint_add_to_or` | `InstCombineAddSub.cpp::visitAdd` | `74` | Bidirectional (`=`) | Yes | `Tier 2` (`AEGraph + BitDomain`) | `(x & 0xFF00) + (y & 0x00FF) -> or disjoint` |
| `F03_shift_mask_composition` | `InstCombineShifts.cpp` + `DAGCombiner` | `66` | Bidirectional (`=`) | Yes | `Tier 2` (`AEGraph + BitDomain`) | `((x << c1) & mask) >> c2 -> (x << (c1-c2)) & (mask >> c2)` |
| `F04_nuw_nsw_knownbits_sharpening` | `InstCombineAddSub.cpp::willNotOverflow` | `62` | Bidirectional (`=`) | Yes | `Tier 2` (`AEGraph + BitDomain`) | `add (x & 255), c -> add nuw nsw (x & 255), c` |
| `F05_operand_erasing_poison_refinement` | `InstructionSimplify.cpp` | `52` | **Directed (`⊑_poison`)** | No | `Tier 1` (`AEGraphCert`) | `(x - x) + (y ^ y) -> 0`, `x & 0 -> 0` |
| `F06_icmp_canonicalization_and_range` | `InstCombineCompares.cpp` | `54` | Bidirectional (`=`) | Yes | `Tier 2` (`AEGraph + BitDomain`) | `icmp ult (x & 63), 64 -> true` |
| `F07_select_absorption_and_freeze` | `InstCombineSelect.cpp` | `44` | **Directed (`⊑_poison`)** | Yes | `Tier 2` (`AEGraph + BitDomain`) | `select cond, (x \| 1), x -> x \| zext(cond)` |
| `F08_bitfield_insert_and_bswap` | `InstCombine` + `DAGCombiner::MatchBSwap` | `38` | Bidirectional (`=`) | Yes | `Tier 2` (`AEGraph + BitDomain`) | `(base & ~m) \| ((v << s) & m)`, `bswap` tree |
| `F09_pow2_udiv_urem_strength_reduce` | `InstCombineMulDivRem.cpp` | `34` | Bidirectional (`=`) | No | `Tier 1` (`AEGraphCert`) | `(x / 2^k) + (x % 2^m) -> (x >> k) + (x & (2^m-1))` |
| `F10_dagcombiner_rotate_and_target_bithacks` | `DAGCombiner.cpp::MatchRotate` | `8` | Bidirectional (`=`) | Yes | `2` `Tier 2` + `6` `Tier 3` (`BvDecide`) | `(x << (r & 31)) \| (x >> ((32-r) & 31)) -> @llvm.fshl` |
| **Total (`ic_dag_500_cones.json`)** | — | **`500`** | **`404` Bi / `96` Dir** | **`346` Yes / `154` No** | **`154` T1 / `340` T2 / `6` T3** | **`98.80%` $\mathcal{R}_{\text{IC}}$ schema + `1.20%` `BvDecide` = `100.0%`** |

---

### 2. Bidirectional Meet-in-the-Middle Search vs. Naive Forward Equality Saturation

**Basis: source + execution (`support/expr_chain_synthesizer.py`, `support/lean/ExprChainReconstruction.lean`)**

1. **Why Bidirectional Meet-in-the-Middle Prevents AC Explosion (`22.61x` Fewer E-Nodes):**
   - Unconstrained forward equality saturation from $e_{\text{pre}}$ under associative-commutative (`AC`) rules for `add`, `mul`, `and`, `or`, and `xor` coupled with distributive and `KnownBits`-conditional rules generates $O(2^d \cdot |V|)$ e-nodes (`mean = 1,254.0` e-nodes/cone).
   - `ExprChainSynthesizer` instead runs at most $k_f \le 3$ forward expansion epochs from $e_{\text{pre}}$ and $k_b \le 2$ backward canonicalization epochs from $e_{\text{post}}$ (`mean = 55.5` e-nodes/cone), intersecting frontier e-classes in **`0.2733 ms` median** (`0.4024 ms` p99).
2. **One-Way Poison Refinement vs. Bidirectional Equality Inside `freeze` (`isBidirectionalStep`):**
   - Forward steps outside `freeze` may apply directed poison-erasing rules (`subSelfToZero : e - e ⊑_poison 0`, `bitAndZeroRight : e & 0 ⊑_poison 0`, `bitXorSelfToZero : e ^ e ⊑_poison 0`, `dropNuwToWrap : addNuw a b ⊑_poison addWrap a b`, `insertFreeze : e ⊑_poison freeze d e`).
   - Crucially, `e & 0 -> 0` is **not** a bidirectional equality over `PoisonOr Int`: when `e = .poison`, `evalDAGExpr (.bitAnd e (.const 0)) = .poison`, whereas `evalDAGExpr (.const 0) = .val 0`. Consequently, rewriting `freeze 42 (e & 0)` or `freeze 42 (e - e)` to `freeze 42 0` would transform `.val 42` into `.val 0` when `e = .poison`!
   - In `support/lean/ExprChainReconstruction.lean`, `checkStepSideCond` gates `.congFreeze d c` on `isBidirectionalStep c = true`, and `bidirectionalStep_eq_sound` proves that every step with `isBidirectionalStep c = true` satisfies strict equality `evalDAGExpr env letVal src = evalDAGExpr env letVal tgt`.
3. **Three-Tier Checking Latency and Parity Gap Closure:**

| Metric | `U2` Fixed Depth-3 `ConeCert` Baseline | `ExprChainSynthesizer` (`Tier 1 + Tier 2 + Tier 3`) | Improvement / Delta |
| :--- | ---: | ---: | :--- |
| **Unremarked `InstCombine`/`DAGCombiner` Cones Verified** | `312 / 500` (`62.40%`) | **`500 / 500` (`100.00%`)** | **`+37.60%` cone coverage** |
| **Synthesis Latency (Median / p99 per Cone)** | N/A (static table) | **`0.2733 ms` / `0.4024 ms`** | `< 1 ms` budget met (`3.66x` headroom) |
| **Native Checker Latency (`Tier 1` / `Tier 2` / `Tier 3`)** | `0.038 µs` | **`0.042 µs` / `0.068 µs` / `4.12 µs`** | Sub-microsecond on `98.8%` of cones |
| **Geomean Runtime Speedup (`w5_o3_corpus` + `full_mir_bench`)** | `11.53x` (`1.54%` gap vs. `-O3`) | **`11.70x` (`0.09%` gap vs. `-O3` `11.71x`)** | **`94.4%` of residual `-O3` gap closed** |
| **Cross-Target `.text` Gap vs. Native `-O3` (`i686` / `aarch64`)** | `+174 B` / `+12 B` | **`+12 B` / `0 B`** | **`93.1%` (`i686`) & `100%` (`aarch64`) closed** |

## Boundaries

- **Loop-Carried Multi-Block Recurrences (`IndVarSimplify` / `LoopStrengthReduce`):** `ExprChainSynthesizer` operates on acyclic intra-block expression cones anchored at shared dominating $\phi$-nodes and `MemorySSA` loads. Rewrites that alter loop-header induction variable stride across iterations require `HybridTrace` SCEV recurrence certificates rather than intra-block cone chains.
- **Floating-Point Fast-Math Cones:** `ExprChainReconstruction.lean` models integer and bitwise `PoisonOr Int` cones; floating-point `reassoc` and `contract` rewrites are governed by `OrderedSimdFoldCert` and `FloatReassocCert` in `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`.

## Evidence

- **Extractor, Synthesizer, and Datasets (`support/`):**
  - `support/extract_ic_dag_cones.py` and `support/ic_dag_500_cones.json`: 500 pre/post `InstCombine` and `DAGCombiner` cones across 10 rewrite families.
  - `support/expr_chain_synthesizer.py` and `support/parity_gap_closure_results.json`: Bidirectional AE-graph + `KnownBits` reconstructor, e-node reduction metrics, and parity gap closure measurements.
- **Lean `v4.34.1` Mechanization (`support/lean/`):**
  - `support/lean/ExprChainReconstruction.lean` and `support/lean/lakefile.lean`: Zero-`sorry`, zero-`native_decide` mechanization of `bidirectionalStep_eq_sound`, `checkConditionalStep_sound`, `checkConeChainCert_sound`, `canary_one_way_poison_under_freeze_rejected`, and `canary_unsound_shift_mask_without_knownbits_rejected`.

## Revalidation

Run the cone extractor, bidirectional synthesizer, and Lean `v4.34.1` kernel check from the package directory:

```bash
python3 support/extract_ic_dag_cones.py
python3 support/expr_chain_synthesizer.py
anneal-lean-run --mode file --concurrency 4 -- lean support/lean/ExprChainReconstruction.lean
```

Confirm exit code `0`, `ric_schema_coverage_pct >= 98.0`, `median_synthesis_latency_ms < 1.0`, and axioms limited to `[propext, Quot.sound]`.
