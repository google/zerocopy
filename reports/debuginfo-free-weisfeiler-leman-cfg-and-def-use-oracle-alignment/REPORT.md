# Debuginfo-Free Weisfeiler-Leman Dominator-Tree and Def-Use Oracle Alignment (`WLAnchorKey`)

## Summary

The 3-level `AnchorKey` alignment protocol established in `oracle-hint-drift-alignment-and-fallback-resilience` requires `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) to compile untrusted LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) oracle queries with `-C debuginfo=1` (`DebugInfoKind::LineTablesOnly`) so `!dbg` `DILocation` `inlinedAt` chains survive in LLVM IR. When consuming stripped `-C debuginfo=0` bitcode (`0` `!DILocation` and `0` `!DISubprogram` nodes) or aggressive `SimplifyCFG` transformations that drop line-table metadata (`MergedLocation`), `AnchorKey` alignment collapses from `99.13%` to **`9.57%` (`44 / 460` sites)**. Designing, evaluating, and mechanizing **`WLAnchorKey`**—a debuginfo-free $k=4$ Weisfeiler-Leman (WL) color-refinement and multiscale Hungarian matcher over attributed dominator-tree and def-use graphs (`support/wl_oracle_aligner.py`, `support/stripped_drift_benchmark_results.json`, `support/lean/WLOracleAlignment.lean`)—establishes:

1. **`98.04%` Stripped-IR (`-C debuginfo=0`) Site Alignment and `99.33%` Speedup Retention Across the 80-Function Drift Corpus (`support/stripped_drift_benchmark_results.json`):**
   - Across `460` optimization sites (`InlineHint`, `SroaHint`, `LoopOptHint`, `VectorizeHint`, `RegAllocHint`) in the 80-function drift corpus (`D1` Tree Borrows vs. `ScopedNoAliasAA`, `D2` `SimplifyCFG`/switch/freeze drift, `D3` `Mid28` vs. `Full42` MIR pass and slice-bounds drift, and `D4` inlining threshold drift) compiled with `-C opt-level=3 -C debuginfo=0`, `WLAnchorKey` aligns **`451 / 460` (`98.04%` recall, `99.34%` precision, `98.69%` F1)** of sites in **`41.8 µs`** mean graph-refinement time per function:
     - **`405 / 460` (`88.04%`)** align via exact singleton-orbit matching (`uniqueExact`) at radius $r \in \{4, 3, 2, 1\}$;
     - **`16 / 460` (`3.48%`)** align via orbit-symmetric twin-site matching (`symmetricOrbit`);
     - **`30 / 460` (`6.52%`)** align via multiscale Hungarian cosine assignment (`softNeighborhood`) when local drift perturbs a radius-$t \ge 2$ neighbor; and
     - **`9 / 460` (`1.96%`)** gracefully fall back to Tier 1/Tier 2 local heuristics with **`0` unsound hint applications**, retaining **`99.33%`** of native `-O3` runtime speedup without any debuginfo metadata.
2. **`97.33%` Alignment and Zero Unsoundness Across 25 Adversarial Symmetry and Diamond-Collapse Stress Tests:**
   - Across `25` adversarial `-C debuginfo=0` functions (`150` sites) containing isomorphic `(x, y)` twin coordinate loops, macro-duplicated callee arms, and `SimplifyCFG` diamond-to-`select` collapses, canonical DFS parameter-root distance tie-breaking resolves `113 / 150` (`75.33%`) of sites into unique orbits, `OrbitSymmetric` hint broadcast resolves `33 / 150` (`22.00%`), and `3` genuinely asymmetric twin sites are cleanly skipped via `ambiguousOrbitFallback`, yielding **`146 / 150` (`97.33%`)** alignment with **`0` compilation panics and `0` unsound rewrites**.
3. **Zero-`sorry`, Zero-`native_decide` Lean `v4.34.1` Mechanization of `WLAnchorKey` Uniqueness and Replay Soundness (`support/lean/WLOracleAlignment.lean`):**
   - Elaborating in **`0.66 s`** (`502.2 MB` peak RSS) under `anneal-lean-run` with axiom footprint `[propext, Quot.sound]`, `WLOracleAlignment.lean` proves `uniqueOrbit_injective`, `foldl_orbit_sound`, `wl_align_and_replay_sound`, and `canary_twin_loop_non_unique_orbit_detected`.

## Applicability

- **Extends:** `oracle-hint-drift-alignment-and-fallback-resilience`, `untrusted-llvm-optimization-oracle-and-certificate-replay-architecture`, `llvm-oracle-guided-minissa-minimach-replay-prototype-and-parity`
- **Subjects and Scope:** Evaluated on Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `joshlf/anneal` (`d4ca2c861f664f200b69cdced9f6af38b5b1175a`).

## Findings

### 1. Construction of the Attributed Program-Dependence and Dominator-Tree Graph $\mathcal{G}_{\text{WL}}(f)$

**Basis: source + execution (`support/wl_oracle_aligner.py`, `support/lean/WLOracleAlignment.lean`)**

When `-C debuginfo=0` strips all `!DILocation` and `!DISubprogram` metadata from LLVM IR (`dbg0_dilocation_count = 0` vs. `dbg1_dilocation_count = 29` on `stripped_twin_loops`), `WLAnchorKey` constructs a typed multi-graph $\mathcal{G}_{\text{WL}}(f) = (V_{\text{bb}} \cup V_{\text{op}} \cup V_{\text{loop}}, E_{\text{dom}} \cup E_{\text{cfg}} \cup E_{\text{def-use}} \cup E_{\text{loop}})$ over invariants that survive CFG restructuring:

1. **Initial Debuginfo-Free Vertex Colors $c^{(0)}(v)$:**
   - Encodes `(normalized_opcode_class, memory_width_and_volatility, callee_def_path_hash_or_sig_arity, terminator_kind, dom_tree_depth, post_dom_depth, loop_nesting_depth, backedge_count, param_root_min_dist)`.
   - Crucially, `param_root_min_dist` records the shortest def-use path distance from each vertex to each numbered function parameter `(arg_0, arg_1, ...)`, breaking symmetry whenever two syntactically identical loops or call arms operate on distinct parameter slices (`xs: &[u32]` vs. `ys: &[u32]`).
2. **Eight Structural Edge Labels (`EdgeLabel` in `WLOracleAlignment.lean`):**
   - `domChild`, `loopBackedge`, `loopExit`, `trueSucc`, `falseSucc`, `defUseOp(argIdx)`, `memAddr`, and `memVal`.
3. **$k=4$ `SplitMix64` Color Refinement and Multiscale Hungarian Fallback:**
   - For $t \in \{1, 2, 3, 4\}$, each vertex updates its color via:
     $$c^{(t)}(v) = \text{SplitMix64}\bigl(c^{(t-1)}(v) \oplus \text{fold}\{(\ell(v, u), c^{(t-1)}(u)) : (v, u) \in E\}\bigr)$$
   - If a vertex $v \in V_{\text{LLVM}}$ and $v' \in V_{\text{MiniSSA}}$ share a singleton color orbit (`isUniqueOrbit g r v' = true`) at the highest non-drifted radius $r \in \{4, 3, 2, 1\}$, `WLAnchorKey` emits `.uniqueExact r v'`.
   - If $|\text{Orbit}(c^{(4)})| > 1$ (isomorphic twin subgraphs) and the oracle hint is orbit-invariant (`isSymmetricOk = true`, e.g., applying `VectorizeHint(VF=4)` to both twin loops), `WLAnchorKey` emits `.symmetricOrbit orbitNodes`; otherwise it emits `.ambiguousOrbitFallback`.
   - For remaining unmatched vertices where local drift (`D1`–`D4`) perturbed a neighbor at radius $t \ge 2$, a Hungarian assignment over multiscale similarity weights $w(u, v) = \sum_{t=0}^4 2^t \cdot \mathbb{I}[c^{(t)}(u) = c^{(t)}(v)]$ emits `.softNeighborhood v'`.

---

### 2. Stripped-IR (`-C debuginfo=0`) Alignment Accuracy Across Drift Categories `D1`–`D4` and Hint Classes

**Basis: execution (`support/wl_oracle_aligner.py`, `support/stripped_drift_benchmark_results.json`)**

Table 1 compares `WLAnchorKey` under `-C debuginfo=0` against `U3`'s `-C debuginfo=1` `AnchorKey` baseline, `U3` under `-C debuginfo=0` (Level 3 fuzzy signature fallback only), and naive `-C debuginfo=0` ordinal matching across the 80-function (`460`-site) drift corpus:

| Drift Category (`80` Functions, `-C debuginfo=0`) | Total Sites | `U3` (`-C debuginfo=1`) | `U3` Stripped (`-C debuginfo=0`) | Naive Ordinal (`-C debuginfo=0`) | `WLAnchorKey` Exact Singleton | `WLAnchorKey` Symmetric Orbit | `WLAnchorKey` Soft Hungarian | `WLAnchorKey` Total Aligned (%) | `-O3` Speedup Retained (%) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`D1` — Tree Borrows vs. `ScopedNoAliasAA`** | `112` | `100.00%` | `16.96%` (`19`) | `27.68%` (`31`) | `106` | `2` | `3` | **`111 / 112` (`99.11%`)** | **`99.82%`** |
| **`D2` — `SimplifyCFG` Switch & `freeze` Drift** | `104` | `99.04%` | `7.69%` (`8`) | `13.46%` (`14`) | `91` | `4` | `7` | **`102 / 104` (`98.08%`)** | **`99.41%`** |
| **`D3` — `Mid28` vs. `Full42` MIR & Bounds Drift** | `128` | `99.22%` | `4.69%` (`6`) | `9.38%` (`12`) | `110` | `4` | `11` | **`125 / 128` (`97.66%`)** | **`99.15%`** |
| **`D4` — Inlining Threshold & Call-Order Drift** | `116` | `98.28%` | `9.48%` (`11`) | `15.52%` (`18`) | `98` | `6` | `9` | **`113 / 116` (`97.41%`)** | **`98.94%`** |
| **Total / Mean (`80` Functions)** | **`460`** | **`99.13%`** | **`9.57%` (`44`)** | **`16.30%` (`75`)** | **`405` (`88.04%`)** | **`16` (`3.48%`)** | **`30` (`6.52%`)** | **`451 / 460` (`98.04%`)** | **`99.33%`** |

Table 2 breaks down stripped-IR (`-C debuginfo=0`) alignment by `OracleHintV1` optimization site class:

| Optimization Site Class | Total Sites | `U3` Stripped (`-C debuginfo=0`) | Naive Ordinal (`-C debuginfo=0`) | `WLAnchorKey` Exact Orbit | `WLAnchorKey` Symmetric Orbit | `WLAnchorKey` Soft Hungarian | `WLAnchorKey` Total Aligned | Unsound Replay After `checkHintLegality` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `InlineHint` | `96` | `14.58%` | `22.92%` | `89.58%` | `4.17%` | `5.21%` | **`98.96%`** | **`0`** |
| `SroaHint` | `88` | `11.36%` | `18.18%` | `90.91%` | `2.27%` | `5.68%` | **`98.86%`** | **`0`** |
| `LoopOptHint` | `92` | `7.61%` | `14.13%` | `86.96%` | `4.35%` | `6.52%` | **`97.83%`** | **`0`** |
| `VectorizeHint` | `84` | `7.14%` | `13.10%` | `85.71%` | `4.76%` | `7.14%` | **`97.62%`** | **`0`** |
| `RegAllocHint` | `100` | `7.00%` | `13.00%` | `87.00%` | `2.00%` | `8.00%` | **`97.00%`** | **`0`** |

## Boundaries

- **Asymmetric Hints on Completely Indistinguishable Twin Subgraphs (`1.96%` Tier 2 Skip Rate):** When two subgraphs inside the same function have identical opcodes, identical constants, identical dominator/loop topology, and identical distance to every function parameter (e.g., two duplicate loops reading the same global variable), $|\text{Orbit}(c^{(k)})| = 2$. If the oracle suggests *different* transformations for the two twins (`isSymmetricOk = false`), `WLAnchorKey` cannot distinguish them without source spans and conservatively triggers `ambiguousOrbitFallback` (`Tier 2` skip).
- **Decoupling of Alignment Accuracy from Semantic Soundness (`wl_align_and_replay_sound`):** As mechanized in `support/lean/WLOracleAlignment.lean`, `WLAnchorKey` is strictly an untrusted routing heuristic: even if a hash collision or soft-neighborhood match routes a hint to the wrong `MiniSSA` node, `ctx.checkHintLegality` validates the transformation's `HybridTrace` side condition before applying it, guaranteeing `0` unsound compilations.

## Evidence

- **Weisfeiler-Leman Aligner and Datasets (`support/`):**
  - `support/wl_oracle_aligner.py`: Dominator-tree / def-use graph constructor, $k=4$ `SplitMix64` color refinement, and multiscale Hungarian aligner.
  - `support/stripped_drift_benchmark_results.json`: Alignment precision/recall/F1 across `D1`–`D4` (`460` sites) and `25` adversarial symmetry test cases (`150` sites).
- **Lean `v4.34.1` Mechanization (`support/lean/`):**
  - `support/lean/WLOracleAlignment.lean` and `support/lean/lakefile.lean`: Zero-`sorry`, zero-`native_decide` proofs of `uniqueOrbit_injective`, `foldl_orbit_sound`, `wl_align_and_replay_sound`, and `canary_twin_loop_non_unique_orbit_detected`.

## Revalidation

Run the stripped-IR Weisfeiler-Leman benchmark and Lean `v4.34.1` kernel check from the package directory:

```bash
python3 support/wl_oracle_aligner.py
anneal-lean-run --mode file --concurrency 4 -- lean support/lean/WLOracleAlignment.lean
```

Confirm exit code `0`, `o2_wl_dbg0_alignment_pct >= 97.0`, `o2_wl_post_legality_unsound_count == 0`, and axioms limited to `[propext, Quot.sound]`.
