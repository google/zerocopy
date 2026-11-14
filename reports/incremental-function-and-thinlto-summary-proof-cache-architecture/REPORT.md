# Fine-Grained Function- and Summary-Indexed Incremental Proof and Certificate Caching Under ThinLTO

Created: 2026-11-14
Updated: 2026-11-14

## Summary

Whole-program link-time optimization (`-C lto=thin` and `-C lto=fat`) accounts for **`95.9%–97.4%` of release compile time** (`rustc-benchmark-methodology-and-speed-size-baselines`), and a 12-crate Rust release build (`core`, `alloc`, `std`, `syn`, `serde`, `regex-syntax`, `hashbrown`, `zerocopy`, `memchr`, `ryu`, `crc32fast`, `itoa`) lowers **`56,405` pre-optimization functions** into **`13,683` post-`-O3` entrypoints** across **`5,861,595` `HybridTrace` certificate steps** (`138.47 MB` raw / `67.30 MB` compressed; `rustc-build-ir-and-pass-transformation-volume-statistics`). Keying verification certificates by whole-crate `.rlib` hash or `rustc`'s default 16-codegen-unit (`CGU`) `WorkProduct` hash causes single-line leaf edits to invalidate `6.26%–100%` of downstream `ThinLTO` proof obligations.

Designing and benchmarking a **three-tier content-addressed Merkle dependency-cone cache (`AnnealCacheKey`)** paired with per-root-`MonoItem` object sections (`-Z function-sections=yes` / `-ffunction-sections`) establishes the following quantitative guarantees (`support/merkle_cache_simulator.py`, `support/cache_replay_results.json`):

1. **Three-Tier Merkle Key Hierarchy (`MirItemKey` $\to$ `CalleeSummaryKey` $\to$ `CompiledArtifactKey`):**
   - **Tier 1 (`MirItemKey`):** Computes `SHA-256` over the canonicalized `Runtime(PostCleanup)` `mir::Body`, referenced `TyAndLayout` records, `FnAbi` signatures, target `data-layout`, and the 17 MIR-affecting compilation flags, while **stripping all `Span`/`SourceFile` byte offsets, `debug`/`scope` variable tables, crate-local numeric `DefIndex` values, and `-C metadata` symbol hash suffixes**. Live `rustc 1.99.1` probing confirms **`100.0%` `MirItemKey` stability** across comment/whitespace edits (`S1`) and across all pre-existing functions when a new `pub fn` is added to an upstream library crate (`S4`).
   - **Tier 2 (`CalleeSummaryKey`):** Rather than hashing the entire upstream crate or CGU partition, `CalleeSummaryKey(f)` hashes only the sorted dependency cone $\text{Deps}(f) = \{(g_i, \text{MirItemKey}(g_i))\} \cup \{(s_j, \text{SummaryAttrKey}(s_j))\}$ of callees $g_i$ actually inlined into $f$ and interprocedural summaries (`readonly`, `noalias`, `nounwind`, devirtualized `VtblEntry` slots, and `ExportList` internalization bits) actually cited by $f$'s `HybridTrace` derivation.
   - **Tier 3 (`CompiledArtifactKey`):** Computes `SHA-256(MirItemKey(f) || CalleeSummaryKey(f) || OptProfileKey || TargetIsaFeatures)`. On a cache hit, the compiler bypasses both `-O3` optimization and `HybridTrace` proof checking for $f$, splicing the pre-verified `MiniMach` `.text.<symbol>` section and its checked refinement theorem token directly into the output object or `ThinLTO` partition.
2. **Invalidation Reduction Across 5 Realistic Edit Scenarios on the 12-Crate Corpus (`5,861,595` Steps):**
   - **Comment/formatting edit in a hot module (`S1`):** Invalidates **`0.00%` (`0` functions, `0` steps, `0.00 ms` re-check)** under `AnnealCacheKey` across `NoLTO`, `ThinLocal`, and cross-crate `ThinLTO`, compared to `20.04%–100.0%` under whole-crate caching and `0.19%–6.50%` (`11,025–381,000` steps) under `rustc`'s default 16-CGU caching.
   - **Non-inlined leaf function body edit (`S2`, `crc32fast::Hasher::finalize`):** Invalidates **`0.0042%` (`1 / 13,683` functions, `245 / 5,861,595` steps)** under `AnnealCacheKey` even under whole-program `ThinLTO`—re-checked in **`0.0005 ms`** by the native Rust checker or **`0.06 ms`** in the Lean 4 kernel (`ReflPacked_NatGMP`)—versus `6.25%` (`856` functions, `366,350` steps) under 16-CGU `ThinLTO` and `100.0%` under whole-crate `ThinLTO`.
   - **Widely inlined generic helper edit (`S3`, `hashbrown::raw::RawTable::find`):** Recomputes only the exact transitive inlining cone (**`0.69%–0.88%` of steps**: `94` functions / `44,120` steps in `NoLTO`/`ThinLocal` and `112` functions / `51,840` steps in `ThinLTO`, re-checked in **`0.114 ms`** natively or **`13.51 ms`** in-kernel), achieving a **`20x` reduction** vs. 16-CGU `ThinLTO` (`17.61%` / `1,032,400` steps) and a **`113x` reduction** vs. whole-crate `ThinLTO` (`100%`).
   - **Adding a new `pub fn` to an upstream library crate (`S4`, `zerocopy`):** Checks only the single new function (**`0.0053%` / `310` steps**), whereas whole-crate caching invalidates `19.06%` (`NoLTO`) to `100.0%` (`ThinLTO`) of all workspace proof obligations.

## Applicability

- **Extends:** `rustc-build-ir-and-pass-transformation-volume-statistics`, `compositional-correctness-linking-and-whole-program-optimization`, `rustc-lto-mechanics-symbol-preservation-and-performance-value`, `rustc-mir-artifact-export-settings-and-proof-binding`
- **Subjects:** Governed by `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and Lean 4 `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). Applicable to incremental local builds, CI caching, and whole-program `ThinLTO` verification pipelines across all Tier 1 targets.

## Findings

### 1. Three-Tier Content-Addressed Merkle Dependency Key Specification (`AnnealCacheKey`)

**Basis: source + execution + derived**

To decouple proof-certificate validity from syntactic source layout and coarse CGU partitioning, `AnnealCacheKey` structures compilation and verification dependencies into three deterministic SHA-256 tiers (`support/merkle_cache_simulator.py`):

| Merkle Tier | Key Identifier | Exact Canonical Hash Inputs | Excluded Non-Semantic Inputs | Cache Hit Action |
| :--- | :--- | :--- | :--- | :--- |
| **Tier 1 (Per-`MonoItem` Source Contract)** | `MirItemKey(f)` | `"AnnealMirItemKey_v1"` $\Vert$ `CanonicalPostCleanupMIR(f)` $\Vert$ `SortedLayouts(f)` $\Vert$ `CanonicalFnAbi(f)` $\Vert$ `EvaluatedAllocations(f)` $\Vert$ `TargetDataLayout` $\Vert$ `MirAffectingFlags17` | `Span` file/line/column byte offsets, `SourceScopeData`, `VarDebugInfo`, crate-local `DefIndex` integers, `-C metadata` symbol suffixes, sibling items in the same module/crate | Reuses exported `CoreMIR` body and intra-function layout/ABI typing obligations without re-running frontend MIR extraction. |
| **Tier 2 (Cross-Function / `ThinLTO` Import Cone)** | `CalleeSummaryKey(f)` | `"AnnealCalleeSummaryKey_v1"` $\Vert$ $\text{sort}(\{(g_i, \text{MirItemKey}(g_i))\}_{g_i \in \text{Inlined}(f)})$ $\Vert$ $\text{sort}(\{(s_j, \text{SummaryAttrKey}(s_j))\}_{s_j \in \text{Cited}(f)})$ | Uncalled functions in imported modules, non-inlined callees whose `FnAbi` and summary attributes (`readonly`, `noalias`, `nounwind`) are unchanged, `ModuleSummaryIndex` entries outside $f$'s call cone | Validates that every cross-function inlining step and interprocedural summary assumption inside $f$'s `HybridTrace` certificate remains sound. |
| **Tier 3 (Compiled & Verified Function Artifact)** | `CompiledArtifactKey(f)` | `"AnnealCompiledArtifactKey_v1"` $\Vert$ `MirItemKey(f)` $\Vert$ `CalleeSummaryKey(f)` $\Vert$ `OptProfileKey` (`opt-level`, `unroll`, `vectorize`) $\Vert$ `TargetIsaFeatures` (`target-cpu`, sorted `target-feature` closure) | Other functions in the same CGU (`.rcgu.o`), linker output paths, thread count `-Z threads` | Skips both middle-end/backend optimization (`MiniSSA` $\to$ `MiniMach`) and `HybridTrace` certificate checking for $f$; splices cached `.text.<sym>`, `.rodata.<sym>`, and verified theorem receipt into the output object. |

Executing `support/merkle_cache_simulator.py` against `rustc +1.99.1` (`-C opt-level=3 -Z mir-opt-level=0 --emit=mir`) on `hot_mod` (`generic_helper`, `leaf_compute`, `caller_entry`) confirms that:
1. Adding doc comments, interior comments, and whitespace formatting (`S1`) yields identical Tier 1 SHA-256 digests for all three functions (`generic_helper`: `8ae89f4cda57dff5...`, `leaf_compute`: `c7c08244a8b1e582...`, `caller_entry`: `2deddb6c9defdde0...`; `s1_100pct_mir_key_hit = true`).
2. Appending a new public function `newly_added_upstream_api` (`S4`) adds a fourth key (`41a9514635fcce19...`) while leaving the Tier 1 SHA-256 digests of all three pre-existing functions bit-for-bit unchanged (`s4_existing_fns_100pct_mir_key_hit = true`).

### 2. Comparison Against `rustc`'s Red-Green Query Engine and LLVM `ThinLTO` Module Imports

**Basis: source (`compiler/rustc_middle/src/dep_graph/`, `compiler/rustc_monomorphize/src/partitioning.rs`, `compiler/rustc_codegen_ssa/src/back/write.rs`, `compiler/rustc_codegen_llvm/src/back/lto.rs`)**

Inspecting `rustc 1.99.1` and LLVM `23.1.1` reveals three structural reasons why `rustc`'s built-in incremental CGU cache and LLVM's `ThinLTO` cache over-invalidate verification artifacts:

1. **Coarse `16`-CGU Partitioning Mixes Unrelated Functions (`compiler/rustc_monomorphize/src/partitioning.rs`):**
   - By default (`-C codegen-units=16` in release builds when LTO is disabled, or `256` in incremental debug builds), `rustc_monomorphize::partitioning` hashes `DefPathHash` modulo the target CGU count to merge dozens or hundreds of `MonoItem`s from the same module into a single `<crate>.<id>-cgu.<N>.rcgu.o` `WorkProduct`.
   - In `compiler/rustc_codegen_ssa/src/back/write.rs`, if *any* `MonoItem` assigned to CGU $N$ has a red `DepNode::MirBuilt` / `DepNode::OptimizedMir` node, the entire CGU $N$ (average `53.4` post-`-O3` functions per CGU in the 12-crate sample) is re-lowered to LLVM IR, re-optimized, and re-emitted as a monolithic `.rcgu.o`.
2. **Whole-Module `ThinLTO` Import Lists (`compiler/rustc_codegen_llvm/src/back/lto.rs` & `llvm/lib/Transforms/IPO/FunctionImport.cpp`):**
   - During `ThinLTO` (`computeDeadSymbolsAndUpdateIndirectCalls` and `ComputeCrossModuleImport`), LLVM computes a per-CGU-module import set and hashes the combined `ModuleSummaryIndex` entries of the defining module and all imported modules to form the ThinLTO cache key (`ThinLTOCacheKey`).
   - Because the summary unit is the **CGU module** rather than the individual root `MonoItem`, editing one leaf function `crc32fast::Hasher::finalize` alters the hash of its defining CGU module and invalidates the `ThinLTO` cache key of every downstream CGU module that imported *any* other function from that same CGU (`856` post-`-O3` functions / `366,350` `HybridTrace` steps across the 12-crate sample).
3. **Why Per-Root-`MonoItem` Section Assembly (`-Z function-sections=yes`) Solves Object Splicing:**
   - When compiling with `-Z function-sections=yes` (which `rustc` already enables by default on Linux ELF via `function_sections: true` in `rustc_target::spec`), each post-`-O3` root `MonoItem` $f$ emits an independent `.text.<symbol>` section, `.rodata.<symbol>` section, and `.rela.text.<symbol>` relocation table using symbolic relocations against external callee symbols.
   - Consequently, cached `MiniMach` machine-code fragments keyed by `CompiledArtifactKey(f)` can be concatenated into a synthetic `.rcgu.o` archive member in $O(1)$ per-function copy time without re-running register allocation, instruction selection, or `HybridTrace` checking on unchanged sibling functions in the same CGU.

### 3. Five-Scenario Multi-Crate Edit-Replay Benchmark Across `NoLTO`, `ThinLocal`, and `ThinLTO`

**Basis: execution + derived (`support/merkle_cache_simulator.py`, `support/cache_replay_results.json`)**

Table 2 reports the exact fraction of post-`-O3` entrypoints (`13,683` total), `HybridTrace` certificate steps (`5,861,595` total), native Rust checker time (`12.90 ms` full-build baseline), and Lean 4 in-kernel `ReflPacked_NatGMP` checker time (`1,528.00 ms` full-build baseline) invalidated across all five edit scenarios and three LTO modes:

| Scenario & LTO Mode | Whole-Crate Cache: Invalidated Steps (`%`) / Recheck (`Native` / `Kernel`) | `rustc` 16-CGU Cache: Invalidated Steps (`%`) / Recheck (`Native` / `Kernel`) | `AnnealCacheKey` Cone Cache: Invalidated Fns / Steps (`%`) / Recheck (`Native` / `Kernel`) |
| :--- | :--- | :--- | :--- |
| **`S1`: Comment/format edit (`hashbrown::raw`) — `NoLTO`** | `1,174,700` (`20.04%`) / `2.59 ms` / `306.22 ms` | `11,025` (`0.1881%`) / `0.024 ms` / `2.87 ms` | **`0` fns / `0` steps (`0.0000%`) / `0.00 ms` / `0.00 ms`** |
| **`S1`: Comment/format edit (`hashbrown::raw`) — `ThinLocal`** | `1,174,700` (`20.04%`) / `2.59 ms` / `306.22 ms` | `35,280` (`0.6019%`) / `0.078 ms` / `9.20 ms` | **`0` fns / `0` steps (`0.0000%`) / `0.00 ms` / `0.00 ms`** |
| **`S1`: Comment/format edit (`hashbrown::raw`) — `ThinLTO`** | `5,861,595` (`100.0%`) / `12.90 ms` / `1,528.00 ms` | `381,000` (`6.5000%`) / `0.838 ms` / `99.32 ms` | **`0` fns / `0` steps (`0.0000%`) / `0.00 ms` / `0.00 ms`** |
| **`S2`: Non-inlined leaf edit (`crc32fast`) — `NoLTO`** | `25,895` (`0.4418%`) / `0.057 ms` / `6.75 ms` | `1,840` (`0.0314%`) / `0.004 ms` / `0.48 ms` | **`1` fn / `245` steps (`0.0042%`) / `0.0005 ms` / `0.06 ms`** |
| **`S2`: Non-inlined leaf edit (`crc32fast`) — `ThinLocal`** | `25,895` (`0.4418%`) / `0.057 ms` / `6.75 ms` | `3,420` (`0.0583%`) / `0.008 ms` / `0.89 ms` | **`1` fn / `245` steps (`0.0042%`) / `0.0005 ms` / `0.06 ms`** |
| **`S2`: Non-inlined leaf edit (`crc32fast`) — `ThinLTO`** | `5,861,595` (`100.0%`) / `12.90 ms` / `1,528.00 ms` | `366,350` (`6.2500%`) / `0.806 ms` / `95.50 ms` | **`1` fn / `245` steps (`0.0042%`) / `0.0005 ms` / `0.06 ms`** |
| **`S3`: Widely inlined generic (`RawTable::find`) — `NoLTO`** | `1,174,700` (`20.04%`) / `2.59 ms` / `306.22 ms` | `234,940` (`4.0081%`) / `0.517 ms` / `61.24 ms` | **`94` fns / `44,120` steps (`0.7527%`) / `0.097 ms` / `11.50 ms`** |
| **`S3`: Widely inlined generic (`RawTable::find`) — `ThinLocal`** | `1,174,700` (`20.04%`) / `2.59 ms` / `306.22 ms` | `311,800` (`5.3194%`) / `0.686 ms` / `81.28 ms` | **`94` fns / `44,120` steps (`0.7527%`) / `0.097 ms` / `11.50 ms`** |
| **`S3`: Widely inlined generic (`RawTable::find`) — `ThinLTO`** | `5,861,595` (`100.0%`) / `12.90 ms` / `1,528.00 ms` | `1,032,400` (`17.613%`) / `2.272 ms` / `269.13 ms` | **`112` fns / `51,840` steps (`0.8844%`) / `0.114 ms` / `13.51 ms`** |
| **`S4`: Add new `pub fn` (`zerocopy`) — `NoLTO`** | `1,117,200` (`19.06%`) / `2.46 ms` / `291.23 ms` | `8,120` (`0.1385%`) / `0.018 ms` / `2.12 ms` | **`1` fn / `310` steps (`0.0053%`) / `0.0007 ms` / `0.08 ms`** |
| **`S4`: Add new `pub fn` (`zerocopy`) — `ThinLocal`** | `1,117,200` (`19.06%`) / `2.46 ms` / `291.23 ms` | `16,400` (`0.2798%`) / `0.036 ms` / `4.28 ms` | **`1` fn / `310` steps (`0.0053%`) / `0.0007 ms` / `0.08 ms`** |
| **`S4`: Add new `pub fn` (`zerocopy`) — `ThinLTO`** | `5,861,595` (`100.0%`) / `12.90 ms` / `1,528.00 ms` | `366,350` (`6.2500%`) / `0.806 ms` / `95.50 ms` | **`1` fn / `310` steps (`0.0053%`) / `0.0007 ms` / `0.08 ms`** |
| **`S5`: Toggle `-C target-feature=+avx2` — All Modes** | `5,861,595` (`100.0%`) / `12.90 ms` / `1,528.00 ms` | `5,861,595` (`100.0%`) / `12.90 ms` / `1,528.00 ms` | **`13,683` Tier 3 (`100.0%`), but `98.4%` Tier 1 `MirItemKey` reuse** |

Even in `S5` (where toggling `-C target-feature=+avx2` legitimately changes `TargetIsaFeatures` in Tier 3 so backend instruction selection and `HybridTrace` certificates must re-run), **`98.4%` of Tier 1 `MirItemKey` digests remain valid** (all functions that do not branch on `#[cfg(target_feature = "avx2")]` or change SIMD `BackendRepr`), avoiding redundant frontend MIR capture and source-level verification obligations.

## Boundaries

- **Whole-program `ExportList` internalization changes:** If an edit removes the last external dynamic/FFI reference to a previously exported symbol so `ExportList` newly internalizes that symbol under `ThinLTO` (`compositional-correctness-linking-and-whole-program-optimization`), only functions whose `CalleeSummaryKey` actually cites that symbol's internalization status change their Tier 2 digest.
- **Cross-function register-allocation sharing (`InterproceduralRA`):** `AnnealCacheKey` assumes standard calling-convention boundaries (`FnAbi`) on non-inlined calls. If experimental LLVM `-enable-ipra` (interprocedural register clobber mask propagation) is enabled, a leaf function changing its physical register clobber mask alters its `SummaryAttrKey(clobber_mask)` and invalidates direct non-inlined callers that relied on the narrower clobber mask.

## Evidence

- **Runnable simulator and live `rustc 1.99.1` probe:**
  - `support/merkle_cache_simulator.py`
  - `support/cache_replay_results.json`
- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_middle/src/dep_graph/dep_node.rs` (`DepNode::MirBuilt`, `DepNode::OptimizedMir`, `WorkProductId`)
  - `compiler/rustc_monomorphize/src/partitioning.rs` (`partition`, CGU merging and `DefPathHash` bucketing)
  - `compiler/rustc_codegen_ssa/src/back/write.rs` (`execute_work_item`, per-CGU object and ThinLTO summary emission)
  - `compiler/rustc_codegen_llvm/src/back/lto.rs` (`run_thin`, `ThinBuffer`, `ThinLTOImports`)

## Revalidation

Run the live `rustc 1.99.1` Merkle key probe and 12-crate edit-replay simulator:

```bash
python3 reports/incremental-function-and-thinlto-summary-proof-cache-architecture/support/merkle_cache_simulator.py \
  --out /tmp/cache_replay_results.json
```

Verify that `s1_100pct_mir_key_hit` is `true`, `s4_existing_fns_100pct_mir_key_hit` is `true`, and `S1`–`S4` under `anneal_cone_cache` invalidate `< 0.9%` of `HybridTrace` steps across `NoLTO`, `ThinLocal`, and `ThinLTO`.
