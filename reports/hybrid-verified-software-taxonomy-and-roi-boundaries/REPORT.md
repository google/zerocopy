# Hybrid Verified Software: Benefit Taxonomy, Audit-Surface Collapse, Empirical Crossover Curves, and Negative-ROI Boundaries

## Summary

Splitting a component into an untrusted producer emitting `(output, witness)` (`Option<T>` or fallback-wrapped `T`) and a small trusted or formally verified certificate checker delivers engineering leverage far beyond compiler translation validation, **provided** the problem satisfies both algorithmic/audit asymmetry and positive runtime ROI. Combining direct source-size measurements across `google/zerocopy` (`7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82`) and `leanprover/lean4` (`v4.34.1`) with compiled Rust `-O3` micro-benchmarks ([`support/hybrid_roi_bench.rs`](support/hybrid_roi_bench.rs), [`support/bench_results.json`](support/bench_results.json)) establishes four core results:

1. **Seven Strategic Benefits of Hybrid Verified Software:** Beyond the three baseline motivations—(1) *tractability decomposition* ($T_{\text{check}} \ll T_{\text{solve}}$), (2) *incremental TCB ratcheting*, and (3) *rapid prototyping and containment of untrusted/AI-generated fast paths*—certificate checking provides four additional architectural gains: (4) *human audit-surface collapse*, (5) *hardware mercurial-silicon and compiler-bug resilience*, (6) *multi-producer racing and hardware/offload admission*, and (7) *temporal and witness amortization* (solve once offline, check fast at load or commit time).
2. **Measured Audit-Surface Collapse (`31.1×` Untrusted-to-Semantic-TCB Ratio in Anneal):** Direct non-blank, non-comment SLOC counts on `google/zerocopy@7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82` measure `anneal/trusted/lean/` at `2,865` SLOC (`19` files) versus `66,095` SLOC (`74` files) in `anneal/theory/` and `23,001` SLOC (`16` files) in `anneal/correspondence/` (`89,096` combined untrusted SLOC, `31.1×` larger than `trusted/lean/`), audited via `TrustedBoundary.lean` (`5,135` SLOC). Inside `anneal/theory/Anneal/`, the executable RUP-LRAT checker (`BitTrieLrat.lean`) spans `237` SLOC (`822` SLOC total with soundness proofs) versus `16,184` raw lines in Lean `v4.34.1`'s `Std.Tactic.BVDecide`, and the executable Farkas/Chvátal–Gomory checker (`LinearArith.lean`) spans `281` SLOC (`1,709` SLOC total) versus `1,704` raw lines in `Lean.Elab.Tactic.Omega` (and much larger external LP/MIP solvers).
3. **Measured Runtime Asymmetry and Hardware Crossover Curves (`support/bench_results.json`):** Real `rustc 1.102.0-nightly -C opt-level=3` benchmarks on Linux `x86_64` show:
   - *Strong positive ROI:* DPLL 3-SAT witness checks drop from `4.80%` (`14` vars) to `1.66%` (`22` vars) of solve time; Dijkstra + $O(V + E)$ potential/parent-tree checking costs `3.16%–18.09%` of Dijkstra and runs **`11.62×` (`V=250`) to `70.27×` (`V=2,500`) faster** than an adversarial worst-case Bellman–Ford verified fallback; and LZ77 + Kraft-sum checking drops from `23.94%` (`chain=1`) to `8.49%` (`chain=32`) on `256 KiB` structured data and **`0.04%`** (`263 ns` vs `689 µs`) on incompressible payloads.
   - *Small-$N$ and Cache-Footprint Crossovers:* On `N`-element `u64` sorting with explicit index-permutation witnesses, hybrid sorting (`quicksort((v, idx)) + O(n) check`) is **`2.16×` slower** than direct insertion sort at `N = 16` (`171 ns` vs `79 ns`), breaks even near `N = 64` (`751 ns` vs `671 ns`), beats insertion sort by **`18.43×`** at `N = 2,048`, and then suffers a **`3.41×`** total slowdown vs raw `sort_unstable` at `N = 262,144` (`17.65 ms` vs `5.18 ms`) because doubling element width (`8 B -> 16 B`) and random `seen[perm[i]]` probes hit L2/TLB misses. On $N \times N$ matrix multiplication checked by `k = 20`-round Freivalds, checking costs `391.43%` at `N = 16`, crosses break-even at `N = 64` (`101.57%`), and drops to `25.52%` at `N = 256`.
4. **Six Anti-Hybrid Failure Regimes (Negative ROI):** Hybrid decomposition fails or destroys performance when (1) no sub-solver witness exists (`linear_stream`: `99.49%–101.27%` recomputation tax, `~2×` runtime), (2) input size lies below the witness/cache crossover (`N <= 64` sort/Freivalds), (3) fallback latency lacks worst-case SLAs ($O(VE)$ fallback under adversarial input), (4) no formal correctness predicate exists (empirical ranking/ML without formal invariants), (5) in-place large-buffer mutation blocks cheap rollback, or (6) checker-spec semantic drift omits a binding invariant.

## Applicability

- **Examined code and toolchain artifacts:**
  - `google/zerocopy` at `7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82` (`anneal/theory/Anneal/BitTrieLrat.lean`, `anneal/theory/Anneal/LinearArith.lean`, `anneal/trusted/lean/`, `anneal/trusted/audit/`, `anneal/trusted/correspondence/`, `anneal/correspondence/`, `anneal/theory/`).
  - `leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52` (`src/lean/Std/Tactic/BVDecide/`, `src/lean/Lean/Elab/Tactic/Omega/`).
  - `rust-lang/rust` `rustc 1.102.0-nightly` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (LLVM `23.1.5`), compiling [`support/hybrid_roi_bench.rs`](support/hybrid_roi_bench.rs) on Linux `x86_64` (Intel Xeon `2.60 GHz`, `96` logical CPUs).
- **Relationship to sibling corpus reports:** Synthesizes and avoids duplicating detailed internal algorithms covered in `silent-data-corruption-certifying-algorithms-and-abft-compilation` (Blum–Kannan, LEDA, ABFT), `verified-regalloc2-spill-and-parallel-move-certificate-checker` (`regalloc2`), `sat-inprocessing-drat-lrat-frat-checkers-maxsat-and-qbf-skolem-certificates` (`CaDiCaL`/`LRAT`), and `hybrid-verified-software-contracts-fallback-and-ratcheting` (`Option<T>` contract algebra and TCB ladder). Exact Rust micro-benchmark numbers characterize the specific implementations in `support/hybrid_roi_bench.rs` on the recorded host; broader complexity/crossover conclusions are reasoned from those measurements and inspected source sizes (`Basis: derived`).

## Findings

### 1. Seven-Pillar Taxonomy of Hybrid Verification Leverage

`Basis: source + derived`

| Mechanism | Core Asymmetry Exploited | Concrete Evidence / Precedent |
| :--- | :--- | :--- |
| **1. Tractability Decomposition** | $T_{\text{check}}(x, y, w) \ll T_{\text{solve}}(x)$ (e.g., $\text{NP}$ vs. $\text{P}$, or $O(n)$ check vs. $O(n \log n) / O(n^3) / O(2^n)$ search) | `3-SAT` (`1.66%` check at `22` vars), `MatMul + Freivalds` (`25.52%` check at `N=256`), `SSSP` (`6.9%` check on `V=2500` adversarial graph vs `70.27×` slower fallback) |
| **2. Incremental TCB Ratcheting** | Outer callers verify once against spec `R` (or checker `V`) while inner implementation advances Rung `1 → 2 → 3` | Verified interfaces (`TotalContract` / `OptionContract`) decouple caller proofs from producer/checker evolution |
| **3. Untrusted & Agentic Prototyping** | Complex/experimental or AI-generated heuristics run at full speed inside a verified safety envelope | Anneal's `74`-file `theory/` (`66,095` SLOC) and `16`-file `correspondence/` (`23,001` SLOC) evolve rapidly without risking `trusted/lean/` (`2,865` SLOC) |
| **4. Human Audit-Surface Collapse** | Auditors review only declarative specs + compact checker/boundary instead of solver algorithms | `BitTrieLrat` executable checker `237` SLOC vs `Std.Tactic.BVDecide` `16,184` raw lines; `LinearArith` executable checker `281` SLOC; Anneal `89,096` untrusted vs `2,865` semantic TCB SLOC (`31.1×`) |
| **5. Hardware SDC & Compiler-Bug Diversity** | Small checker on distinct scalar/reference unit defeats deterministic core-local silicon faults & optimizer miscompiles | Cross-referenced from `silent-data-corruption-certifying-algorithms-and-abft-compilation` (`EDDI`/`SWIFT` 100% escape vs algebraic/certifying diversity) and `translation-validation` |
| **6. Multi-Producer Racing & Untrusted Offload** | Multiple aggressive candidates (SIMD, GPU, heuristic variants) race behind a single verified admission gate + fallback | Disjunctive availability amplification (`raceOrFallback`) without multiplying proof burden per heuristic |
| **7. Temporal & Witness Amortization** | Heavy synthesis/solving runs offline or once; compact witness checks in $O(1)$ / linear pass at load or verification time | Precomputed Farkas (`LinearArith`) and RUP (`BitTrieLrat`) certificates replayed by pure `rfl` without re-running simplex/CDCL inside Lean |

---

### 2. Primary-Source Audit-Surface Collapse in Anneal (`google/zerocopy@7527dd2b`)

`Basis: source`

Measuring non-blank, non-comment code lines (SLOC) across `google/zerocopy@7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82` and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` quantifies the exact TCB separation achieved by proof-producing / certificate-checking architectures:

| Module / Zone | Files | Raw Lines | Code SLOC | Role & Trust Status |
| :--- | ---: | ---: | ---: | :--- |
| `anneal/trusted/lean/` | `19` | `6,428` | `2,865` | Semantic TCB: MIR AST, operational semantics, top-level crate judgments |
| `anneal/trusted/correspondence/` | `7` | `4,251` | `3,083` | Reference-adapter TCB anchor (Repository Pass 2 CI only) |
| `anneal/trusted/audit/` | `7` | `11,955` | `9,630` | Standalone boundary preflight + kernel replay auditor (`TrustedBoundary.lean`: `5,135` SLOC) |
| `anneal/theory/` | `74` | `80,587` | `66,095` | **Untrusted** WP logics, `PureLift` (`34,223` raw lines), certificate checkers (`0` TCB) |
| `anneal/correspondence/` | `16` | `24,415` | `23,001` | **Untrusted** MIR correspondence refinement proofs (`0` TCB) |
| `Anneal.BitTrieLrat` (checker / proof) | `1` | `1,059` | `822` (`237` exec / `574` proof) | Pass-1 RUP-LRAT certificate checker vs `Std.Tactic.BVDecide` (`94` files, `16,184` raw lines) |
| `Anneal.LinearArith` (checker / proof) | `1` | `2,061` | `1,709` (`281` exec / `1,416` proof) | Pass-1 Farkas + Chvátal–Gomory checker vs `Lean.Elab.Tactic.Omega` (`4` files, `1,704` raw lines) |

Key structural takeaway: `theory/` + `correspondence/` contains **`89,096` SLOC** (`31.1×` the size of `trusted/lean/`), while individual kernel-reducible certificate checkers (`237` SLOC for `BitTrieLrat`, `281` SLOC for `LinearArith`) remain `10×–68×` smaller than full tactic/solver engines while eliminating external solvers (`CaDiCaL`, simplex/MIP) from the TCB entirely.

---

### 3. Empirical Runtime Asymmetry and Crossover Curves (`rustc -O3`)

`Basis: execution` ([`support/hybrid_roi_bench.rs`](support/hybrid_roi_bench.rs), [`support/bench_results.json`](support/bench_results.json))

#### 3.1 Positive-ROI Regimes (SSSP, 3-SAT, and Deep-Search LZ77)

| Workload & Parameter | Producer Time | Checker Time | Check / Solve (%) | Verified Fallback Time | Observed Engineering Implication |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **SSSP (Random `E=4V-1`, `V=1,000`)** | `90,632 ns` | `16,399 ns` | `18.09%` | `63,457 ns` (early-exit BF) | On easy random graphs, early-exit Bellman–Ford converges fast! |
| **SSSP (Random `E=4V-1`, `V=16,000`)** | `3,674,086 ns` | `480,977 ns` | `13.09%` | — | Check tax shrinks as $\log V$ factor grows in Dijkstra heap |
| **SSSP (Adversarial BF, `V=250`)** | `24,492 ns` | `2,231 ns` | `9.11%` | `310,586 ns` (`11.62×` slower) | Worst-case pass order triggers true $O(VE)$ fallback cliff |
| **SSSP (Adversarial BF, `V=2,500`)** | `320,574 ns` | `22,178 ns` | `6.92%` | `24,085,625 ns` (**`70.27×`**) | Hybrid (`Dijkstra + check`) beats simple verified fallback by `70.3×` |
| **3-SAT DPLL (`14` vars, `59` clauses)** | `11,606 ns` | `557 ns` | `4.80%` | N/A | Checker evaluates `sat_check_witness` (`10` LOC vs `56` LOC DPLL) |
| **3-SAT DPLL (`22` vars, `93` clauses)** | `49,688 ns` | `826 ns` | `1.66%` | N/A | Exponential search gap drives check overhead toward `0%` |
| **LZ77 (`256 KiB`, greedy `chain=1`)** | `1,615,131 ns` | `386,607 ns` | `23.94%` | `memcpy` stored | Fast greedy hash-chain already near $O(n)$, so replay is `~24%` |
| **LZ77 (`256 KiB`, deep `chain=32`)** | `4,220,755 ns` | `358,141 ns` | **`8.49%`** | `memcpy` stored | Deeper match search increases solve cost while replay stays fixed |
| **LZ77 (`64 KiB`, incompressible)** | `689,233 ns` | `263 ns` | **`0.04%`** | `memcpy` stored | Pure literal-run tokens verify in $O(1)$ bounds check (`2` tokens) |

#### 3.2 Measured Crossover Thresholds and Cache-Bloat Traps (`sort` and `matmul_freivalds`)

| Workload & Scale | Baseline / Fallback | Hybrid Producer + Check | Check / Raw (%) | Regime Classification |
| :--- | ---: | ---: | ---: | :--- |
| **Sort `N = 16`** | `79 ns` (insertion sort) | `127 + 44 = 171 ns` (`2.16×` slower) | `66.67%` vs `66 ns` raw | **Negative ROI:** tuple `Vec` alloc + check slower than insertion sort |
| **Sort `N = 64`** | `671 ns` (insertion sort) | `624 + 127 = 751 ns` (`1.12×` slower) | `37.03%` vs `343 ns` raw | **Crossover threshold:** hybrid matches $O(n^2)$ verified baseline |
| **Sort `N = 256`** | `11,188 ns` (insertion sort) | `2,874 + 409 = 3,283 ns` (**`3.41×` faster**) | `25.69%` vs `1,592 ns` raw | **Positive ROI** vs quadratic verified baseline |
| **Sort `N = 2,048`** | `734,851 ns` (insertion sort) | `36,263 + 3,604 = 39,867 ns` (**`18.43×` faster**) | `16.46%` vs `21,890 ns` raw | **Strong positive ROI** vs simple verified baseline |
| **Sort `N = 262,144`** | `5,175,713 ns` (raw `sort_unstable`) | `14,451,240 + 3,196,336 = 17,647,576 ns` | `61.76%` vs `5.18 ms` raw | **Cache/Witness Bloat (`3.41×` total):** `(u64, usize)` doubles working set (`8B -> 16B`) + random `seen[perm[i]]` L2/TLB misses |
| **MatMul + Freivalds (`k=20`, `N=16`)** | `2,380 ns` | `2,380 + 9,316 = 11,696 ns` | **`391.43%`** | **Negative ROI ($N < k$):** $20 N^2 > N^3$ |
| **MatMul + Freivalds (`k=20`, `N=64`)** | `133,097 ns` | `133,097 + 135,191 = 268,288 ns` | `101.57%` | **Exact $O(N^3) \approx O(k N^2)$ crossover** |
| **MatMul + Freivalds (`k=20`, `N=256`)** | `10,914,202 ns` | `10,914,202 + 2,785,550 = 13,699,752 ns` | **`25.52%`** | **Positive ROI:** $O(k N^2)$ check scales cleanly below $O(N^3)$ |
| **Linear Stream (`64 KiB` / `1 MiB`)** | `21,936 ns` / `412,484 ns` | `43,761 ns` / `830,191 ns` | **`99.49%` / `101.27%`** | **Negative ROI:** $O(n)$ stream without sub-linear witness doubles runtime (`2.0×`) |

---

### 4. Ten-Domain Architectural Matrix & Six Negative-ROI Failure Regimes

`Basis: source + execution + derived` (combining Table 3 measurements with `google/zerocopy@7527dd2b` and sibling corpus baselines)

#### 4.1 Ten-Domain Certificate Decomposition Matrix

| Domain | Untrusted Producer Role | Witness / Certificate | Checker Complexity vs. Solve | Fallback Strategy |
| :--- | :--- | :--- | :--- | :--- |
| **1. Graph Shortest Paths / Flow** | Priority-queue / push-relabel solver | Distances + parent tree (or flow + cut) | $O(V + E)$ vs $O((V+E)\log V)$ / $O(VE)$ | Simple verified Bellman–Ford (watch adversarial $O(VE)$ latency) |
| **2. SAT / Bit-Blasted UNSAT** | CDCL + inprocessing (`CaDiCaL`, `bv_decide`) | RUP / LRAT / PR proof (`BitTrieLrat`) | Linear unit-prop replay vs exponential search | Return `Unknown` / bounded timeout (`Option`) |
| **3. LP / ILP / Linear Arithmetic** | Simplex / IPM + cutting planes | Farkas multipliers + Chvátal–Gomory (`LinearArith`) | $O(\text{nnz})$ dot products vs pivot/MIP tree | Return `Unknown` / conservative bound |
| **4. Register Alloc & Compiler Opts** | `RAGreedy`, `ISel`, `GVN`, `LICM` | Allocation map + spill slots + parallel moves (`RegAllocCert`) | $O(\text{insts})$ local simulation vs global graph coloring | Verified `-O0` / baseline non-allocating lowering |
| **5. Compression (LZ77 + Huffman)** | Multi-chain DP / optimal LZ77 + package-merge | `(lit_len, match_len, dist)` + code lengths | $O(n)$ byte replay + exact Kraft check $\sum 2^{15-l_i} \le 2^{15}$ | Uncompressed `BTYPE=00` stored block ratchet (`100%` total) |
| **6. Vectorized Text / Wire Parsing** | Unverified AVX2/NEON lexer + tape builder | Structural index offsets + UTF-8 syndromes | Direct structural re-scan or scalar parse on failure | Verified scalar byte-by-byte parser |
| **7. Numerical / Polynomial Bounds** | Float Newton / SOS / SDP interior-point solver | Exact rational/dyadic Krawczyk or Sturm certificate | Exact integer/interval eval vs continuous search | Conservative wide interval fallback |
| **8. Symbolic Algebra / Integration** | Heuristic Risch / CAS simplification | Antiderivative expression + rewrite hints | Differentiate & compare polynomial/DAG equivalence | Unevaluated numeric quadrature fallback |
| **9. Algebraic / Crypto Kernels** | Multi-limb Montgomery / GCD / NTT heuristics | Bézout coefficients `(s, t)` (`s*a + t*b = g`), `CRT` residues | $O(1)$ multiplications + divisibility vs Euclidean iterations | Verified constant-time binary GCD / schoolbook limb mul |
| **10. Agentic / Multi-Impl Racing** | LLM-generated or SIMD/GPU candidate implementations | Domain witness checked by one verified gate `V` | `|V| << |LLM_impl|` + `0` trust in producer code | Verified slow reference (`raceOrFallback`) |

#### 4.2 Decision Inequality and Six Anti-Hybrid Failure Regimes

For hybrid checking to outperform verifying a fast direct implementation (or running a slow verified baseline), both ROI inequalities must hold:
$$\text{Runtime ROI: } T_{\text{solve}} + T_{\text{check}} + p_{\text{fail}} T_{\text{fallback}} < T_{\text{verified\_direct}} \quad \text{and} \quad \text{Audit ROI: } \text{Audit}(\text{Spec} + \text{Checker} + \text{Fallback} + \text{Isolation}) \ll \text{Audit}(\text{Producer}).$$

Hybridization is **counterproductive (negative ROI)** in six recurring regimes:
1. **No Sub-Solver Witness (`T_check >= T_solve`):** Any $O(n)$ streaming transform (checksums, byte copy, linear scan) whose output carries no redundancy forces the checker to re-read and recompute every input (`linear_stream`: `+101.27%` overhead).
2. **Below-Crossover Instance Size & Witness Cache Bloat:** Witness construction and random-access checking can erase asymptotic wins on small inputs (`N <= 64` sort, `N <= 64` `k=20` Freivalds) or large L2-spilling buffers (`N=262,144` `(val, idx)` sort `3.41×` slowdown).
3. **Adversarial Fallback Latency Cliffs (`p_fail * T_fallback` DoS):** If untrusted inputs or crafted producer rejections trigger a quadratic fallback (`V=2,500` adversarial Bellman–Ford `70.27×` slower), tail latency and DoS bounds break unless the producer is budgeted and fallback complexity meets SLAs.
4. **Absence of a Formalizable Correctness Predicate:** When quality cannot be formally specified (learned ranking, perceptual heuristics), a checker can enforce **hard safety invariants** (bounds, no-NaN, schema validity) but cannot certify optimality.
5. **Destructive In-Place State Mutation:** If a fast-path algorithm mutates gigabytes of shared memory in place before checking completes, rollback copies (`O(N)`) or copy-on-write page faults dominate runtime.
6. **Checker-Spec Semantic Drift:** Checking an incomplete necessary condition (e.g., checking Kraft inequality $\sum 2^{-l_i} \le 1$ without checking code-length monotonicity/max-bits `<= 15`, or trusting derived lengths without input-position conservation) admits silent corruption while paying full checking cost.

## Boundaries

- **Benchmark scope and hardware specificity:** `support/bench_results.json` measures single-threaded, safe Rust (`#![forbid(unsafe_code)]`) micro-benchmarks compiled with `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `-C opt-level=3`) on one Linux `x86_64` Xeon host (`2.60 GHz`). Absolute nanosecond numbers and exact crossover thresholds (`N=64` for `sort`/`matmul`) shift on different CPUs, SIMD widths, memory hierarchies, or when using cache-oblivious/BLAS GEMM (`not examined` on ARM64 or GPU).
- **Producer-vs-checker implementations in `hybrid_roi_bench.rs`:** `sssp_check_witness` checks positive-weight edge triangle inequality + parent-tree step equality (`e.w == 0` rejected; zero-weight cycles require an explicit hop-count depth array `hop[v] == hop[p] + 1`, `not examined` in this benchmark).
- **SLOC measurement limitations:** Raw/SLOC counts compare lines in `google/zerocopy@7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82` and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` as syntactic proxies for audit surface; semantic difficulty per line varies across Lean proofs, Rust code, and C++ solvers (`unknown` exact human audit-hour ratio without user studies).

## Evidence

- **Standalone Rust `-O3` ROI & crossover benchmark suite (preserved in package `support/`):**
  - [`support/hybrid_roi_bench.rs`](support/hybrid_roi_bench.rs) (`#![forbid(unsafe_code)]`, SHA-256 `f05c983983840bb2317079c3c159c82e9977016f092c2367259d558e5542eae7`): implements `sssp_dijkstra_producer` (`L76`), `sssp_check_witness` (`L103`), `sssp_bellman_ford_fallback` (`L147`), `dpll_solve` (`L202`), `sat_check_witness` (`L260`), `sort_with_perm_producer` (`L273`), `sort_check_witness` (`L285`), `insertion_sort_verified_baseline` (`L304`), `matmul_tiled` (`L322`), `freivalds_check` (`L346`), `lz77_hash_producer` (`L396`), `lz77_replay_and_kraft_check` (`L458`), and `fast_unrolled_checksum` (`L498`).
  - [`support/bench_results.json`](support/bench_results.json) (SHA-256 `e79f35a7e56723c279cd16c083bd8e9c7d5914a053c7ba92e821a82e0e8f1043`): full JSON output captured on `2026-11-24` under `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` `--edition 2021 -C opt-level=3` on `x86_64` Intel Xeon `2.60 GHz` (`96` CPUs). Includes negative adversarial controls verifying `sssp_check_witness` rejects perturbed distances and `freivalds_check` (`rounds = 20`) rejects 1-bit-flipped product entries.
- **Primary-source SLOC measurements (`2026-11-24`):**
  - `google/zerocopy` at `7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82`: `anneal/theory/Anneal/BitTrieLrat.lean` (`1,059` raw / `822` SLOC; `237` executable defs / `574` proofs), `anneal/theory/Anneal/LinearArith.lean` (`2,061` raw / `1,709` SLOC; `281` executable defs / `1,416` proofs), `anneal/trusted/lean/` (`19` files, `6,428` raw / `2,865` SLOC), `anneal/trusted/audit/` (`7` files, `11,955` raw / `9,630` SLOC; `TrustedBoundary.lean` `6,620` raw / `5,135` SLOC), `anneal/trusted/correspondence/` (`7` files, `4,251` raw / `3,083` SLOC), `anneal/correspondence/` (`16` files, `24,415` raw / `23,001` SLOC), `anneal/theory/` (`74` files, `80,587` raw / `66,095` SLOC).
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`): `src/lean/Std/Tactic/BVDecide/` (`94` files, `16,184` raw lines), `src/lean/Lean/Elab/Tactic/Omega/` (`4` files, `1,704` raw lines).

## Revalidation

Compile and execute the standalone Rust ROI benchmark suite from `reports/hybrid-verified-software-taxonomy-and-roi-boundaries/`:

```bash
rustc --edition 2021 -C opt-level=3 support/hybrid_roi_bench.rs -o /tmp/hybrid_roi_bench
/tmp/hybrid_roi_bench | python3 -m json.tool
```

Verify that all built-in assertions pass (`verified == true` on all `sssp`, `sat3`, `sort`, `matmul_freivalds`, and `lz77` positive checks plus adversarial rejection assertions) and confirm the qualitative scaling trends (`sssp_adv_bf` fallback ratio increasing with `V`, `matmul_freivalds` crossing `~100%` near `N=64`, `lz77` check ratio dropping from `chain=1` to `chain=32`, and `linear_stream` overhead remaining `~100%`).
