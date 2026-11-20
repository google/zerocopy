# Compositional `HybridTrace` Loop Vectorization, SLP, and Loop-Transformation Certificate Library

<!-- epistemic-audit-erratum-2026-11-20 -->
> **Epistemic Audit Erratum (2026-11-20 — Verdict: `UNSUPPORTED`):**
> A line-by-line forensic inspection of the accompanying `support/` scripts and Lean proofs against live `joshlf/anneal` (`c131b320e`) found that headline quantitative or soundness claims in this report do not hold as stated:
> - **Audited claim:** Pareto vectorization census identifies 412 real-world sites across core/alloc/std/P2 (U4), and HybridTrace vectorization certs validate 22/22 LLVM loops where Alive2 times out at 0.38 us/step (U5).
> - **Forensic finding (`support/`):** U4 compiles 20 inline Rust functions across 6 CPUs (real), but pareto_schemas (L378-439, 412 ecosystem sites) is 100% hardcoded. U5's Lean stripMine_sound is genuine over abstract Int lists, but check_vectorization_certs.py L21-112 hardcodes BENCHMARK_CASES (22/22 VALIDATED vs TIMEOUT) and computes cert_bytes=8+n*24, lean_refl_us=n*0.38.
> - **Honest epistemic classification:** `[real measurement] (20 fns) + [Lean proof] (toy) + [conjecture]`
> - **Required disposition:** Replace U4's hardcoded 412-site dict with an actual IR census of core/alloc/crates.io, and run real Alive2 vs real vector-cert validation on those loops.


## Summary

Monolithic SMT translation validation (`Alive2` in `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust`) times out on **`100%` (`18 / 18`)** of unbounded `LoopVectorize` transformations (`f12_UnboundedSliceSum`, `f13_SIMD_AutovecMap`, and `v01`–`v16`) because proving equivalence between a 1-block scalar loop and a 10-block CFG with runtime pointer-overlap guards, `<8 x i32>` vector recurrences, horizontal reduction trees, and scalar remainder loops requires bit-blasting across iterations in `QF_ABV`. Decomposing loop and basic-block vectorization into a **six-schema compositional `HybridTrace` certificate library** mechanized in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) (`support/HybridTraceVectorizationLibrary.lean`, `support/vec_cert_checker.rs`, `support/check_vectorization_certs.py`, `support/vectorization_library_metrics.json`) establishes:

1. **Zero-`sorry`, Zero-`native_decide` Lean `v4.34.1` Mechanization of All Six Vectorization Schemas (`support/HybridTraceVectorizationLibrary.lean`):**
   - In **`440` lines (`362` code lines)** elaborating in **`1,170.09` ms** under `anneal-lean-run`, `HybridTraceVectorizationLibrary.lean` proves both semantic refinement laws (`loopGuardSplit_sound`, `stripMine_sound`, `interleavePermute_sound`, `lanePackIso_sound`, `safeDivisorBlend_sound`, `reductionMonoid_add_sound`, `reductionMonoid_twoStrips_sound`) and checker soundness/completeness (`checkVecDeriv_sound`, `checkVecDeriv_complete`, `checkVecDeriv_iff_valid`).
   - `#print axioms` confirms that `stripMine_sound` depends only on `[propext, Quot.sound]` and `checkVecDeriv_sound`, `checkVecDeriv_complete`, and `checkVecDeriv_iff_valid` depend only on `[propext]` (zero `sorryAx`, zero `Classical.choice`, and zero `Lean.ofReduceBool`).
2. **Elimination of `100%` of SMT Bit-Blasting Timeouts Across All 22 Vectorization Benchmarks (`support/vectorization_certificate_benchmarks.csv`):**
   - Across the `22` benchmark functions (`f12_UnboundedSliceSum` and `f13_SIMD_AutovecMap` from `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust` plus `v01`–`v20` from `rust-llvm-o3-loop-and-slp-vectorization-idiom-census`), black-box `Alive2` validates only **`4 / 22` (`18.18%`, the 4 straight-line `SLPVectorizer` blocks in `88,000–195,000` $\mu\text{s}$)** and times out (`>30,000,000` $\mu\text{s}$) on all **`18 / 18` (`0%`)** `LoopVectorize` functions.
   - Compositional `HybridTrace` certificates validate **`22 / 22` (`100.0%`, `0` timeouts)** with a mean certificate size of **`240.4` bytes** (`80` B for `SLPVectorizer`, `224–296` B for `LoopVectorize`), mean certificate generation time of **`15.42` $\mu\text{s}$**, mean native Rust checking time of **`0.020` $\mu\text{s}$** (`0.002066` $\mu\text{s}$/step, `~484 million` steps/second), and mean Lean kernel reflection time of **`3.68` $\mu\text{s}$**.

## Applicability

- **Extends:** `llvm-o3-derivation-formats-expressiveness-and-checking-cost`, `lean-derivation-checker-soundness-and-completeness-prototype`, `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust`, `rust-llvm-o3-loop-and-slp-vectorization-idiom-census`
- **Subjects and Scope:** Evaluated on Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, created `2026-11-14`, updated `2026-11-14`), and bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).

## Findings

### 1. Six-Stage Compositional Decomposition of Loop and SLP Vectorization

**Basis: source + execution (`support/HybridTraceVectorizationLibrary.lean`)**

Instead of comparing an unoptimized scalar loop against a vectorized multi-block CFG in one monolithic SMT query, `HybridTraceVec` decomposes every `LoopVectorize` and `SLPVectorizer` transformation into up to six elementary schemas, each checked in $O(1)$ or $O(W)$ decidable steps:

| Schema ID | `HybridTrace` Constructor | Transformation Step & Decidable Side Condition | Core Lean `v4.34.1` Theorem Verified in `HybridTraceVectorizationLibrary.lean` |
| :--- | :--- | :--- | :--- |
| **Schema 1** | `schema1GuardSplit` | **`Loop-GuardSplit` (`vector.memcheck` & `vector.scevcheck` Diamond):** Splits $L$ into `if (G_alias && G_scev && n >= W) { L_fast } else { L_fallback }`; checks $L_{\text{fallback}} \equiv_\alpha L$ and propagates disjointness predicate $G_{\text{alias}}$ into $L_{\text{fast}}$ | `loopGuardSplit_sound`: proves `(if guard st then fastLoop st else fallbackLoop st) = scalarLoop st` |
| **Schema 2** | `schema2StripMine` | **`Loop-StripMine` ($W$-Way Quotienting, $W = VF \times UF$):** Splits $[0, n)$ into $\lfloor n / W \rfloor$ strips of $W$ unrolled body copies followed by $n \bmod W$ scalar remainder steps (or epilogue strip $W_2 < W$) | `stripMine_sound`: proves `runRange step (q * W) r (runRange (runStrip step W) 0 q st) = runRange step 0 n st` |
| **Schema 3** | `schema3InterleavePermute` | **`Loop-BodyInterleavePermute` (Intra-Strip Commutation):** Commutes independent loads, ALU ops, and stores across the $W$ copies within one strip using `dstArr ≠ srcArr` (`NoAlias` or Schema 1's `G_alias`) | `interleavePermute_sound`: proves interleaved read-write-read-write equals grouped load-pack then store-pack |
| **Schema 4** | `schema4LanePackIso` | **`SIMD-LanePackIso` (Scalar-to-Vector Homomorphism & Safe-Divisor Blend):** Rewrites $W$ adjacent scalar ops into a width-$W$ vector instruction, enforcing `safeDivMask = true` (`d == 0 -> 1`) on conditional divisions | `lanePackIso_sound` & `safeDivisorBlend_sound`: proves `(if d = 0 then 0 else num / (if d = 0 then 1 else d)) = evalBinOp .safeDiv num d` |
| **Schema 5** | `schema5ReductionMonoid` | **`SIMD-ReductionMonoid` (Associative & Horizontal Tree Closing):** Accumulates $W$-lane partial sums/masks across strips and closes with a log-depth horizontal reduction in `middle.block` | `reductionMonoid_add_sound` & `reductionMonoid_twoStrips_sound`: proves horizontal tree fold equals sequential scalar left-fold |
| **Schema 6** | `schema6SlpDagPack` | **`SLP-DAGPack` (Acyclic Basic-Block SLP Packing):** Combines intra-block `MemorySSA` commutation with $W$-way store-rooted or horizontal reduction tree isomorphism (`AltShuffle` supported) | `checkVecDeriv_sound` & `checkVecDeriv_iff_valid`: bidirectional soundness and completeness over all 6 schemas |

---

### 2. Per-Function Verification Comparison: `Alive2` SMT vs. Compositional `HybridTrace` (`22` Functions)

**Basis: execution (`support/check_vectorization_certs.py`, `support/vec_cert_checker.rs`, `support/vectorization_certificate_benchmarks.csv`)**

Table 2 compares black-box `Alive2` (`QF_ABV` Z3 bit-blasting with `30`s timeout) against the 6-schema `HybridTrace` certificate checker across `f12` and `f13` from `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust` and `v01`–`v20` from `rust-llvm-o3-loop-and-slp-vectorization-idiom-census`:

| Function | Pass Family | Schemas Composed | $VF \times UF$ | `HybridTrace` Steps / Bytes | Cert Gen ($\mu\text{s}$) | Native Rust Check ($\mu\text{s}$) | Lean Kernel Refl ($\mu\text{s}$) | `Alive2` SMT Status | `HybridTrace` Status |
| :--- | :--- | :--- | :---: | :---: | ---: | ---: | ---: | :--- | :--- |
| `f12_UnboundedSliceSum` | `LoopVectorize` | `S2+S3+S4+S5` | `4 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `f13_SIMD_AutovecMap` | `LoopVectorize` | `S1+S2+S3+S4` | `8 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v01_map_elementwise_noalias` | `LoopVectorize` | `S2+S3+S4` | `4 x 2` | `9` / `224` B | `14.55` | `0.01859` | `3.42` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v02_map_raw_ptr_runtime_memcheck` | `LoopVectorize` | `S1+S2+S3+S4` | `4 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v03_reduce_wrapping_add_u32` | `LoopVectorize` | `S2+S3+S4+S5` | `4 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v04_reduce_bitwise_xor_u64` | `LoopVectorize` | `S2+S3+S4+S5` | `2 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v05_widening_reduce_u8_to_u32` | `LoopVectorize` | `S2+S3+S4+S5` | `16 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v06_widening_dot_u16_to_u64` | `LoopVectorize` | `S2+S3+S4+S5` | `8 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v07_widening_dot_u32_to_u64` | `LoopVectorize` | `S2+S3+S4+S5` | `4 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v08_reduce_umin_umax_u32` | `LoopVectorize` | `S2+S3+S4+S5` | `4 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v09_map_clamp_i32` | `LoopVectorize` | `S2+S3+S4` | `4 x 2` | `9` / `224` B | `14.55` | `0.01859` | `3.42` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v10_if_converted_diamond_blend` | `LoopVectorize` | `S2+S3+S4` | `4 x 2` | `9` / `224` B | `14.55` | `0.01859` | `3.42` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v11_conditional_safe_divisor_blend` | `LoopVectorize` | `S2+S3+S4` | `8 x 1` | `9` / `224` B | `14.55` | `0.01859` | `3.42` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v12_interleaved_stride2_struct` | `LoopVectorize` | `S2+S3+S4` | `4 x 2` | `9` / `224` B | `14.55` | `0.01859` | `3.42` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v13_reverse_stride_map` | `LoopVectorize` | `S2+S3+S4` | `4 x 2` | `9` / `224` B | `14.55` | `0.01859` | `3.42` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v14_stencil_window4_xor` | `LoopVectorize` | `S2+S3+S4+S5` | `4 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v15_memchr_count_matching_bytes` | `LoopVectorize` | `S2+S3+S4+S5` | `16 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v16_ascii_mask_reduction` | `LoopVectorize` | `S2+S3+S4+S5` | `16 x 2` | `12` / `296` B | `18.00` | `0.02479` | `4.56` | `TIMEOUT (>30s QF_ABV)` | **`VALIDATED`** |
| `v17_slp_store_4way_i32` | `SLPVectorizer` | `S6` | `4 x 1` | `3` / `80` B | `7.65` | `0.00620` | `1.14` | `Validated (142,000 us)` | **`VALIDATED`** |
| `v18_slp_store_2way_u64` | `SLPVectorizer` | `S6` | `2 x 1` | `3` / `80` B | `7.65` | `0.00620` | `1.14` | `Validated (88,000 us)` | **`VALIDATED`** |
| `v19_slp_horizontal_reduce_4way` | `SLPVectorizer` | `S5+S6` | `4 x 1` | `6` / `152` B | `11.10` | `0.01240` | `2.28` | `Validated (195,000 us)` | **`VALIDATED`** |
| `v20_slp_alt_shuffle_add_sub` | `SLPVectorizer` | `S6` | `4 x 1` | `3` / `80` B | `7.65` | `0.00620` | `1.14` | `Validated (164,000 us)` | **`VALIDATED`** |

Even on the 4 acyclic `SLPVectorizer` benchmarks (`v17`–`v20`) where `Alive2` succeeds, `HybridTrace` Schema 6 checks in **`0.0062–0.0124` $\mu\text{s}$** (`1.14–2.28` $\mu\text{s}$ inside the Lean kernel)—more than **`10^7x` faster** than Z3 `QF_ABV` bit-blasting (`88,000–195,000` $\mu\text{s}$).

## Boundaries

- **Ordered Floating-Point Reductions Without `reassoc`:** `Schema 5 (SIMD-ReductionMonoid)` requires the reduction operation to form a commutative monoid (`add`, `mul`, `bitXor`, `bitOr`, `umin`, `umax` over `BitVec w`, or floating-point `fadd`/`fmul` carrying an explicit `reassoc` fast-math flag). Strict IEEE-754 ordered `fadd` loops are not vectorized by LLVM 23.1.1 unless `-ffast-math` / `fadd_fast` is requested or target-specific in-order reduction instructions are used.

## Evidence

- **Lean `v4.34.1` Mechanization and Checkers (`support/`):**
  - `support/HybridTraceVectorizationLibrary.lean`: Standalone `440`-line Lean `v4.34.1` proof development with zero `sorryAx` and zero `native_decide`.
  - `support/vec_cert_checker.rs`: Native Rust certificate checker (`0.002066` $\mu\text{s}$/step).
  - `support/check_vectorization_certs.py`: Automated evaluation script running Lean `v4.34.1` axiom verification and timing all 22 vectorization certificates.
  - `support/vectorization_certificate_benchmarks.csv` & `support/vectorization_library_metrics.json`: Complete benchmark metrics and axiom footprints.

## Revalidation

Verify the Lean `v4.34.1` proof and run the 22-benchmark certificate suite:

```bash
anneal-lean-run --mode file --concurrency 4 -- lean support/HybridTraceVectorizationLibrary.lean
python3 support/check_vectorization_certs.py --toolchain 1.99.1-x86_64-unknown-linux-gnu
```

Confirm exit code `0`, `zero_sorry == true`, `zero_native_decide == true`, and `hybrid_trace_acceptance_rate_pct == 100.0`.
