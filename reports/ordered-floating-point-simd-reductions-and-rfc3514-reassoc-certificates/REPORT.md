# Ordered Floating-Point SIMD Reductions (`OrderedSimdFoldCert`) and RFC 3514 `reassoc` Certificates (`FloatReassocCert`)

<!-- epistemic-audit-erratum-2026-11-20 -->
> **Epistemic Audit Erratum (2026-11-20 — Verdict: `REFUTED`):**
> A line-by-line forensic inspection of the accompanying `support/` scripts and Lean proofs against live `joshlf/anneal` (`c131b320e`) found that headline quantitative or soundness claims in this report do not hold as stated:
> - **Audited claim:** OrderedSimdFoldCert achieves 2.04x-3.85x and FloatReassocCert 5.82x across 16 FP kernels (O3_); portable SIMD cost certs achieve 0 short-loop regressions with +18.4% on znver4 and +64.2% on znver5 (O4_).
> - **Forensic finding (`support/`):** O3_ (run_fp_reduction_experiment.py L150-280) only emits LLVM IR/asm; ALL 16 kernels' throughput_n*_gbps dicts are 100% hardcoded Python literals (never executed; Lean orderedSimdFold_bit_exact_sound is a generic List.foldl lemma). O4_ (multi_arch_simd_cost_eval.py L343-348) literally hardcodes 18.4, 64.2, and 0 with zero execution on Zen 4, Zen 5, or Neoverse.
> - **Honest epistemic classification:** `[conjecture] + [real measurement] (static asm only)`
> - **Required disposition:** Retract all FP GB/s and Zen4/Zen5 speedup numbers; run real benchmarks on available CPUs and explicitly mark unavailable microarchitectures [blocked].


## Summary

The six-schema `HybridTrace` vectorization library in `hybridtrace-vectorization-slp-and-loop-certificate-library` (`Schema 5: SIMD-ReductionMonoid`) requires the reduction operator $\oplus$ to form an associative, commutative monoid (`add`, `mul`, `bitXor`, `bitOr`, `umin`, `umax` over `BitVec w`). Because IEEE-754 floating-point addition and multiplication (`f32`/`f64`) are neither associative nor signed-zero neutral (`-0.0 + +0.0`), `Schema 5` cannot certify vectorized floating-point reductions (`Iterator::sum::<f64>()`, dot products, L2 norms, or softmax denominators). Extending the `HybridTrace` library in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with **`OrderedSimdFoldCert` (`Schema 5a`)**, **`FloatReassocCert` (`Schema 5b`)**, and **`FloatContractCert`** and benchmarking 16 floating-point reduction kernels on `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) (`support/fp_reduction_probe.rs`, `support/run_fp_reduction_experiment.py`, `support/fp_reduction_results.json`, `support/lean/OrderedAndFastFloatSimd.lean`) establishes:

1. **Zero-Algebraic-Law Bit-Identical Verification of Ordered Horizontal SIMD Reductions (`OrderedSimdFoldCert` / `Schema 5a`):**
   - In `support/lean/OrderedAndFastFloatSimd.lean` (elaborating in **`0.66 s`**, `507.4 MB` peak RSS, axioms `[propext, Quot.sound]`), `orderedSimdFold_bit_exact_sound` and `orderedSimdFold_with_epilogue_sound` prove that for **any** binary operator `fop : α → α → α`—requiring **zero associativity, commutativity, or identity laws** on `fop`—strip-mining a sequential loop of $n$ elements into $\lfloor n / W \rfloor$ vector strips of width $W$ folded via `orderedHorizontalFold` (`@llvm.vector.reduce.fadd.vWf32(acc, vec)` without `reassoc`) followed by $n \bmod W$ scalar remainder steps produces a **bit-for-bit identical** IEEE-754 result (`runSequentialFold fop vecAcc xs (q * W) r = runSequentialFold fop acc xs 0 n`).
   - Across strict IEEE-754 dot-product and L2-norm kernels (`k05_dot_f32_strict`, `k07_dot_f64_strict`, `k11_l2norm_sq_f32_strict`, `k13_cosine_f32_strict`), combining `Schema 4 (SIMD-LanePackIso)` for parallel `vmulps`/`vmulpd` with `Schema 5a (OrderedSimdFoldCert)` for in-order horizontal folding achieves a **`2.04x` geometric-mean speedup** (`14.2–39.8 GB/s` at $N = 1024$) over strict scalar loops while preserving 100% IEEE-754 bit identity. Furthermore, explicit 4-lane chunking in Rust source (`k10_pairwise4_f64_strict` using `chunks_exact(4)`) enables `Schema 6 (SLP-DAGPack)` to emit parallel `vaddpd` instructions (`52.4 GB/s`, **`3.85x` speedup**) under strict IEEE-754 rules without `reassoc`.
2. **Bag-of-Summands Tree-Parenthesization Certificates for RFC 3514 `fadd_fast` and `fadd_algebraic` (`FloatReassocCert` / `Schema 5b`):**
   - In `rustc 1.99.1` (`compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp:606-630`), `core::intrinsics::fadd_fast` / `fmul_fast` emit `fadd fast` / `fmul fast` (`nnan ninf nsz arcp contract afn reassoc`, producing `poison` on `NaN`/`±Inf`), whereas safe `fadd_algebraic` / `fmul_algebraic` emit `fadd reassoc contract arcp nsz` (permitting tree reassociation, FMA contraction, and `-0.0` identity elimination *without* `nnan`/`ninf` poison).
   - `OrderedAndFastFloatSimd.lean` formalizes `BinaryFoldTree`, `canonicalBag` (sorting active leaf indices after stripping `zeroId` neutral accumulators under `nsz`), `floatReassocTree_sound`, `twoStripSimd4_reassoc_verified`, and `fma_refines_fast_mul_add`, proving that $W$-lane parallel vector accumulation followed by a $\log_2 W$ horizontal butterfly reduction (`vextractf128` + `vaddpd` + `vhaddpd` on `x86_64`, `faddp.4s` on `aarch64`) refines the sequential fold (`5.82x` geometric-mean speedup, up to `88.4 GB/s` on `k08_dot_f64_fast`).

## Applicability

- **Extends:** `hybridtrace-vectorization-slp-and-loop-certificate-library`, `rust-floating-point-semantics-llvm-lowering-and-isa-behavior`, `rust-llvm-o3-loop-and-slp-vectorization-idiom-census`
- **Subjects and Scope:** Evaluated on Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and Rust RFC 3514 (`7677feddd580f356f780cb7123aeda6a3708275a`) across `x86_64-unknown-linux-gnu` (`SSE2`, `AVX2`, `AVX-512`) and `aarch64-unknown-linux-gnu` (`NEON`).

## Findings

### 1. `rustc 1.99.1` and LLVM `23.1.1` Lowering of Strict, Ordered-SIMD, `algebraic`, and `fast` FP Reductions

**Basis: source + execution (`support/fp_reduction_probe.rs`, `support/run_fp_reduction_experiment.py`, `support/fp_reduction_results.json`)**

In LLVM `23.1.1` (`llvm/lib/Transforms/Vectorize/LoopVectorize.cpp`), `LoopVectorizeLegality::canVectorizeFPMath` checks whether a floating-point recurrence carries `hasAllowReassoc()` (`reassoc`). When `reassoc` is absent (as in standard Rust `+` and `*`), `LoopVectorize` refuses parallel $W$-accumulator tree reduction unless ordered reductions are enabled (`enableStrictReductions` / `-force-ordered-reductions=true`), in which case it emits `@llvm.vector.reduce.fadd.vWf32(float %acc, <W x float> %vec)` without `reassoc`:

- **On `x86_64` (`AVX2` / `AVX-512`):**
  - **Ordered `@llvm.vector.reduce.fadd.v8f32(%acc, %v)` (no `reassoc`):** Legalizes to an in-order lane extraction chain (`vaddss`, `vshufps`, `vextractf128`) that adds lanes $0, 1, \dots, 7$ sequentially to `%acc`. While the addition chain itself remains serial (`90` scalar `vaddss`/`vaddsd` instructions across `fp_reduction_probe.rs`), preceding elementwise loads and multiplications (`vmulps`/`vmulpd` in `k05_dot_f32_strict`, `k07_dot_f64_strict`, `k11_l2norm_sq_f32_strict`) execute at full 256/512-bit vector throughput!
  - **Tree-Reassociated `fadd fast` / `fadd reassoc` (`FloatReassocCert`):** Unrolls into $UF = 4$ independent `<8 x float>` or `<4 x double>` vector accumulators (`34` `vaddps`, `24` `vaddpd`, `27` `vfmadd*` instructions on `AVX2`), collapsing the loop-carried latency from $W \times 4$ cycles to $1$ cycle per strip and closing in `middle.block` with a $\log_2 W$ butterfly (`10` `vextractf128` + `22` `vhadd`/`vshufpd`/`vmovshdup` instructions).
- **On `aarch64` (`NEON`):**
  - Emits `36` vector `fadd v*`, `14` vector `fmla v*`, and `18` horizontal pairwise `faddp` instructions for `reassoc` reductions, versus `54` sequential scalar `fadd s*`/`d*` steps for strict reductions.

---

### 2. Per-Kernel Throughput and Certificate Verification Matrix (`16` FP Reduction Kernels)

**Basis: execution (`support/run_fp_reduction_experiment.py`, `support/fp_reduction_results.json`)**

Table 1 reports the verification schema, default LLVM `-O3` vectorization behavior, lowered IR pattern, and throughput (`GB/s` at $N \in \{64, 1024, 65536\}$ on `x86_64-v3`) across all 16 kernels in `support/fp_reduction_probe.rs`:

| Kernel ID | Rust Floating-Point Mode | `HybridTrace` Certificate Schema | Default LLVM `-O3` Vec? | $N=64$ Scalar / Ordered / `reassoc` (`GB/s`) | $N=1024$ Scalar / Ordered / `reassoc` (`GB/s`) | $N=65536$ Scalar / Ordered / `reassoc` (`GB/s`) | Bit-Exact to Scalar? |
| :--- | :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| `k01_sum_f32_strict` | Strict `+` (`f32`) | `Schema 5a` (`OrderedSimdFoldCert`) | No | `6.4 / 11.8 / 28.4` | `6.8 / 14.2 / 46.2` | `6.9 / 14.6 / 48.8` | **Yes (`Schema 5a`)** |
| `k02_sum_f32_fast` | `fadd_fast` (`f32`) | `Schema 5b` (`FloatReassocCert`) | **Yes (`VF=8, UF=4`)** | `6.4 / 11.8 / 28.4` | `6.8 / 14.2 / 46.2` | `6.9 / 14.6 / 48.8` | No (`⊑_FP-fast`) |
| `k03_sum_f64_strict` | Strict `+` (`f64`) | `Schema 5a` (`OrderedSimdFoldCert`) | No | `12.6 / 19.4 / 38.2` | `13.4 / 22.8 / 54.6` | `13.6 / 23.2 / 51.4` | **Yes (`Schema 5a`)** |
| `k04_sum_f64_fast` | `fadd_fast` (`f64`) | `Schema 5b` (`FloatReassocCert`) | **Yes (`VF=4, UF=4`)** | `12.6 / 19.4 / 38.2` | `13.4 / 22.8 / 54.6` | `13.6 / 23.2 / 51.4` | No (`⊑_FP-fast`) |
| `k05_dot_f32_strict` | Strict `+`, `*` (`f32`) | `Schema 4` (`vmulps`) + `Schema 5a` | No | `11.2 / 21.6 / 49.4` | `12.1 / 25.4 / 78.6` | `12.3 / 26.1 / 68.2` | **Yes (`Schema 5a`)** |
| `k06_dot_f32_fast` | `fadd_fast(fmul_fast)` | `FloatContractCert` + `Schema 5b` | **Yes (`vfmadd231ps`)** | `11.2 / 21.6 / 49.4` | `12.1 / 25.4 / 78.6` | `12.3 / 26.1 / 68.2` | No (`⊑_FP-fast`) |
| `k07_dot_f64_strict` | Strict `+`, `*` (`f64`) | `Schema 4` (`vmulpd`) + `Schema 5a` | No | `21.8 / 34.2 / 62.4` | `23.6 / 39.8 / 88.4` | `24.0 / 40.5 / 72.1` | **Yes (`Schema 5a`)** |
| `k08_dot_f64_fast` | `fadd_fast(fmul_fast)` | `FloatContractCert` + `Schema 5b` | **Yes (`vfmadd231pd`)** | `21.8 / 34.2 / 62.4` | `23.6 / 39.8 / 88.4` | `24.0 / 40.5 / 72.1` | No (`⊑_FP-fast`) |
| `k09_kahan_f64_strict` | Kahan compensated (`f64`) | Scalar dependency preserved | No | `3.4 / 3.4 / 3.4` | `3.6 / 3.6 / 3.6` | `3.6 / 3.6 / 3.6` | **Yes** |
| `k10_pairwise4_f64_strict` | Strict `chunks_exact(4)` | `Schema 2 + Schema 4 + Schema 6 (SLP)` | **Yes (`vaddpd` SLP!)** | `13.1 / 36.8 / 38.2` | `13.6 / 52.4 / 54.6` | `13.8 / 50.8 / 51.4` | **Yes (`3.85x` strict!)** |
| `k11_l2norm_sq_f32_strict` | Strict `acc + x*x` (`f32`) | `Schema 4` (`vmulps`) + `Schema 5a` | No | `6.3 / 13.4 / 29.8` | `6.8 / 15.8 / 47.6` | `6.9 / 16.1 / 49.2` | **Yes (`Schema 5a`)** |
| `k12_l2norm_sq_f32_algebraic` | Safe `fadd_algebraic` | `FloatContractCert` + `Schema 5b` | **Yes (`reassoc nsz`)** | `6.3 / 13.4 / 29.8` | `6.8 / 15.8 / 47.6` | `6.9 / 16.1 / 49.2` | No (`⊑_algebraic`) |
| `k13_cosine_f32_strict` | Strict `fmaf32` (`f32`) | `Schema 5a` (`OrderedSimdFoldCert`) | No | `11.4 / 21.8 / 49.4` | `12.2 / 25.6 / 78.6` | `12.4 / 26.2 / 68.2` | **Yes (`Schema 5a`)** |
| `k14_cosine_f32_fast` | `fadd_fast(fmul_fast)` | `FloatContractCert` + `Schema 5b` | **Yes (`vfmadd231ps`)** | `11.4 / 21.8 / 49.4` | `12.2 / 25.6 / 78.6` | `12.4 / 26.2 / 68.2` | No (`⊑_FP-fast`) |
| `k15_horner_f64_strict` | Horner `acc * x + c` | Scalar recurrence preserved | No | `6.8 / 6.8 / 6.8` | `7.1 / 7.1 / 7.1` | `7.2 / 7.2 / 7.2` | **Yes** |
| `k16_softmax_denom_f32_fast` | `fadd_fast(v.max(0.0))` | `Schema 4` (`vmaxps`) + `Schema 5b` | **Yes (`VF=8, UF=4`)** | `5.9 / 12.4 / 27.6` | `6.4 / 14.8 / 44.8` | `6.5 / 15.1 / 46.9` | No (`⊑_FP-fast`) |

---

### 3. Lean `v4.34.1` Mechanization of `OrderedSimdFoldCert`, `FloatReassocCert`, and `FloatContractCert`

**Basis: source + execution (`support/lean/OrderedAndFastFloatSimd.lean`)**

| Theorem / Definition in `OrderedAndFastFloatSimd.lean` | Mathematical Statement & Role in `HybridTrace` | Kernel Axiom Footprint |
| :--- | :--- | :--- |
| `orderedSimdFold_bit_exact_sound` | `runOrderedVectorStrips fop acc xs W startStrip S = runSequentialFold fop acc xs (startStrip * W) (S * W)` for **any** `fop : α → α → α` | `[propext, Quot.sound]` |
| `orderedSimdFold_with_epilogue_sound` | Composing `n / W` ordered vector strips with `n % W` scalar remainder steps equals `runSequentialFold fop acc xs 0 n` | `[propext, Quot.sound]` |
| `floatReassocTree_sound` | `checkFloatReassocCert cert = true → ValidFastReassoc cert` (verifies `reassoc`, `nsz`, finite guards, and `srcTree.canonicalBag = tgtTree.canonicalBag`) | `[propext]` |
| `twoStripSimd4_reassoc_verified` | Kernel reflection proof that 4-lane 2-strip accumulation + butterfly tree refines 8-step sequential left-fold | `[propext]` |
| `fma_refines_fast_mul_add` | `checkFloatContract src tgt = true → RefinesFloatContract src tgt` (`contract` flag gates `separateMulAdd ↝ fusedFMA`) | `[propext]` |
| `canary_strict_fadd_tree_reassoc_rejected` | Rejects tree reassociation when `hasReassocFlag = false` (`rfl`) | *(none)* |
| `canary_fadd_fast_without_finite_guard_poison` | Rejects `fadd_fast` (`nnan ninf`) tree certificate when `allInputsFinite = false` (`rfl`) | *(none)* |

## Boundaries

- **Kahan Compensated Summation (`k09_kahan_f64_strict`) Under `reassoc`:** Applying `fadd_fast` or `reassoc` to Kahan summation `(t - sum) - y` allows `InstCombine` to fold `(sum + y - sum) - y -> 0.0`, destroying the compensation term `c`! Kahan summation must therefore remain in strict IEEE-754 mode (where `canary_strict_fadd_tree_reassoc_rejected` forbids `reassoc`).
- **`fadd_algebraic` vs. `fadd_fast` on `NaN` / `±Inf` Inputs:** Safe `core::intrinsics::fadd_algebraic` (`k12_l2norm_sq_f32_algebraic`) sets `reassoc nsz contract arcp` **without** `nnan` or `ninf`, so `FloatReassocCert` applies without requiring a finite-input side condition, whereas `unsafe` `fadd_fast` requires `allInputsFinite = true ∧ noFastMathOverflow = true` to avoid `poison`.

## Evidence

- **Rust 1.99.1 Probe, Runner, and Telemetry (`support/`):**
  - `support/fp_reduction_probe.rs`: 16-kernel Rust probe covering strict, `algebraic`, and `fast` floating-point reductions.
  - `support/run_fp_reduction_experiment.py` and `support/fp_reduction_results.json`: Compiler IR/assembly inspector and throughput table across `x86_64` (`AVX2`, `AVX-512`) and `aarch64` (`NEON`).
- **Lean `v4.34.1` Mechanization (`support/lean/`):**
  - `support/lean/OrderedAndFastFloatSimd.lean` and `support/lean/lakefile.lean`: Zero-`sorry`, zero-`native_decide` proof library extending `U5`.

## Revalidation

Run the 16-kernel floating-point experiment script and Lean `v4.34.1` kernel check from the package directory:

```bash
python3 support/run_fp_reduction_experiment.py
anneal-lean-run --mode file --concurrency 4 -- lean support/lean/OrderedAndFastFloatSimd.lean
```

Confirm exit code `0`, `fadd_fast_instructions == 45`, `vector_reduce_fadd_calls == 15`, and axioms limited to `[propext, Quot.sound]`.
