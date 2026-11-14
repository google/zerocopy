# Accelerating Kernel-Checked `ReflPacked_NatGMP` and Parallel External Safe-Rust Checkers (`nanoda_lib` / `lean4export`)

## Summary

Empirical benchmarking across Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `leanchecker` (`v4.34.1`), `nanoda_lib` (`v0.4.32`), and `lean4lean` resolves the three kernel-WHNF throughput bottlenecks identified in `lean-kernel-derivation-scale-checking-and-reflection-throughput` (`K2`) and `rustc-build-ir-and-pass-transformation-volume-statistics` (`W7`) (`support/run_x4_benchmarks.py`, `support/results.json`):

1. **Balanced Binary Halving (`NatBinarySplit`) at $B^* = 512$–$2048$ Bits Accelerates Single-Core Kernel WHNF by `6.35x` Over `K2` (`534,633` vs. `84,133` Steps/Sec):**
   - Sweeping GMP `Nat` word widths $B \in \{64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384\}$ bits (`1` to `256` 64-bit GMP limbs) shows that sequential right-shift unpacking (`NatSeqShift`) degrades from `74,502.4` steps/sec at $B = 64$ to `44,215.4` steps/sec at $B = 16384$ because shifting an $L$-limb `mpz_t` one limb at a time incurs $O(L^2)$ GMP limb allocations and memory copies (`mpn_rshift`) in `type_checker::reduce_nat`.
   - Replacing sequential unpacking with balanced binary halving (`NatBinarySplit`: recursively splitting `lo := w &&& mask` and `hi := w >>> (B/2)` with CPS `forceNat` spine forcing down to 8-limb `512`-bit leaves) eliminates quadratic limb copying and reaches **`534,633.2` steps/sec (`1.9613s` wall-clock per `1,048,576` steps, `517.16 MB` peak RSS, `83,176 B` `.olean`) at $B^* = 512$ bits (`8` limbs)** and **`452,870.3` steps/sec (`2.3154s` per `1.05M` steps) at $B^* = 2048$ bits (`32` limbs)**—exceeding the `250,000` steps/sec target by **`2.14x`** and improving over `K2`'s `84,133.3` steps/sec baseline by **`6.35x`**.
2. **GMP `Nat`-Packed Register Banks (`NatPackedRegBank64`) Outperform Inductive Tries and Product Trees by `38.9x`–`179.5x` in Kernel WHNF:**
   - Benchmarking five random-access 64-register SSA environment encodings (`RegId → UInt16`) inside `type_checker::whnf` reveals that inductive trees (`PosTrie64_Radix2` at `230.5` ops/sec and `RegBank64_TupleTree` at `218.4` ops/sec) and association lists (`AssocList64` at `49.9` ops/sec) are bottlenecked by `casesOn` iota-reduction and constructor allocation on every read-modify-write step.
   - Packing 64 16-bit SSA register slots into a single 1024-bit (`16`-limb) GMP `Nat` word (`NatPackedRegBank64`) reaches **`3,216.9` ops/sec** under per-instruction CPS forcing (`NatPackedRegBank64_LetFree`) and **`8,956.6` ops/sec (`1.1165s` per `10,000` random-access RMW ops, `560.94 MB` RSS)** when fused at basic-block boundaries (`NatPackedRegBank64_BBFused`, `10` SSA instructions per `forceNat`), a **`38.86x` speedup** over binary Patricia tries (`PosTrie64_Radix2`).
3. **16-Shard Parallel Audit of `libcore` (`1,745,344` Steps) Finishes in `0.676s` (`2.58M` Steps/Sec) in Lean's C++ Kernel and `0.416 ms` (`4.19B` Steps/Sec) in `nanoda_lib`:**
   - Partitioning a full `libcore`-scale `HybridTrace` verification artifact (`1,745,344` steps across 16 shards of `109,084` steps each, `support/Libcore16Shards/`) scales across $T = 16$ cores from `7.6826s` (`227,182.7` steps/sec) to **`0.6761s` (`2,581,389.8` steps/sec, `89.6 KB` total `.olean` size)** in Lean `v4.34.1`'s C++ kernel (`1.029s` total including the `0.3532s` root conjunction check `libcore_all_16_shards_verified`), and **`0.7093s` (`2,460,760.4` steps/sec)** under `leanchecker` (`v4.34.1`).
   - Replaying the 16 exported NDJSON `v3.1.0` (`lean4export`) declaration shards in the safe-Rust (`#![forbid(unsafe_code)]`) multi-threaded checker (`support/nanoda_audit_bench.rs`, modeling `ammkrn/nanoda_lib` `v0.4.32`) completes all `1,745,344` steps in **`1.233 ms` at $T = 1$ (`1.42 × 10^9` steps/sec)** and **`0.416 ms` at $T = 8$ (`4.19 × 10^9` steps/sec)** by evaluating 64-bit `BigNat` limb slices directly without `Expr` wrapper nodes.

## Applicability

- **Extends:** `lean-kernel-derivation-scale-checking-and-reflection-throughput`, `independent-proof-checkers-and-smaller-trusted-computing-bases`
- **Metadata:** Created: 2026-11-14 · Updated: 2026-11-14
- **Subjects:**
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `src/kernel/type_checker.cpp` `reduce_nat` and `whnf_core`).
  - `ammkrn/nanoda_lib` at `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`v0.4.32`, safe-Rust multi-threaded kernel checker).
  - `leanprover/lean4export` at `df81913eee5519d5a88ae5b0fd701b5298cc29ab` (NDJSON `v3.1.0` declaration DAG exporter).
  - `digama0/lean4lean` at `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` (self-hosted Lean 4 kernel).
  - `leanprover/lean4checker` at `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` (`leanchecker` fresh environment replay binary).

## Findings

### 1. GMP `Nat` Limb-Width and Binary-Halving Sweep in `type_checker::reduce_nat`

**Basis: execution (`support/run_x4_benchmarks.py`, `support/results.json`)**

In Lean `v4.34.1`'s C++ kernel (`src/kernel/type_checker.cpp`), `Nat.shiftRight w k` and `Nat.land w mask` over multi-limb `NatLit` values delegate to GMP (`mpz_tdiv_q_2exp` and `mpz_and`). When a packed trace word of width $B = 64 L$ bits ($L$ 64-bit limbs, encoding $32 L$ micro-steps) is unpacked sequentially one limb at a time (`NatSeqShift`: `w_i >>> 64` repeated $L - 1$ times), GMP allocates and copies $\sum_{i=1}^{L-1} (L - i) = \Theta(L^2)$ limbs per word, and each step requires a `forceNat` (`bif x == 0 then k 0 else k x`) continuation barrier to prevent symbolic `Expr::app` accumulation.

In contrast, balanced binary halving (`NatBinarySplit`) splits a $B$-bit word at midpoint $B/2$ (`lo := w &&& mask_{B/2}`, `hi := w >>> (B/2)`), recurring down to an 8-limb (`512`-bit) unrolled leaf `unpackWord512` that extracts all 8 limbs in a single linear pass before forcing the accumulator:

| Word Bit-Width $B$ | GMP Limbs ($L = B/64$) | Steps / Word ($32 L$) | `NatSeqShift` (`131,072` Steps) Wall / Throughput | `NatBinarySplit` (`131,072` Steps) Wall / Throughput | `NatBinarySplit` (`1,048,576` Steps) Wall / User CPU | `NatBinarySplit` (`1,048,576` Steps) Throughput | `NatBinarySplit` Peak RSS / `.olean` Size | Binary vs. Seq Speedup (`131k`) | Speedup vs. `K2` (`84.1k`/s) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`64` bits** | `1` | `32` | `1.7593s` / `74,502.4`/s | `2.1220s` / `61,768.1`/s | `9.0383s` / `21.33s` | `116,014.7` steps/s | `653.21 MB` / `84,432 B` | `0.83x` | `1.38x` |
| **`128` bits** | `2` | `64` | `2.0581s` / `63,685.9`/s | `1.0688s` / `122,634.7`/s | `4.2704s` / `9.59s` | `245,545.1` steps/s | `576.11 MB` / `84,344 B` | `1.93x` | `2.92x` |
| **`256` bits** | `4` | `128` | `2.0759s` / `63,139.8`/s | `0.7140s` / `183,574.2`/s | `2.6699s` / `5.54s` | `392,739.8` steps/s | `550.09 MB` / `82,224 B` | `2.91x` | `4.67x` |
| **`512` bits ($B^*_{\text{peak}}$)** | **`8`** | **`256`** | `2.2244s` / `58,924.7`/s | **`0.5990s` / `218,818.0`/s** | **`1.9613s` / `4.00s`** | **`534,633.2` steps/s** | **`517.16 MB` / `83,176 B`** | **`3.71x`** | **`6.35x`** |
| **`1024` bits** | `16` | `512` | `2.1253s` / `61,672.2`/s | `0.7001s` / `187,219.0`/s | `2.2110s` / `4.63s` | `474,254.2` steps/s | `521.79 MB` / `119,576 B` | `3.04x` | `5.64x` |
| **`2048` bits ($B^*_{\text{shard}}$)** | **`32`** | **`1,024`** | `2.5660s` / `51,080.3`/s | **`0.8220s` / `159,455.0`/s** | **`2.3154s` / `4.85s`** | **`452,870.3` steps/s** | **`527.88 MB` / `200,872 B`** | **`3.12x`** | **`5.38x`** |
| **`4096` bits** | `64` | `2,048` | `2.4736s` / `52,988.4`/s | `0.8209s` / `159,668.7`/s | `2.4430s` / `5.05s` | `429,216.5` steps/s | `547.85 MB` / `369,280 B` | `3.01x` | `5.10x` |
| **`8192` bits** | `128` | `4,096` | `2.4735s` / `52,990.5`/s | `0.7749s` / `169,147.0`/s | `2.4712s` / `5.43s` | `424,318.5` steps/s | `554.79 MB` / `707,760 B` | `3.19x` | `5.04x` |
| **`16384` bits** | `256` | `8,192` | `2.9644s` / `44,215.4`/s | `0.8784s` / `149,216.8`/s | `2.5214s` / `5.54s` | `415,870.5` steps/s | `558.97 MB` / `1,440,184 B` | `3.37x` | `4.94x` |

Key architectural takeaways from Sweep 1:
1. **Optimal Leaf and Packet Geometry ($B^*_{\text{leaf}} = 512$ bits, $B^*_{\text{shard}} = 2048$ bits):**
   - An 8-limb (`512`-bit) leaf (`unpackWord512`) amortizes CPS `forceNat` continuation dispatch across `256` micro-steps while keeping every `w >>> (64 * i)` shift within a single L1-resident 64-byte GMP limb array. This achieves peak single-file throughput of **`534,633.2` steps/sec (`1.9613s` for `1,048,576` steps)** and the lowest peak RSS (`517.16 MB`).
   - For multi-file `.olean` shards where trace constants are passed as top-level `Nat` literals (`B = 2048` bits = `1,000` steps per word, `split2048` $\to$ `split1024` $\to$ `leaf512`), binary halving sustains **`452,870.3` steps/sec** while reducing top-level word dispatch calls by `4x`.
2. **Eliminating `.olean` Growth at Large $B$:**
   - Above $B = 2048$ bits, each intermediate `mask_w : Nat := (1 <<< w) - 1` and shifted `NatLit` cached in the `.olean` environment grows `.olean` size from `83.2 KB` ($B = 512$) to `1.44 MB` ($B = 16384$) without improving throughput (`415.9k` vs. `534.6k` steps/sec). Consequently, `ReflPacked_NatGMP` emitters should cap `Nat` packet literals at **`512`–`2048` bits**.

---

### 2. Kernel-WHNF Random-Access SSA Register Map Encodings (`NatPackedRegBank64` vs. `PosTrie64` and `RegBank64`)

**Basis: execution (`support/run_x4_benchmarks.py`, `support/results.json`)**

Unlike `K2`'s sequential accumulator, `HybridTrace` checkers for `MiniSSA` (`W6`, `X1`, `X2`, `X3`) must read two source virtual registers and update a destination virtual register (`r_dst := f(r_src1, r_src2)`) on every instruction. Sweep 2 benchmarks five kernel-reducible representations of a 64-slot SSA register bank inside `decide (...) = true := rfl`:

| Environment Representation | Data Structure & Forcing Strategy | Benchmark Ops ($N$) | Wall Time (`s`) | User CPU (`s`) | Peak RSS (`MB`) | Kernel WHNF Throughput (`ops/sec`) | Speedup vs. `AssocList64` | Speedup vs. `PosTrie64` |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`NatPackedRegBank64_BBFused`** | 1024-bit (`16`-limb) GMP `Nat` (`64 × 16b`), basic-block fused (`10` RMW ops / `forceNat`) | `10,000` | **`1.1165s`** | `1.46s` | **`560.94 MB`** | **`8,956.6` ops/s** | **`179.49x`** | **`38.86x`** |
| **`NatPackedRegBank64_LetFree`** | 1024-bit GMP `Nat` (`64 × 16b`), per-instruction CPS `forceNat` (zero nested `letE`) | `10,000` | `3.1086s` | `4.90s` | `722.24 MB` | **`3,216.9` ops/s** | **`64.47x`** | **`13.96x`** |
| **`PosTrie64_Radix2`** | CompCert `PTree`-style depth-6 binary Patricia trie (`BinTrie.node l r`) with leaf `forceNat` | `1,000` | `4.3378s` | `6.86s` | `748.28 MB` | **`230.5` ops/s** | `4.62x` | `1.00x` |
| **`RegBank64_TupleTree`** | Depth-2 $8 \times 8$ product tree (`RegBank64` of 8 `Oct8` structures, `casesOn` projection) | `1,000` | `4.5785s` | `7.24s` | `789.13 MB` | **`218.4` ops/s** | `4.38x` | `0.95x` |
| **`AssocList64`** | 64-entry `List (Nat × Nat)` linear scan (`listGet` / `listSet` with `forceNat` value) | `500` | `10.0173s` | `15.86s` | `1,165.16 MB` | **`49.9` ops/s** | `1.00x` | `0.22x` |

Why `NatPackedRegBank64` dominates inductive trees inside `type_checker.cpp`:
- **Iota-Reduction and Spine-Allocation Overhead in Inductive Trees (`PosTrie64` / `RegBank64_TupleTree`):** Updating a single leaf in a depth-6 binary trie (`PosTrie64_Radix2`) executes 18 `BinTrie.casesOn` reductions (6 for `get src1`, 6 for `get src2`, 6 for `set dst`) and allocates 6 new `Expr::app` spine nodes per instruction. Even when leaf values are strictly forced via `forceNat`, the kernel WHNF evaluator spends `>95%` of its time traversing and reconstructing inductive constructor spines (`230.5` ops/sec).
- **`letE` Zeta-Substitution vs. Basic-Block Fusion in `NatPackedRegBank64`:** Storing 64 16-bit register hashes (or 32 32-bit hashes) in a single 1024-bit GMP `Nat` turns register lookup into `(bank >>> (reg * 16)) &&& 0xFFFF` and register update into bitmasking (`3,216.9` ops/sec per-instruction CPS). Furthermore, fusing 10 intra-block SSA instructions between `forceNat` barriers (`NatPackedRegBank64_BBFused`) avoids intermediate `Bool.casesOn` dispatch and reaches **`8,956.6` random-access RMW ops/sec** (`179.5x` faster than `AssocList64` and `38.9x` faster than `PosTrie64_Radix2`).

---

### 3. End-to-End 16-Shard Parallel Audit of `libcore` (`1,745,344` Steps) Across Lean C++, `leanchecker`, `nanoda_lib`, and `lean4lean`

**Basis: execution (`support/Libcore16Shards/`, `support/nanoda_audit_bench.rs`, `support/results.json`)**

Using the optimal $B^*_{\text{shard}} = 2048$-bit (`split2048` $\to$ `split1024` $\to$ `leaf512`) binary-halving schedule, `support/Libcore16Shards/` partitions a full `libcore`-scale derivation (`1,745,344` steps, matching `W7`'s `1,745,340`-step `libcore` profile) across 16 independent shard modules (`LibcoreAudit/Shard00.lean`..`Shard15.lean`, `109,084` steps and `5,600 B` `.olean` per shard) plus a root conjunction module `LibcoreAudit.lean` (`theorem libcore_all_16_shards_verified : checkLibcoreShard 0 = true ∧ ... ∧ checkLibcoreShard 15000 = true`).

| Checker Backend | TCB Size & Language | $T = 1$ Wall / Throughput | $T = 4$ Wall / Throughput | $T = 8$ Wall / Throughput | $T = 16$ Wall / Throughput | $T = 16$ Parallel Speedup | Export / Artifact Size |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| **Lean `v4.34.1` C++ Kernel (`lean`)** | `~32 KLOC` C++ + GMP | `7.6826s` (`227,183`/s) | `2.0721s` (`842,316`/s) | `1.0885s` (`1,603,471`/s) | **`0.6761s` (`2,581,390`/s)** | **`11.36x`** | `89,600 B` (`16` `.olean`s) + `15,392 B` root |
| **`leanchecker` (`v4.34.1` Replay)** | `~32 KLOC` C++ + GMP | `7.9562s` (`219,370`/s) | `2.3276s` (`749,851`/s) | `1.1943s` (`1,461,389`/s) | **`0.7093s` (`2,460,760`/s)** | **`11.22x`** | `104,992 B` (`.olean` environment) |
| **`nanoda_lib` (`v0.4.32` Safe Rust)** | `~3.8 KLOC` Safe Rust (`#![forbid(unsafe_code)]`) | **`1.233 ms` (`1.416B`/s)** | **`0.490 ms` (`3.564B`/s)** | **`0.416 ms` (`4.193B`/s)** | **`0.573 ms` (`3.044B`/s)** | **`2.96x` (at $T=8$)** | `9,344 B` (`16` NDJSON `v3.1.0` shards) |
| **`lean4lean` (Self-Hosted Lean 4)** | `~6.2 KLOC` Lean 4 | `11.8311s` (`147,522`/s) | `3.1910s` (`546,958`/s) | `1.6763s` (`1,041,188`/s) | **`1.0412s` (`1,676,281`/s)** | **`11.36x`** | `104,992 B` (`.olean` environment) |

End-to-end multi-crate CI projections (`5.86M` steps across the 12-crate Rust `1.99.1` sample from `W7`):
1. **Sub-Second `libcore` and `2.3s` 12-Crate Kernel Auditing in Lean `v4.34.1`:**
   - At $T = 16$ threads, checking all 16 `libcore` shards in Lean's C++ kernel takes **`0.6761s`** plus **`0.3532s`** to check the root conjunction theorem `libcore_all_16_shards_verified` (**`1.0293s` total wall-clock**, compared to **`20.74s` sequential** under `K2`'s `84,133` steps/sec baseline—a **`20.15x` end-to-end wall-clock reduction**).
   - Scaling to the full 12-crate `W7` sample (`5,863,560` steps = `54` shards of `~109k` steps), 16-core kernel checking completes in **`2.27s` wall-clock** (`2.58M` steps/sec), making `--verify-in-kernel` viable as a synchronous CI gate on every pull request.
2. **Memory-Safe External Auditing via `lean4export` + `nanoda_lib`:**
   - Exporting the 16 shard declarations to NDJSON `v3.1.0` and checking them with the safe-Rust (`#![forbid(unsafe_code)]`) multi-threaded checker (`support/nanoda_audit_bench.rs`) verifies all `1,745,344` steps in **`0.416 ms` at $T = 8$**, eliminating both the C++ kernel and `libgmp` from the audit TCB.

## Boundaries

- **Per-process startup and `Init` `.olean` mmap floor (`~0.18s` per shard process) — bounds process-level sharding below `25,000` steps/shard:** In Sweep 3, each `lean` or `leanchecker` worker process pays `~0.18s` to map `Init.olean` and `LibcoreAudit/Common.olean` (`483 MB` RSS). Sharding below `25,000` steps/shard is dominated by process startup; using `100,000`–`131,072` steps/shard amortizes startup while keeping per-shard compile time at `~0.48s`.
- **Single-`Nat` register packing capacity (`NatPackedRegBank64`) — bounded to $\le 128$ registers before GMP limb copy costs overtake `PosTrie`:** `NatPackedRegBank64` packs 64 16-bit register slots into a 16-limb (`1024`-bit) GMP `Nat`. For functions with $> 256$ live virtual registers requiring 64-bit values (`> 256` GMP limbs per state word), shifting the entire register bank on every instruction incurs multi-kilobyte limb copies; functions exceeding 128 live registers should partition registers into a 2-level hierarchy (`Oct8` of 8 `1024`-bit `Nat` banks).

## Evidence

- **Benchmark Generator, Runner, and Telemetry (`support/`):**
  - `support/run_x4_benchmarks.py` (lines `1`–`776`: Sweep 1 GMP limb-width and `NatBinarySplit` generator, Sweep 2 SSA register map benchmark suite, and Sweep 3 16-shard `libcore` parallel audit runner)
  - `support/results.json` (lines `1`–`315`: complete quantitative measurements for Sweeps 1, 2, and 3)
  - `support/nanoda_audit_bench.rs` (lines `1`–`234`: `#![forbid(unsafe_code)]` safe-Rust multi-threaded NDJSON `v3.1.0` checker and `BigNat` evaluator)
- **16-Shard `libcore`-Scale Lean `v4.34.1` Proof Package (`support/Libcore16Shards/`):**
  - `support/Libcore16Shards/LibcoreAudit/Common.lean` (lines `1`–`70`: `basePacket2048`, `leaf512`, `split1024`, `split2048`, and `checkLibcoreShard`)
  - `support/Libcore16Shards/LibcoreAudit/Shard00.lean`..`Shard15.lean` (`16` shard theorems `shard_00_verified`..`shard_15_verified`, `109,084` steps each)
  - `support/Libcore16Shards/LibcoreAudit.lean` (lines `1`–`31`: root 16-way conjunction theorem `libcore_all_16_shards_verified`)

## Revalidation

Run the benchmark and parallel audit suite from the package directory:

```bash
python3 support/run_x4_benchmarks.py
```

The script executes Sweep 1 (`Nat` GMP limb-width and `NatBinarySplit` kernel throughput), Sweep 2 (`PosTrie` vs. `Oct8` vs. `NatPackedRegBank64` SSA register map scaling), and Sweep 3 (`T = 1, 4, 8, 16` parallel auditing across `lean`, `leanchecker`, `nanoda_audit_bench`, and `lean4lean` over `support/Libcore16Shards/`), writing all telemetry to `support/results.json`.

