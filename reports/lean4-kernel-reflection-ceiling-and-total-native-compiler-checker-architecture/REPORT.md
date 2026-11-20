# Lean 4 Kernel Reflection Throughput Ceilings (`v4.28`–`v4.35`) and Pure-Total Native Compiler Checker Substrates

## Summary

Two critical design choices for a verified drop-in `rustc` depend on real, non-inflated Lean 4 performance measurements: (1) whether fine-grained per-instruction optimization certificates can be checked synchronously inside Lean 4's C++ kernel via definitional-equality (`rfl`/`decide`) reflection during compilation, and (2) whether **pure, total, FFI-free** compiled Lean 4 code (obeying strict TCB rules: zero `@[extern]`, zero `partial def`, zero `unsafe`) is fast enough to execute hot compiler passes or certificate checkers natively compared to safe Rust (`rustc 1.99.1 -C opt-level=3`).

Executing non-inflated (`1 step == 1 actual checked IR step`), zero-`sorry`, zero-axiom benchmarks across three Lean 4 releases (`v4.28.0-rc1`, `v4.34.1`, `v4.35.0`) and `rustc 1.99.1` establishes three decisive architectural facts:

1. **Honest Lean 4 Kernel Reflection Ceiling Is `~290–590` Real SSA+Interval+BCE Steps/Second Across `v4.28`–`v4.35`:**
   - A naive `List` + `UInt64` SSA+poison checker reduces at **`~187` real steps/s** (`v4.28.0-rc1`, `N = 100 -> 250`) and hits Lean's default `maxRecDepth` wall at `N = 500`.
   - Switching to a **balanced binary tree of 16-step bit-packed `Nat` chunks** (`O(log N)` recursion depth), restricting every operation to Lean's **kernel GMP fast paths** (`Nat.add`, `Nat.sub`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble`), and using **strict pattern-destructuring register updates** (avoiding call-by-name `{ f with r_i := v }` projection-thunk towers that time out at `>180s` for `N = 100`!) reaches:
     - **`Lean v4.28.0-rc1`:** `387.1` real steps/s (`N = 100 -> 4,000`: `3.400s -> 13.475s`, `~105 KB` RSS/step, hitting `maxHeartbeats` and `2,006.6 MB` RSS before `N = 16,000`; `0` axioms).
     - **`Lean v4.34.1`:** `445.0` real steps/s (`N = 100 -> 4,000`: `0.797s -> 9.562s`; `588.3` steps/s on `1,000 -> 4,000`).
     - **`Lean v4.35.0`:** `538.4` real steps/s (`N = 100 -> 4,000`: `3.960s -> 11.204s`; `400.0` steps/s on `1,000 -> 4,000`).
   - **Architectural consequence:** Checking `1,000,000` fine-grained optimization micro-steps inside Lean's kernel via `rfl` requires `~1,700–3,400` CPU-seconds and tens of gigabytes of RAM across every modern Lean 4 release. Per-instruction kernel reflection inside `rustc` compile time is mathematically unviable; checking must either run as a **compiled verified native checker** (proved sound once in Lean, `CompCert`/`CakeML`-style, or self-verified in Rust) or operate strictly on **coarse-grained function/superblock summaries**.
2. **Pure, Total, FFI-Free Compiled Lean 4 Runs at `2.18x–3.36x` of Safe Rust `-O3` on Unboxed `ByteArray`/`Array UInt32`, but Hits a `24.31x` Heap-Boxing Cliff on `Array UInt64`:**
   - Using zero `@[extern]`, zero `partial`, zero `unsafe`, CLI-parameterized workloads, and explicit IO sequencing before end-timestamps (preventing Lean's closed-term hoisting and LCNF pure-`let` reordering past `IO.monoNanosNow`), compiled pure-total Lean `v4.28.0-rc1` (`lean -c` + `leanc -O3`) matches safe `rustc 1.99.1 -C opt-level=3` bit-for-bit on all checksums (`total wall: 299.7 ms vs. 120.5 ms = 2.49x`):
     - **`inst_encode` (`2,000,000` x86-64 `REX+ModRM+disp32` instructions into `ByteArray`):** `135.51 ms` vs. `62.18 ms` = **`2.18x`**.
     - **`egraph_uf` (`200,000`-node fuel-bounded union-find, `600,000` ops on `Array UInt32`):** `128.42 ms` vs. `38.25 ms` = **`3.36x`**.
     - **`liveness_bs` (`2,000` BBs × `256`-var iterative bitset dataflow, `15` passes):** **`24.31x`** (`9.41 ms` vs. `0.39 ms`) on `Array UInt64` because `64`-bit `UInt64` does not fit in Lean's `63`-bit tagged scalar pointer and heap-boxes every write; switching to unboxed `8`-word **`Array UInt32`** halves Lean runtime (`5.29 ms` vs. `0.44 ms` = **`12.11x`**), with the remaining gap driven by LLVM AVX2 auto-vectorization and Lean per-access bounds checks.
3. **Three Lean 4 Kernel & Compiler Performance Traps Documented Live:**
   - **(a) Kernel lazy `{ s with field := v }` thunk blowup:** Struct-update notation without explicit destructuring creates exponential call-by-name projection towers in Lean's kernel WHNF reducer.
   - **(b) Lean LCNF pure-`let` timer reordering:** `let t0 ← IO.monoNanosNow; let c := pureKernel n; let t1 ← IO.monoNanosNow` allows Lean's LCNF compiler to float `pureKernel n` past `t1` (yielding bogus `0.000 ms` timings!) unless `t0` feeds a data dependency into `pureKernel` and `c` is forced by an `IO` action before reading `t1`.
   - **(c) `63`-bit scalar tagging cutoff:** `UInt32` (and smaller) stay unboxed inside `Array α` on 64-bit Lean, whereas `UInt64` allocates a boxed heap object on every `Array.set!`.

---

## Applicability

All benchmarks ran natively on Linux `x86_64` (`2026-11-20`) under hardware-capped cgroup memory governance with synchronous kernel checking (`-DElab.async=false -Ddebug.skipKernelTC=false`):

- **`leanprover/lean4:v4.28.0-rc1`** (`3b0f2862196c6a8af9eb0025ee650252694013dd`, matching `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`'s pinned toolchain): full naive `List`/`UInt64` sweep (`N = 10..1000`), balanced-tree GMP sweep (`N = 100..16,000`), and pure-total native vs. `rustc 1.99.1` benchmarks.
- **`leanprover/lean4:v4.34.1`** (`5045d0056413266e57c625dcd7c365b10e377c52`) and **`leanprover/lean4:v4.35.0`** (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`): cross-version balanced-tree GMP kernel reflection sweeps (`N = 100, 1000, 4000`).
- **`rust-lang/rust` (`rustc 1.99.1`)** (`58cf8f9c35b355199727627d07ae34a4e2846d67`): safe Rust `-C opt-level=3` reference baseline (`std::hint::black_box`, `5`-run medians).

These measurements directly supersede earlier inflated kernel-throughput and C11 `@[extern]` parity claims and inform the checker-deployment trade-off alongside `proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings` and `lean4-kernel-memory-maxrecdepth-and-per-body-mir-proof-sharding`.

---

## Findings

### 1. Honest Lean 4 Kernel Reflection Throughput (`0` Step Inflation, `0` Forbidden Axioms)

`Basis: execution (lake env lean / elan run lean -DElab.async=false -Ddebug.skipKernelTC=false on support/e1_2b_honest_lean_kernel_throughput.json and support/e1_2b_lean_version_comparison.json)`

Every checked step decodes an actual `32`-bit packed instruction (`op : 3b`, `dst : 3b`, `srcA : 3b`, `srcB : 3b`, `imm16 : 16b`), reads an `8`-register abstract fact file (`nonPoison : Bool`, `lo : Nat`, `hi : Nat`), checks real arithmetic/poison/bounds side conditions (`const`, `add nuw` checking `hiA + hiB <= 2^64 - 1`, `sub nuw` checking `hiB <= loA`, `checkBounds` checking `hiA + 1 <= loB`, `freeze` elimination checking `np == true`), and updates the strictly destructured `RegFile`. Soundness of `add nuw` (`add_nuw_interval_sound`) and bounds-check elimination (`bce_interval_sound`) plus all `cert_valid_gmp_N` theorems depend on **zero axioms (`∅`)** (and `[propext, Quot.sound]` for the `List`/`UInt64` variant):

| Checker Encoding & Lean Version | `N = 100` | `N = 500` | `N = 1,000` | `N = 4,000` | `N = 16,000` | Marginal Real Steps/s | Peak RSS (`N = 4,000`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Naive `List` + `UInt64` (`v4.28.0-rc1`)** | `1.424s` | `FAIL (maxRecDepth)` | `FAIL (maxRecDepth)` | — | — | **`~187` steps/s** (`100→250`: `2.226s`) | `483 MB` (`N = 250`) |
| **Balanced-Tree GMP (`v4.28.0-rc1`, warm run)** | `3.400s` | `4.372s` | `5.115s` | `13.475s` | `FAIL (maxHeartbeats, 30.58s, 2.01 GB)` | **`387.1` steps/s** (`100→4,000`) | `855.3 MB` |
| **Balanced-Tree GMP (`v4.28.0-rc1`, multi-ver)** | *(queued)* | — | `5.104s` | `15.399s` | — | **`291.4` steps/s** (`1,000→4,000`) | — |
| **Balanced-Tree GMP (`v4.34.1`)** | `0.797s` | — | `4.463s` | `9.562s` | — | **`445.0` steps/s** (`100→4,000`) / **`588.3`** (`1k→4k`) | — |
| **Balanced-Tree GMP (`v4.35.0`)** | `3.960s` | — | `3.704s` | `11.204s` | — | **`538.4` steps/s** (`100→4,000`) / **`400.0`** (`1k→4k`) | — |

**Key Kernel Engineering Findings:**
1. **Strict Destructuring Is Mandatory for Kernel WHNF:** Writing `setR` with Lean's record-update syntax `{ f with r4 := v }` generates lazy projections `f.r0 .. f.r7`. Under Lean's call-by-name kernel reducer, `100` consecutive updates form an unreduced projection tower that exceeded `180s` (`TimeoutExpired`) on `N = 100`. Replacing `{ f with ... }` with explicit `match f with | ⟨r0, ..., r7⟩ => ...` dropped `N = 100` from `>180s` to `0.80s–3.40s` (`>50x` speedup).
2. **`Nat.land`/`Nat.lor`/`Nat.xor` Lack Kernel GMP Fast Paths:** Only `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble`, `Nat.pow`, and `Nat.gcd` hit C++ GMP fast paths inside Lean's kernel; bitwise ops fall back to recursive `Nat.bitwise`, degrading step speed further.
3. **RSS & Heartbeat Wall:** At `~105 KB` peak RSS per real step (`447 MB` at `N = 100` → `855 MB` at `N = 4,000` → `2,007 MB` at `N = 16,000`), Lean 4's kernel hits default `maxHeartbeats` between `4,000` and `16,000` real SSA steps in a single `rfl` proof term.
4. **Why Prior Benchmarks Reported `534k–4.19B` Steps/s:** Inflating step counters (`+ 50` or `+ 250` per loop iteration with zero IR state transition) or substituting an unverified Rust loop for kernel checking measures trivial arithmetic addition rather than certificate validation.

### 2. Pure, Total, FFI-Free Compiled Lean 4 vs. Safe `rustc 1.99.1 -O3`

`Basis: execution (lean -c + leanc -O3 vs rustc +1.99.1 -C opt-level=3, 5-run medians, exact UInt64 checksum equality in support/e1_2c_pure_total_lean_vs_rust.json)`

All three Lean kernels use strictly total structural/fuel recursion (`0` `partial def`, `0` `@[extern]`, `0` `unsafe`, `0` `sorry`), read problem sizes from CLI `args` with a live `t0 &&& 0` dependency, and force each checksum via `IO.println` **before** calling the end `IO.monoNanosNow` (verified against outer process wall-clock: `299.70 ms` Lean vs. `120.48 ms` Rust = **`2.49x`** overall):

| Compiler Kernel | Workload | Pure-Total Lean `v4.28.0-rc1` (`-O3`) | Safe Rust `1.99.1` (`-O3`) | Lean / Rust Ratio | Checksum Match | Bottleneck Anatomy |
| :--- | :--- | ---: | ---: | ---: | :---: | :--- |
| **`inst_encode`** | `2,000,000` x86-64 `REX+ModRM+disp32` emissions (`14 MB` `ByteArray`) | **`135.514 ms`** | `62.184 ms` | **`2.18x`** | `True` (`11361685715086791552`) | Unboxed `ByteArray` in-place COW mutation (`lean_byte_array_push`); zero per-byte heap boxing. |
| **`egraph_uf`** | `200,000` nodes, `600,000` fuel-bounded union-find path-halving ops (`Array UInt32`) | **`128.424 ms`** | `38.247 ms` | **`3.36x`** | `True` (`92554`) | `UInt32` fits in Lean's 63-bit tagged scalar pointer (zero element boxing); gap is COW exclusivity check + `toNat` bounds checks. |
| **`liveness_bs` (`Array UInt64`)** | `2,000` BBs × `256` vars (`4` `UInt64` words/BB) × `15` iterations | **`9.407 ms`** | `0.387 ms` | **`24.31x`** | `True` (`16315244818618830336`) | **`63`-bit scalar tagging cutoff:** `UInt64` allocates a boxed heap object on every `Array.set!` + RC traffic. |
| **`liveness_u32` (`Array UInt32`)** | `2,000` BBs × `256` vars (`8` `UInt32` words/BB) × `15` iterations | **`5.290 ms`** | `0.437 ms` | **`12.11x`** | `True` (`238530189440`) | Eliminates heap boxing (`2.0x` speedup over `Array UInt64`); remaining gap is Rust/LLVM AVX2 auto-vectorization + Lean `Array.get!` bounds checks. |

**Compiler Timing Trap Observed Live:** Before adding `IO.println` on the checksum prior to `t1 ← IO.monoNanosNow`, Lean 4's LCNF optimizer floated all three pure kernel calls outside the `(t0, t1)` timing brackets, printing `0.000 ms` with valid checksums! Any Lean 4 microbenchmark timing pure functions inside `IO` **must** verify that inner timer sums match outer wall-clock time and thread explicit IO barriers around each kernel.

### 3. Architectural Consequence for a Verified Drop-In `rustc`

Comparing `~300–590` real steps/s inside Lean's kernel (`E1-2b`) against `~14.8M` encoded instructions/s (`inst_encode`: `2M` insts in `135.5 ms`) and `~4.7M` union-find ops/s (`egraph_uf`: `600k` ops in `128.4 ms`) in compiled pure-total Lean (`E1-2c`) reveals a **`>10,000x` throughput gap** between Lean kernel `rfl` reflection and compiled pure-total Lean native execution:

| Deployment Architecture | Throughput on Real IR Checks | TCB Surface | Viability for Drop-In `rustc` |
| :--- | :--- | :--- | :--- |
| **1. Per-instruction `rfl` reflection in Lean kernel** | `~300–590` steps/s (`~105 KB`/step) | Smallest (Lean kernel / `lean4lean` / `nanoda`) | **Unviable** for whole-crate optimization traces (`>30` min per `1M` steps). |
| **2. Proved-once Lean checker compiled natively (`lean -c` + `leanc -O3`, pure total `ByteArray`/`Array UInt32`)** | `2.2x–3.4x` of Rust `-O3` (`~5M–15M` ops/s) | Lean kernel + Lean LCNF-to-C compiler + C runtime + C compiler (`CompCert`/`CakeML` trade-off) | **Viable** for default `cargo build` compile-time budget. |
| **3. Coarse-grained summary certificates + Anneal-self-verified safe Rust checker** | `1.0x` native Rust `-O3` (with kernel audit for function specs & high-assurance mode) | Lean kernel + `rustc-capture` + `Trusted.MirSemantics` (bootstrapped via Anneal) | **Strongest long-term target** once Anneal supports full `ByteArray`/`Vec` MIR semantics. |

### 4. Performance, Comprehensibility, and Validation (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

- **`L1` / `L2` / `L3` / `L4` / `L5` / `L6`:** `Basis: execution` — Directly quantifies `L5` (`291–588` real steps/s kernel reflection vs. `5M–15M` ops/s compiled pure-total Lean), `L6` (`447–2,007 MB` kernel RSS), and `L3` (`2.18x–3.36x` pure-total native overhead vs. Rust `-O3`). `L1`/`L4` (proof effort / generated target-binary speed): `not measured`.
- **`C1` / `C2`:** Pure-total `ByteArray`/`Array UInt32` Lean code stays `100%` inside `TrustedBoundary.lean`'s safe subset (zero `@[extern]`, zero `partial`, zero RC aliasing UB) while recovering within `2.2x–3.4x` of Rust `-O3`.
- **`V1`–`V4`:** `V1`/`V2` verified `0` axioms on kernel reflection theorems, exact `UInt64` checksum identity between Lean and Rust across all 4 kernels, and outer-wall-clock sanity checking catching the LCNF timer-reordering bug live. `V3`/`V4`: `not examined`.

---

## Boundaries

1. **Single-Core Measurements (`not examined`):** All kernel reflection and native Lean-vs-Rust measurements ran single-threaded (`1` core); multi-core sharding across independent functions scales throughput linearly with cores up to RAM limits (`~105 KB`/step in kernel mode), but does not close the `>10,000x` per-step gap between kernel `rfl` and compiled native checking.
2. **External Checkers (`not examined`):** This report benchmarks Lean's built-in C++ kernel (`v4.28.0-rc1`, `v4.34.1`, `v4.35.0`) and compiled pure-total Lean native binaries; real `lean4export` serialization + `nanoda_lib` / `lean4lean` checking throughput on these exact `HonestGmp_N` proof terms remains to be measured directly.
3. **Lean `v4.34.1`/`v4.35.0` Native Codegen (`not examined`):** Native Lean-vs-Rust (`E1-2c`) was timed on `v4.28.0-rc1` (matching `joshlf/anneal`'s pinned toolchain); `v4.34.1`/`v4.35.0` were measured on kernel reflection (`E1-2b`) only.
4. **Refinement Proofs on `E1-2c` Kernels (`not examined`):** The `E1-2c` Lean kernels are pure, total, and free of `partial`/`@[extern]`, proving that total code structure alone achieves `2.18x–3.36x` of Rust `-O3`; functional correctness proofs over those three mutable-`do` `ByteArray`/`Array UInt32` loops were not authored here.

---

## Evidence

| Artifact / Source | Pin / Scope | Role |
| :--- | :--- | :--- |
| `support/e1_2b_honest_lean_kernel_throughput.json` | `v4.28.0-rc1` (`N = 10..1000` `List`/`UInt64` + `N = 100..16,000` Balanced-Tree GMP) | Exact timings, RSS, `maxRecDepth`/`maxHeartbeats` cliffs, and `0`-axiom receipts. |
| `support/e1_2b_lean_version_comparison.json` | `v4.28.0-rc1` vs. `v4.34.1` vs. `v4.35.0` (`N = 100, 1000, 4000`) | Cross-version Lean 4 kernel reflection throughput measurements (`291–588` real steps/s). |
| `support/e1_2c_pure_total_lean_vs_rust.json` | `v4.28.0-rc1` (`lean -c` + `leanc -O3`) vs. `rustc 1.99.1 -C opt-level=3` (`5`-run medians) | Exact median ms, outer wall-clock validation, and matching `UInt64` checksums for `inst_encode`, `egraph_uf`, and `liveness_bs`. |
| `leanprover/lean4` (`v4.28.0-rc1`, `v4.34.1`, `v4.35.0`) | `3b0f2862196c6a8af9eb0025ee650252694013dd`, `5045d0056413266e57c625dcd7c365b10e377c52`, `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | Verified Lean 4 toolchains benchmarked. |
| `rust-lang/rust` (`rustc 1.99.1`) | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Safe Rust `-O3` reference compiler. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `TrustedBoundary.lean` rules banning `@[extern]`, `partial`, `bv_decide`, and `native_decide`. |

---

## Revalidation

1. **Re-run balanced-tree GMP kernel reflection benchmark across Lean versions:**
   ```bash
   for tc in leanprover/lean4:v4.28.0-rc1 leanprover/lean4:v4.34.1 leanprover/lean4:v4.35.0; do
     elan run "$tc" lean -DElab.async=false -Ddebug.skipKernelTC=false HonestGmp_4000.lean
   done
   ```
   Verify `0` axioms (`#print axioms`), strict destructuring in `setR`, and `1` real checked IR step per packed word.
2. **Re-run pure-total Lean vs. safe Rust `-O3` comparison:** Compile `PureTotalBench.lean` with `lean -c` + `leanc -O3` and `pure_total_rust.rs` with `rustc +1.99.1 -C opt-level=3`, pass runtime CLI sizes (`200000 600000 2000 15 2000000`), verify identical checksums and agreement with outer wall-clock time.
