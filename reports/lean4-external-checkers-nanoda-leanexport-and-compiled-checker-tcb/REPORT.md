# Real External Lean 4 Proof-Term Checkers (`nanoda_bin 0.4.19`, `lean4export 3.1.0`, `lean4lean`): Reflective Throughput, Compiler-Pass TCB Diversity, and Export Coupling

## Summary

A central architectural question for a verified drop-in `rustc` backed by Lean
4 is whether independent Rust external proof checkers (such as
`ammkrn/nanoda_lib`) can break Lean's C++ kernel reflection ceiling (`291–588`
steps/sec) and allow per-instruction proof-term verification during normal
compilation, or whether external checkers instead belong purely in the
**offline compiler-pass TCB diversity layer** (re-checking pre-proved compiler
theorems once per compiler release).

An earlier exploratory report in this corpus substituted a 140-line synthetic
Rust `for`-loop for `nanoda_lib` and projected `4.19 billion steps/s`. This
report replaces that unverified surrogate with direct head-to-head
`[real measurement]` execution of the **actual `Lean 4.35.0` C++ kernel**
(`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc`),
**`lean4export 3.1.0`**
(`leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`),
**`nanoda_bin 0.4.19`**
(`ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`), and
**`lean4lean`** across two authentic compiler-verification workloads:

1. **Balanced-Tree GMP-Fast-Path Reflective Micro-Trace (`HonestGmp_100` to
   `HonestGmp_4000`, `0` axioms, `nat_extension = true`)** `[real measurement]`:
   - `Lean 4.35.0` C++ kernel: `1.137 s` (`475.6 MB`) at `N=100` → **`9.159 s`
     (`772.9 MB`) at `N=4,000`** (**`486.2` marginal steps/sec**).
   - `lean4export 3.1.0` (`.olean -> NDJSON`): `0.603–1.210 s` (`708.8–711.7 MB`,
     `422.5–446.3 KB` NDJSON, `7,974–8,389` lines).
   - **Real `nanoda_bin 0.4.19` (`ammkrn/nanoda_lib`):** `0.063 s` (`13.4 MB`)
     at `N=100` → **`3.262 s` (`268.5 MB`) at `N=4,000`** (**`1,219.0` marginal
     steps/sec**, `0` typechecker errors across `254` exported declarations).
   - **Takeaway:** Real `nanoda_lib` genuinely outperforms Lean's C++ kernel by
     **`2.51x`** in reflective reduction throughput and **`2.88x`** in peak RAM
     with no `maxHeartbeats` elaborator wall, **yet is `3,437,000x` (3.44
     million times) slower than the earlier fabricated `4.19B steps/s` loop.**
     At `1,219` steps/sec (`0.82 ms/step`), checking our measured `1,640,035`
     post-`-O3` LLVM instructions across `109` real Rust crates would still take
     `~22.4` single-core CPU minutes — proving per-instruction reflective
     reduction at compile time is unviable even in an external Rust kernel.
2. **Pre-Proved Compiler-Pass Theorem (`F1-1` `MirToMiniSsa_DeinitMove_Proof`,
   `2,446` LOC, `7` public / `35` total theorems, `3,032` transitive
   declarations)** `[real measurement]`:
   - `Lean 4.35.0` elaboration + kernel: `12.832 s` (`688.6 MB`, `10.26 MB`
     `.olean`).
   - `lean4export 3.1.0`: `1.581 s` (`729.4 MB`, `14.53 MB` / `282,950`-line
     NDJSON).
   - **Real `nanoda_bin 0.4.19` independent verification:** **`0.726 s` and
     `33.1 MB` peak RSS** (`0` typechecker errors across all `3,032`
     declarations — `17.7x` faster and `20.8x` leaner than Lean elaboration).
   - **Takeaway:** Independent multi-kernel TCB diversity for proved-once
     compiler-pass theorems (and verified certificate checkers compiled to
     native code) is essentially **free (`< 1 s`, `33 MB`)**.
3. **Two Real-World External-Checker TCB Coupling Hazards Observed Live**
   `[real measurement]`:
   - **Transitive `Init` Axiom Leakage under `lean4export`:** On `Lean 4.35.0`,
     exporting `F1-1`'s `7` public theorems pulls in a transitive `Init`
     declaration referencing `Classical.choice` (`nanoda_bin` panics at
     `src/tc.rs:230` with `declaration not found in infer_const,
     Classical.choice` when `permitted_axioms` excludes `Classical.choice`, even
     though `Lean 4.28.0-rc1` `#print axioms` reports strictly
     `[propext, Quot.sound]`). Pure zero-`Init` reflection (`HonestGmp_4000`)
     checks cleanly with `permitted_axioms: []`.
   - **Binary `.olean` Format Skew (`lean4lean` vs. NDJSON `lean4export`):**
     The installed `lean4lean` binary failed immediately (`rc=1`,
     `incompatible header`) against `Lean 4.35.0` `.olean` files, whereas the
     versioned JSON export format (`lean4export 3.1.0` → `nanoda_bin 0.4.19`)
     verified both workloads cleanly without binary-header coupling.

## Applicability

These measurements directly settle the proof-checking TCB architecture for a
verified drop-in `rustc` (and any Lean 4–backed verification pipeline such as
`joshlf/anneal`):

- **What external Rust checkers CAN do:** Provide ultra-fast (`0.726 s`,
  `33.1 MB`), memory-safe, independent secondary kernel verification of
  **pre-proved compiler passes, sound native certificate checkers, and
  coarse-grained user/crate specifications** via `lean4export` NDJSON, breaking
  single-kernel trust in Lean's C++ implementation.
- **What external Rust checkers CANNOT do:** Serve as a compile-time hot-loop
  engine for per-instruction translation-validation reflection (`1,219`
  steps/sec cannot absorb millions of MIR/LLVM instructions per crate).
  Compile-time translation validation must execute as a **proved-once compiled
  pure-total native checker** (`CompCert`/`CakeML` or self-verified Rust),
  whose *soundness theorem* is independently double-checked once at compiler
  build time by both Lean's C++ kernel and `nanoda_bin`.

## Findings

### 1. Reflective Micro-Trace Scaling: `Lean 4.35.0` vs. `lean4export 3.1.0` vs. `nanoda_bin 0.4.19`

Each `HonestGmp_N` module executes `N` genuine interval + poison + `add nuw` +
bounds-check abstract-interpretation steps over a balanced binary `ChunkTree`
(leaf size `16`, GMP-accelerated `Nat` operations, strict `RegFile`
destructuring, `0` axioms, `0` counter inflation). Every module was compiled
with `lean -DElab.async=false -Ddebug.skipKernelTC=false -o <mod>.olean`,
exported with `leanexport <mod> -- VrustcHonestGmpBench.cert_valid_gmp_<N>`,
and independently checked with `nanoda_bin` configured with
`permitted_axioms: []`, `nat_extension: true`, `string_extension: true`
(`[real measurement]`).

| Scale (`N` Steps) | `.olean` (KB) | NDJSON (KB / Lines) | `Lean 4.35.0` Wall (s) | `Lean 4.35.0` RSS (MB) | `leanexport` Wall (s) | `leanexport` RSS (MB) | `nanoda_bin` Wall (s) | `nanoda_bin` RSS (MB) | `nanoda_bin` Speedup vs. Lean |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `100` | `394.6` | `422.5` / `7,974` | `1.137` | `475.6` | `1.210` | `711.4` | **`0.063`** | **`13.4`** | `18.0x` (startup-dominated) |
| `500` | `469.1` | `432.4` / `8,142` | `2.388` | `510.3` | `0.767` | `708.8` | **`0.289`** | **`40.8`** | `8.3x` |
| `1,000` | `573.5` | `445.2` / `8,366` | `3.540` | `567.4` | `0.603` | `711.7` | **`0.542`** | **`77.7`** | `6.5x` |
| `4,000` | `586.5` | `446.3` / `8,389` | `9.159` | `772.9` | `0.997` | `711.3` | **`3.262`** | **`268.5`** | **`2.81x` e2e / `2.51x` marginal** |

#### Marginal Throughput (`N = 100 -> N = 4,000`, `3,900` Real Steps)

| Checker | `ΔWall` (s) | Marginal Throughput (`steps/sec`) | End-to-End @ `4,000` (`steps/sec`) | Marginal RSS / Step | vs. Refuted `4.19B/s` Surrogate |
| :--- | ---: | ---: | ---: | ---: | ---: |
| `Lean 4.35.0` C++ kernel | `8.022` | **`486.2`** | `436.7` | `~76 KB/step` | `8,618,000x` slower |
| `nanoda_bin 0.4.19` (Rust) | `3.199` | **`1,219.0`** | `1,226.1` | `~65 KB/step` | **`3,437,000x` slower** |

*(Note: `nanoda_bin` reports `Checked 254 declarations with no typechecker
errors` on all four scales with `permitted_axioms: []`. The constant `254`
declarations confirms that the balanced-tree proof term is checked inside one
kernel reduction of `cert_valid_gmp_N`, where `nanoda_bin`'s Rust WHNF/GMP
reducer runs at `~0.82 ms/step` and scales linearly in RSS at `~65 KB/step`.)*

### 2. Real Pre-Proved Compiler Theorem (`F1-1`, `2,446` LOC, `3,032` Transitive Decls)

We exported all `7` public theorems (`mir_to_minissa_forward_bisim`,
`mir_to_minissa_vc_transport`, `3` sharpness counterexamples, and `2`
non-vacuity canaries) of `F1_1_MirToMiniSsa_DeinitMove_Proof.lean`
(`field-granular-deinit-move-mir-to-minissa-bisimulation-and-vc-transport`)
through the exact same `Lean 4.35.0 -> leanexport 3.1.0 -> nanoda_bin 0.4.19`
pipeline (`[real measurement]`):

| Stage | Exit Code | Wall Time (s) | Peak RSS (MB) | Output Artifact / Result |
| :--- | ---: | ---: | ---: | :--- |
| `Lean 4.35.0` (`lean -DElab.async=false -Ddebug.skipKernelTC=false`) | `0` | `12.832` | `688.6` | `10,509,504 B` (`10.26 MB`) `.olean` |
| `leanexport 3.1.0` (`7` public theorems) | `0` | `1.581` | `729.4` | `14,883,724 B` (`14.53 MB`, `282,950` NDJSON lines) |
| `nanoda_bin 0.4.19` (`permitted_axioms: [propext, Quot.sound]`) | `101` | `0.640` | `19.7` | Panic at `src/tc.rs:230`: `declaration not found in infer_const, Classical.choice` |
| **`nanoda_bin 0.4.19` (`permitted_axioms: [propext, Quot.sound, Classical.choice]`)** | **`0`** | **`0.726`** | **`33.1`** | **`Checked 3032 declarations with no typechecker errors`** |
| `lean4lean` (direct `.olean` replay) | `1` | `3.119` | `80.0` | `failed to read file '*.olean', incompatible header` |

### 3. Architectural & TCB Lessons

1. **Decisive Split Between Compile-Time Checking and Release-Time TCB Audit:**
   - **Compile-time hot loop:** Even real Rust `nanoda_bin 0.4.19` executes
     reflective `rfl` micro-traces at only `1,219` steps/sec (`~65 KB` RSS/step),
     which cannot verify `1.64M` LLVM IR instructions (`~22.4` CPU-minutes)
     inside `rustc` compile time. Instead, our companion measurement
     (`lean4-kernel-reflection-ceiling-and-total-native-compiler-checker-architecture`)
     shows that a **proved-once compiled pure-total Lean checker** runs at
     `2.18x–3.36x` of `rustc -O3` on `ByteArray`/`Array UInt32`.
   - **Release-time TCB diversity:** Re-checking the `2,446`-line `F1-1`
     bisimulation theorem (`3,032` transitive declarations, `14.53 MB` NDJSON)
     in `nanoda_bin 0.4.19` takes **`0.726 s` and `33.1 MB` RAM** (`17.7x`
     faster and `20.8x` leaner than Lean elaboration). Running `lean4export` +
     `nanoda_bin` in CI on every compiler-pass theorem and every compiled
     checker soundness proof provides independent Rust-kernel verification at
     negligible cost.
2. **Audit `Init` Transitive Dependencies vs. Target-Theorem Axiom Sets:**
   When `unpermitted_axiom_hard_error: false` is set in `nanoda_bin`, skipping
   an unpermitted axiom (`Classical.choice`) that is later referenced by an
   exported transitive `Init` helper triggers an internal panic (`src/tc.rs:230`).
   External-checker CI gates should distinguish between (a) allowing Lean's
   three standard axioms `[propext, Quot.sound, Classical.choice]` in the
   exported environment while **forbidding** `sorryAx`, `Lean.ofReduceBool`,
   and `Lean.trustCompiler`, and (b) additionally verifying zero `Classical.choice`
   on target theorem declarations via explicit dependency-graph inspection.
3. **Prefer Versioned Text/NDJSON Export Over Binary `.olean` Coupling:**
   Binary `.olean` readers like `lean4lean` break across `.olean` header
   revisions (`incompatible header` even when placed inside a `v4.35.0`
   toolchain directory), whereas `lean4export` NDJSON format `3.1.0` cleanly
   decouples `nanoda_bin` from Lean's internal binary serialization layout.

## Boundaries

- **Single `nanoda_bin` Release (`0.4.19`) & Single Export Format (`3.1.0`):**
  Measurements reflect `nanoda_bin 0.4.19` with `nat_extension: true` and
  `string_extension: true` on `x86_64-unknown-linux-gnu` Linux. Future
  `nanoda_lib` optimizations (or alternative checkers such as `lean4lean`
  rebuilt cleanly against matching `v4.35.0` headers, or `coqchk`/`metamath`
  translators) may change constant factors, though reducing `~1,219` steps/sec
  to `10^6+` steps/sec without abandoning dependent type-checking reduction is
  not plausible.
- **`lean4lean` Not Benchmarked on Throughput:** Because the installed
  `lean4lean` binary failed on `.olean` header incompatibility (`rc=1`), this
  report makes **no throughput claim** for `lean4lean` and records only the
  observed format-coupling failure.
- **No Unbounded `N > 4,000` `nanoda_bin` Scaling Curve:** While `nanoda_bin`
  completed `N=4,000` in `3.262 s` (`268.5 MB`) with linear RSS growth
  (`~65 KB/step`), `Lean 4.35.0` itself hits `maxHeartbeats` before `N=16,000`,
  bounding what can be exported from Lean via `rfl` without splitting proofs
  into smaller shards.

## Evidence

All primary artifacts are included under `support/`:

- `support/bench_external_checkers.py`: Parameterized reproduction harness
  invoking `lean`, `lean4lean`, `leanexport`, and `nanoda_bin` with
  `/usr/bin/time -v` wall-clock and peak-RSS capture.
- `support/e2_2_real_external_checkers.json`: Exact measured wall time, user
  time, peak RSS, `.olean` bytes, NDJSON bytes/lines, declaration counts, and
  exit diagnostics across `HonestGmp_{100,500,1000,4000}` and `F1_1_Proof`.
- Related ground-truth reports in this corpus:
  - `lean4-kernel-reflection-ceiling-and-total-native-compiler-checker-architecture`
  - `field-granular-deinit-move-mir-to-minissa-bisimulation-and-vc-transport`
  - `rustc-lto-monomorphization-dedup-ir-volume-and-dwarf-coverage-census`

## Revalidation

Re-run whenever upgrading Lean 4, `lean4export`, `nanoda_lib`, or rebuilding
`lean4lean` for a new `.olean` header version:

```bash
python3 support/bench_external_checkers.py \
  --toolchain-dir /path/to/elan/toolchains/leanprover--lean4---v4.35.0 \
  --f1-proof /path/to/F1_1_MirToMiniSsa_DeinitMove_Proof.lean \
  --out-json /tmp/e2_2_reval.json
```

Verify that `nanoda_bin` reports `0` typechecker errors on both `HonestGmp_4000`
(`permitted_axioms: []`) and `F1_1_Proof` (`permitted_axioms: ["propext",
"Quot.sound", "Classical.choice"]`), and confirm whether a matching `lean4lean`
build resolves the `.olean` header mismatch.
